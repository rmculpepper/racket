#lang racket/base
(require racket/syntax
         racket/pretty racket/string
         syntax/parse/private/residual-ct ;; keep abs. path
         "minimatch.rkt"
         "rep-patterns.rkt"
         "kws.rkt")
(provide (struct-out pk1)
         (rename-out [optimize-matrix0 optimize-matrix]))

;; controls debugging output for optimization successes and failures
(define DEBUG-OPT-SUCCEED #f)
(define DEBUG-OPT-FAIL #f)

(define-logger stxpattern)

;; ----

;; A Matrix is a (listof PK) where each PK has same number of columns
;; A PK is one of
;;  - (pk1 (listof pattern) expr) -- a simple row in a parsing matrix
;;  - (pk/same pattern Matrix)    -- a submatrix with a common first column factored out
;;  - (pk/pair Matrix)            -- a submatrix with pair patterns in the first column unfolded
;;  - (pk/and Matrix)             -- a submatrix with and patterns in the first column unfolded
;;  - (pk/disj (Listof (cons Pattern Matrix)))  -- a submatrix with distinct first patterns
(struct pk1 (patterns k) #:prefab)
(struct pk/same (pattern inner) #:prefab)
(struct pk/pair (inner) #:prefab)
(struct pk/and (inner) #:prefab)
(struct pk/disj (inner) #:prefab)

(define (pk1-car pk) (car (pk1-patterns pk)))
(define (pk1-cdr pk) (pk1 (cdr (pk1-patterns pk)) (pk1-k pk)))

;; Can factor pattern P given clauses like
;;   [ P P1 ... | e1]     [  | [P1 ... | e1] ]
;;   [ P  :     |  :]  => [P | [ :     |  :] ]
;;   [ P PN ... | eN]     [  | [PN ... | eN] ]
;; if P cannot cut and P succeeds at most once (otherwise may reorder backtracking)

;; Can unfold pair patterns as follows:
;;   [ (P11 . P12) P1 ... | e1 ]                [ P11 P12 P1 ... | e1 ]
;;   [      :       :     |  : ] => check pair, [      :         |  : ]
;;   [ (PN1 . PN2) PN ... | eN ]                [ PN1 PN2 PN ... | eN ]

;; Can unfold ~and patterns similarly; ~and patterns can hide
;; factoring opportunities.

;; ----

;; FIXME: New (unimplemented) optimization ideas

;; (1) When collecting pair patterns, can reorder rows with pair vs never-pair
;; first columns:
;;   [ (P11 . P12) P1 ... | e1 ]      [ (P11 . P12) P1 ... | e1 ]
;;   [     P21     P2 ... | e2 ]  =>  [ (P31 . P32) P3 ... | e3 ]
;;   [ (P31 . P32) P3 ... | e3 ]      [     P21     P2 ... | e2 ]
;; provided P21 does not cut and cannot match a pair term.
;; Likewise for literals and never-symbol patterns.

;; (2) If a row has a non-rejecting pattern (ie, always matches) in its first
;; column, then the rows above it do not need to produce failure information
;; *for their first columns*. For example, in the following matrix
;;   [ P11 P1 ... | e1 ]
;;   [ P21 P2 ... | e2 ]
;;   [ P31 P3 ... | e3 ]
;; Suppose that P21 always matches (eg _) and assume P{1,3}1 are cut-free. Then
;; P{1,3}1 do not need to produce failure info (set es = #f, etc). Here's why.
;; If control reaches row 2, then since P21 cannot fail, if it fails the
;; progress must be greater than P11 or P31. FIXME: Must also check neither P11
;; nor P31 use ~post (or call stxclass that uses ~post, etc)!


;; ----

(define (optimize-matrix0 rows)

  (let ()
    (define ps (for/list ([row (in-list rows)]) (car (pk1-patterns row))))
    (define propss (map pattern-props ps))
    (define main-ps (map pattern-main-pattern ps))
    (define main-propss (map pattern-props main-ps))
    (log-stxpattern-debug
     "patterns (~a) ~s / ~s:\n~a\n"
     (length rows)
     (decode-pattern-props (apply bitwise-ior propss))
     (decode-pattern-props (apply bitwise-ior main-propss))
     (string-join
      (for/list ([p (in-list ps)]
                 [main-p (in-list main-ps)]
                 [props (in-list propss)]
                 [main-props (in-list main-propss)])
        (format ";~a ~s ~s\n~a"
                (cond [(eq? main-p p) ""]
                      [else (format " [~s ~s] /"
                                    (pattern-size main-p)
                                    (decode-pattern-props main-props))])
                (pattern-size p)
                (decode-pattern-props props)
                (pretty-format (pattern->sexpr p) #:mode 'write)))
      "\n")))

  (define now (current-inexact-milliseconds))
  (when (and (> (length rows) 1))
    (log-syntax-parse-debug "OPT matrix (~s rows)\n~a" (length rows)
                            (pretty-format (matrix->sexpr rows) #:mode 'print)))
  (define result (optimize-matrix rows))
  (define then (current-inexact-milliseconds))
  (when (and (> (length rows) 1))
    (cond [(= (length result) (length rows))
           (log-syntax-parse-debug "OPT FAILED (~s ms)" (floor (- then now)))]
          [else
           (log-syntax-parse-debug "OPT ==> (~s ms)\n~a" (floor (- then now))
                                   (pretty-format (matrix->sexpr result) #:mode 'print))]))
  result)

;; optimize-matrix : (listof pk1) -> Matrix
(define (optimize-matrix rows)
  (cond [(null? rows) null]
        [(null? (cdr rows)) rows] ;; no opportunities for 1 row
        [(null? (pk1-patterns (car rows))) rows]
        [else
         ;; first unfold and-patterns
         (let-values ([(col1 col2)
                       (for/lists (col1 col2) ([row (in-list rows)])
                         (unfold-and (car (pk1-patterns row)) null))])
           (cond [(ormap pair? col2)
                  (list
                   (pk/and
                    (optimize-matrix*
                     (for/list ([row (in-list rows)]
                                [col1 (in-list col1)]
                                [col2 (in-list col2)])
                       (pk1 (list* col1
                                   (make-and-pattern col2)
                                   (cdr (pk1-patterns row)))
                            (pk1-k row))))))]
                 [else (optimize-matrix* rows)]))]))

;; optimize-matrix* : (listof pk1) -> Matrix
;; The matrix is nonempty, and first column has no unfoldable pat:and.
;; Split into submatrixes (sequences of rows) starting with similar patterns,
;; handle according to similarity, then recursively optimize submatrixes.
(define (optimize-matrix* rows)
  (define row1 (car rows))
  (define pat1 (car (pk1-patterns row1)))
  (define k1 (pk1-k row1))
  ;; Now accumulate rows starting with patterns like pat1
  (define-values (like? combine) (pattern->partitioner pat1))
  (let loop ([rows (cdr rows)] [rrows (list row1)])
    (cond [(null? rows)
           (cons (combine (reverse rrows)) null)]
          [else
           (define row1 (car rows))
           (define pat1 (car (pk1-patterns row1)))
           (cond [(like? pat1)
                  (loop (cdr rows) (cons row1 rrows))]
                 [else
                  (cons (combine (reverse rrows))
                        (optimize-matrix* rows))])])))

;; pattern->partitioner : pattern -> (values (pattern -> boolean) ((listof pk1) -> PK))
(define (pattern->partitioner pat1)
  (match pat1
    [(pat:pair head tail)
     (values (lambda (p) (pat:pair? p))
             (lambda (rows)
               (log-syntax-parse-debug "-- got ~s pair rows like ~e" (length rows) (pattern->sexpr pat1))
               (cond [(> (length rows) 1)
                      (pk/pair (optimize-matrix
                                (for/list ([row (in-list rows)])
                                  (let* ([patterns (pk1-patterns row)]
                                         [pat1 (car patterns)])
                                    (pk1 (list* (pat:pair-head pat1)
                                                (pat:pair-tail pat1)
                                                (cdr patterns))
                                         (pk1-k row))))))]
                     [else (car rows)])))]
    #;
    [(? pat:literal?)
     (define h (make-hash))
     (values (lambda (p)
               ;; FIXME: do real non-overlapping check / coalesce adjacent same lits
               (and (pat:literal? p)
                    (let ([key (syntax-e (pat:literal-id p))])
                      (and (not (hash-has-key? h (syntax-e (pat:literal-id p))))
                           (begin0 #t (hash-set! h key #t))))))
             (lambda (rows)
               (cond [(> (length rows) 1)
                      (log-syntax-parse-debug "-- got ~s disjoint literals: ~e" (length rows) (hash-keys h))
                      (pk/disj
                       (for/list ([row (in-list rows)])
                         (cons (pk1-car row) (list (pk1-cdr row)))))]
                     [else (car rows)])))]
    [(? pattern-factorable?)
     (values (lambda (pat2) (pattern-equal? pat1 pat2))
             (lambda (rows)
               (log-syntax-parse-debug "-- got ~s factorable like ~e" (length rows) (pattern->sexpr pat1))
               (cond [(> (length rows) 1)
                      (pk/same pat1
                               (optimize-matrix
                                (for/list ([row (in-list rows)])
                                  (pk1 (cdr (pk1-patterns row)) (pk1-k row)))))]
                     [else (car rows)])))]
    [_
     (values (lambda (pat2) #f)
             (lambda (rows)
               ;; (length rows) = 1
               (car rows)))]))

;; unfold-and : pattern (listof pattern) -> (values pattern (listof pattern))
(define (unfold-and p onto)
  (match p
    [(pat:and subpatterns)
     ;; pat:and is worth unfolding if first subpattern is not pat:action
     ;; if first subpattern is also pat:and, keep unfolding
     (let* ([first-sub (car subpatterns)]
            [rest-subs (cdr subpatterns)])
       (cond [(not (pat:action? first-sub))
              (unfold-and first-sub (*append rest-subs onto))]
             [else (values p onto)]))]
    [_ (values p onto)]))

(define (pattern-factorable? p)
  ;; Can factor out p if p can succeed at most once, does not cut
  ;;  - if p can succeed multiple times, then factoring changes success order
  ;;  - if p can cut, then factoring changes which choice points are discarded (too few)
  (match p
    [(pat:any) #t]
    [(pat:svar _n) #t]
    [(pat:var/p _ _ _ _ _ (scopts _ commit? _ _))
     ;; commit? implies delimit-cut
     commit?]
    [(? pat:integrated?) #t]
    [(pat:literal _lit _ip _lp) #t]
    [(pat:datum _datum) #t]
    [(pat:action _act _pat) #f]
    [(pat:head head tail)
     (and (pattern-factorable? head)
          (pattern-factorable? tail))]
    [(pat:dots heads tail)
     ;; Conservative approximation for common case: one head pattern
     ;; In general, check if heads don't overlap, don't overlap with tail.
     (and (= (length heads) 1)
          (let ([head (car heads)])
            (and (pattern-factorable? head)))
          (equal? tail (pat:datum '())))]
    [(pat:and patterns)
     (andmap pattern-factorable? patterns)]
    [(pat:or patterns) #f]
    [(pat:not pattern) #f] ;; FIXME: ?
    [(pat:pair head tail)
     (and (pattern-factorable? head)
          (pattern-factorable? tail))]
    [(pat:vector pattern)
     (pattern-factorable? pattern)]
    [(pat:box pattern)
     (pattern-factorable? pattern)]
    [(pat:pstruct key pattern)
     (pattern-factorable? pattern)]
    [(pat:describe pattern _desc _trans _role)
     (pattern-factorable? pattern)]
    [(pat:delimit pattern)
     (pattern-factorable? pattern)]
    [(pat:commit pattern) #t]
    [(? pat:reflect?) #f]
    [(pat:ord pattern _ _)
     (pattern-factorable? pattern)]
    [(pat:post pattern)
     (pattern-factorable? pattern)]
    ;; ----
    [(hpat:var/p _ _ _ _ _ (scopts _ commit? _ _))
     commit?]
    [(hpat:seq inner)
     (pattern-factorable? inner)]
    [(hpat:commit inner) #t]
    ;; ----
    [(ehpat head repc)
     (and (equal? repc #f)
          (pattern-factorable? head))]
    ;; ----
    [else #f]))

(define (subpatterns-equal? as bs)
  (and (= (length as) (length bs))
       (for/and ([a (in-list as)]
                 [b (in-list bs)])
         (pattern-equal? a b))))

(define (pattern-equal? a b)
  (define result
    (cond [(and (pat:any? a) (pat:any? b)) #t]
          [(and (pat:svar? a) (pat:svar? b))
           (bound-identifier=? (pat:svar-name a) (pat:svar-name b))]
          [(and (pat:var/p? a) (pat:var/p? b))
           (and (free-id/f-equal? (pat:var/p-parser a) (pat:var/p-parser b))
                (bound-id/f-equal? (pat:var/p-name a) (pat:var/p-name b))
                (equal-iattrs? (pat:var/p-nested-attrs a) (pat:var/p-nested-attrs b))
                (equal-argu? (pat:var/p-argu a) (pat:var/p-argu b))
                (expr-equal? (pat:var/p-role a) (pat:var/p-role b)))]
          [(and (pat:integrated? a) (pat:integrated? b))
           (and (bound-id/f-equal? (pat:integrated-name a) (pat:integrated-name b))
                (free-identifier=? (pat:integrated-predicate a)
                                   (pat:integrated-predicate b))
                (expr-equal? (pat:integrated-role a) (pat:integrated-role b)))]
          [(and (pat:literal? a) (pat:literal? b))
           ;; literals are hard to compare, so compare gensyms attached to
           ;; literal ids (see rep.rkt) instead
           (let ([ka (syntax-property (pat:literal-id a) 'literal)]
                 [kb (syntax-property (pat:literal-id b) 'literal)])
             (and ka kb (eq? ka kb)))]
          [(and (pat:datum? a) (pat:datum? b))
           (equal? (pat:datum-datum a)
                   (pat:datum-datum b))]
          [(and (pat:head? a) (pat:head? b))
           (and (pattern-equal? (pat:head-head a) (pat:head-head b))
                (pattern-equal? (pat:head-tail a) (pat:head-tail b)))]
          [(and (pat:dots? a) (pat:dots? b))
           (and (subpatterns-equal? (pat:dots-heads a) (pat:dots-heads b))
                (pattern-equal? (pat:dots-tail a) (pat:dots-tail b)))]
          [(and (pat:and? a) (pat:and? b))
           (subpatterns-equal? (pat:and-patterns a) (pat:and-patterns b))]
          [(and (pat:or? a) (pat:or? b))
           (subpatterns-equal? (pat:or-patterns a) (pat:or-patterns b))]
          [(and (pat:not? a) (pat:not? b))
           (pattern-equal? (pat:not-pattern a) (pat:not-pattern b))]
          [(and (pat:pair? a) (pat:pair? b))
           (and (pattern-equal? (pat:pair-head a) (pat:pair-head b))
                (pattern-equal? (pat:pair-tail a) (pat:pair-tail b)))]
          [(and (pat:vector? a) (pat:vector? b))
           (pattern-equal? (pat:vector-pattern a) (pat:vector-pattern b))]
          [(and (pat:box? a) (pat:box? b))
           (pattern-equal? (pat:box-pattern a) (pat:box-pattern b))]
          [(and (pat:pstruct? a) (pat:pstruct? b))
           (and (equal? (pat:pstruct-key a)
                        (pat:pstruct-key b))
                (pattern-equal? (pat:pstruct-pattern a)
                                (pat:pstruct-pattern b)))]
          [(and (pat:describe? a) (pat:describe? b)) #f] ;; can't compare desc exprs
          [(and (pat:delimit? a) (pat:delimit? b))
           (pattern-equal? (pat:delimit-pattern a) (pat:delimit-pattern b))]
          [(and (pat:commit? a) (pat:commit? b))
           (pattern-equal? (pat:commit-pattern a) (pat:commit-pattern b))]
          [(and (pat:reflect? a) (pat:reflect? b)) #f] ;; FIXME: ?
          [(and (pat:ord? a) (pat:ord? b))
           (and (pattern-equal? (pat:ord-pattern a) (pat:ord-pattern b))
                (equal? (pat:ord-group a) (pat:ord-group b))
                (equal? (pat:ord-index a) (pat:ord-index b)))]
          [(and (pat:post? a) (pat:post? b))
           (pattern-equal? (pat:post-pattern a) (pat:post-pattern b))]
          ;; ---
          [(and (hpat:var/p? a) (hpat:var/p? b))
           (and (free-id/f-equal? (hpat:var/p-parser a) (hpat:var/p-parser b))
                (bound-id/f-equal? (hpat:var/p-name a) (hpat:var/p-name b))
                (equal-iattrs? (hpat:var/p-nested-attrs a) (hpat:var/p-nested-attrs b))
                (equal-argu? (hpat:var/p-argu a) (hpat:var/p-argu b))
                (expr-equal? (hpat:var/p-role a) (hpat:var/p-role b)))]
          [(and (hpat:seq? a) (hpat:seq? b))
           (pattern-equal? (hpat:seq-inner a) (hpat:seq-inner b))]
          ;; ---
          [(and (ehpat? a) (ehpat? b))
           (and (equal? (ehpat-repc a) #f)
                (equal? (ehpat-repc b) #f)
                (pattern-equal? (ehpat-head a) (ehpat-head b)))]
          ;; FIXME: more?
          [else #f]))
  (when (and (log-level? syntax-parse-logger 'debug)
             (eq? result #f)
             (equal? (syntax->datum #`#,a) (syntax->datum #`#,b)))
    (log-syntax-parse-debug "** pattern-equal? failed on ~e" a))
  result)

(define (equal-iattrs? as bs)
  (and (= (length as) (length bs))
       ;; assumes attrs in same order
       (for/and ([aa (in-list as)]
                 [ba (in-list bs)])
         (and (bound-identifier=? (attr-name aa) (attr-name ba))
              (equal? (attr-depth aa) (attr-depth ba))
              (equal? (attr-syntax? aa) (attr-syntax? ba))))))

(define (expr-equal? a b)
  ;; Expression equality is undecidable in general. Especially difficult for unexpanded
  ;; code, but it would be very difficult to set up correct env for local-expand because of
  ;; attr binding rules. So, do *very* conservative approx: simple variables and literals.
  ;; FIXME: any other common cases?
  (cond [(not (and (syntax? a) (syntax? b)))
         (equal? a b)]
        [(and (identifier? a) (identifier? b))
         ;; note: "vars" might be identifier macros (unsafe to consider equal),
         ;; so check var has no compile-time binding
         (and (free-identifier=? a b)
              (let/ec k (syntax-local-value a (lambda () (k #t))) #f))]
        [(syntax-case (list a b) (quote)
           [((quote ad) (quote bd))
            (cons (syntax->datum #'ad) (syntax->datum #'bd))]
           [_ #f])
         => (lambda (ad+bd)
              (equal? (car ad+bd) (cdr ad+bd)))]
        [else
         ;; approx: equal? only if both simple data (bool, string, etc), no inner stx
         (let ([ad (syntax-e a)]
               [bd (syntax-e b)])
           (and (equal? ad bd)
                (free-identifier=? (datum->syntax a '#%datum) #'#%datum)
                (free-identifier=? (datum->syntax b '#%datum) #'#%datum)))]))

(define (equal-argu? a b)
  (define (unwrap-arguments x)
    (match x
      [(arguments pargs kws kwargs)
       (values pargs kws kwargs)]))
  (define (list-equal? as bs inner-equal?)
    (and (= (length as) (length bs))
         (andmap inner-equal? as bs)))
  (let-values ([(apargs akws akwargs) (unwrap-arguments a)]
               [(bpargs bkws bkwargs) (unwrap-arguments b)])
    (and (list-equal? apargs bpargs expr-equal?)
         (equal? akws bkws)
         (list-equal? akwargs bkwargs expr-equal?))))

(define (free-id/f-equal? a b)
  (or (and (eq? a #f)
           (eq? b #f))
      (and (identifier? a)
           (identifier? b)
           (free-identifier=? a b))))

(define (bound-id/f-equal? a b)
  (or (and (eq? a #f)
           (eq? b #f))
      (and (identifier? a)
           (identifier? b)
           (bound-identifier=? a b))))

(define (make-and-pattern subs)
  (cond [(null? subs) (pat:any)] ;; shouldn't happen
        [(null? (cdr subs)) (car subs)]
        [else (pat:and subs)]))

(define (*append a b) (if (null? b) a (append a b)))

(define (stx-e x) (if (syntax? x) (syntax-e x) x))

;; ----

(define (matrix->sexpr rows)
  (cond [(null? rows) ;; shouldn't happen
         '(FAIL)]
        [(null? (cdr rows))
         (pk->sexpr (car rows))]
        [else
         (cons 'TRY (map pk->sexpr rows))]))
(define (pk->sexpr pk)
  (match pk
    [(pk1 pats k)
     (cons 'MATCH (map pattern->sexpr pats))]
    [(pk/same pat inner)
     (list 'SAME (pattern->sexpr pat) (matrix->sexpr inner))]
    [(pk/pair inner)
     (list 'PAIR (matrix->sexpr inner))]
    [(pk/and inner)
     (list 'AND (matrix->sexpr inner))]
    [(pk/disj rows)
     (cons 'DISJ (map (lambda (row) `(IF ,(pattern->sexpr (car row)) ,(matrix->sexpr (cdr row)))) rows))]
    ))
(define (pattern->sexpr p)
  (match p
    [(pat:any) '_]
    [(pat:integrated name pred desc _)
     (format-symbol "~a:~a" (or name '_) desc)]
    [(pat:svar name)
     (syntax-e name)]
    [(pat:var/p name parser _ _ _ _)
     (cond [(and parser (regexp-match #rx"^parse-(.*)$" (symbol->string (syntax-e parser))))
            => (lambda (m)
                 (format-symbol "~a:~a" (or name '_) (cadr m)))]
           [else
            (if name (syntax-e name) '_)])]
    [(? pat:literal?) `(syntax ,(syntax->datum (pat:literal-id p)))]
    [(pat:datum datum)
     (cond [(or (symbol? datum) (pair? datum))
            `(quote ,datum)]
           [else datum])]
    [(pat:action action (pat:any)) '<Action>]
    [(pat:action action inner) (list '~and '<Action> (pattern->sexpr inner))]
    [(pat:and patterns) (cons '~and (map pattern->sexpr patterns))]
    [(pat:or _ patterns _) (cons '~or (map pattern->sexpr patterns))]
    [(pat:ord pattern _ _) (list '~ord (pattern->sexpr pattern))]
    [(pat:pair head tail)
     (cons (pattern->sexpr head) (pattern->sexpr tail))]
    [(pat:head head tail)
     (cons (pattern->sexpr head) (pattern->sexpr tail))]
    [(pat:dots (list eh) tail)
     (list* (pattern->sexpr eh) '... (pattern->sexpr tail))]
    [(ehpat _as hpat '#f _cn)
     (pattern->sexpr hpat)]
    [_ 'PATTERN]))

;; ============================================================

#;
;; pattern-has-expr? : *Pattern -> Boolean
;; Returns #t if p has expr that needs attr bindings (or do env!)
(define (pattern-has-expr? p)
  (define (loop p)
    (match p
      ;; -- S patterns
      [(pat:any) #f]
      [(pat:svar name) #f]
      [(pat:var/p _ _ argu _ _ _) (not (equal? argu no-arguments))]
      [(pat:reflect _ _ _ _ _) #t]
      [(pat:datum _) #f]
      [(pat:literal _ _ _) #f] ;; FIXME
      [(pat:action a sp) (or (loop a) (loop sp))]
      [(pat:head headp tailp) (or (loop headp) (loop tailp))]
      [(pat:pair headp tailp) (or (loop headp) (loop tailp))]
      [(pat:vector sp) (loop sp)]
      [(pat:box sp) (loop sp)]
      [(pat:pstruct key sp) (loop sp)]
      [(pat:describe sp _ _ _) (or (loop sp) #t)]
      [(pat:and ps) (ormap loop ps)]
      [(pat:or _ ps _) (ormap loop ps)]
      [(pat:not sp) (loop sp)]
      [(pat:dots headps tailp) (or (ormap loop headps) (loop tailp))]
      [(pat:delimit sp) (loop sp)]
      [(pat:commit sp) (loop sp)]
      [(pat:ord sp _ _) (loop sp)]
      [(pat:post sp) (loop sp)]
      [(pat:integrated _ _ _ _) #f]
      ;; -- A patterns
      [(action:cut) #f]
      [(action:fail _ _) #t]
      [(action:bind attr expr) #t]
      [(action:and ps) (ormap loop ps)]
      [(action:parse sp rhs) (or (loop sp) #t)]
      [(action:do stmts) #t]
      [(action:undo stmts) #t]
      [(action:ord sp _ _) (loop sp)]
      [(action:post sp) (loop sp)]
      ;; -- H patterns
      [(hpat:var/p _ _ argu _ _ _) (not (equal? argu no-arguments))]
      [(hpat:reflect _ _ _ _ _) #t]
      [(hpat:seq lp) (loop lp)]
      [(hpat:action a hp) (or (loop a) (loop hp))]
      [(hpat:describe hp _ _ _) (or (loop hp) #t)]
      [(hpat:and hp sp) (or (loop hp) (loop sp))]
      [(hpat:or _ ps _) (ormap loop ps)]
      [(hpat:delimit hp) (loop hp)]
      [(hpat:commit hp) (loop hp)]
      [(hpat:ord hp _ _) (loop hp)]
      [(hpat:post hp) (loop hp)]
      [(hpat:peek hp) (loop hp)]
      [(hpat:peek-not hp) (loop hp)]
      ;; EH patterns
      [(ehpat _ hp '#f _) (loop hp)]
      [(ehpat _ hp _ _) #t]))
  (loop p))

;; pattern-reduce : (*Pattern (-> X) -> X) (X ... -> X) -> *Pattern -> X
(define (pattern-reduce handle reduce p)
  (define base (reduce))
  (define (reducemap f xs) (apply reduce (map f xs)))
  (define (loop p)
    (handle p (lambda ([x base]) (reduce x (loop* p)))))
  (define (loop* p)
    (match p
      ;; -- S patterns
      [(pat:any) base]
      [(pat:svar name) base]
      [(pat:var/p _ _ _ _ _ _) base]
      [(pat:reflect _ _ _ _ _) base]
      [(pat:datum _) base]
      [(pat:literal _ _ _) base]
      [(pat:action a sp) (reduce (loop a) (loop sp))]
      [(pat:head headp tailp) (reduce (loop headp) (loop tailp))]
      [(pat:pair headp tailp) (reduce (loop headp) (loop tailp))]
      [(pat:vector sp) (loop sp)]
      [(pat:box sp) (loop sp)]
      [(pat:pstruct key sp) (loop sp)]
      [(pat:describe sp _ _ _) (loop sp)]
      [(pat:and ps) (reducemap loop ps)]
      [(pat:or _ ps _) (reducemap loop ps)]
      [(pat:not sp) (loop sp)]
      [(pat:dots headps tailp) (reduce (reducemap loop headps) (loop tailp))]
      [(pat:delimit sp) (loop sp)]
      [(pat:commit sp) (loop sp)]
      [(pat:ord sp _ _) (loop sp)]
      [(pat:post sp) (loop sp)]
      [(pat:integrated _ _ _ _) base]
      ;; -- A patterns
      [(action:cut) base]
      [(action:fail _ _) base]
      [(action:bind attr expr) base]
      [(action:and ps) (reducemap loop ps)]
      [(action:parse sp rhs) (loop sp)]
      [(action:do stmts) base]
      [(action:undo stmts) base]
      [(action:ord sp _ _) (loop sp)]
      [(action:post sp) (loop sp)]
      ;; -- H patterns
      [(hpat:var/p _ _ _ _ _ _) base]
      [(hpat:reflect _ _ _ _ _) base]
      [(hpat:seq lp) (loop lp)]
      [(hpat:action a hp) (reduce (loop a) (loop hp))]
      [(hpat:describe hp _ _ _) (loop hp)]
      [(hpat:and hp sp) (reduce (loop hp) (loop sp))]
      [(hpat:or _ ps _) (reducemap loop ps)]
      [(hpat:delimit hp) (loop hp)]
      [(hpat:commit hp) (loop hp)]
      [(hpat:ord hp _ _) (loop hp)]
      [(hpat:post hp) (loop hp)]
      [(hpat:peek hp) (loop hp)]
      [(hpat:peek-not hp) (loop hp)]
      ;; EH patterns
      [(ehpat _ hp _ _) (loop hp)]))
  (loop p))

;; ----------------------------------------

(define (bit n) (arithmetic-shift 1 n))
(define EXPOSED:CUT   (bit 0))
(define EXPOSED:MULTI (bit 1))
(define HAS:CUT       (bit 4))
(define HAS:UNDO      (bit 5))  ;; includes literals!
(define HAS:EXPR      (bit 6))
(define HAS:OR        (bit 7))
(define HAS:HEAD      (bit 8))
(define HAS:LITERAL   (bit 9))
;; FIXME: lit in non-default phase
(define HAS:INLSC     (bit 11))
(define HAS:STXCLASS  (bit 12))  ;; but not integrated stxclass
(define HAS:FAIL      (bit 13))  ;; has ~fail check
(define HAS:DOTS      (bit 16))
(define HAS:DOTS:ALTS (bit 17))
(define HAS:DOTS:HEAD (bit 18))
(define HAS:DOTS:REPC (bit 19))

(define (decode-pattern-props n)
  (define (flag sym bit)
    (if (zero? (bitwise-and n bit)) #f sym))
  (filter symbol?
          (list (flag 'E-cut EXPOSED:CUT)
                (flag 'E-multi EXPOSED:MULTI)
                (flag 'cut HAS:CUT)
                (flag 'undo HAS:UNDO)
                (flag 'expr HAS:EXPR)
                (flag 'or HAS:OR)
                (flag 'head HAS:HEAD)
                (flag 'lit HAS:LITERAL)
                (flag 'stxclass HAS:STXCLASS)
                (flag 'inlsc HAS:INLSC)
                (flag 'fail HAS:FAIL)
                (flag 'dots HAS:DOTS)
                (flag 'dots-alts HAS:DOTS:ALTS)
                (flag 'dots-head HAS:DOTS:HEAD)
                (flag 'dots-repc HAS:DOTS:REPC))))

;; pattern-props : *Pattern -> Nat
;; Returns #t if p has expr that needs attr bindings (or do env!)
(define (pattern-props p)
  (define ior bitwise-ior)
  (define (clr n . ks) (bitwise-and n (apply bitwise-xor -1 ks)))
  (define (bitwhen n cnd?) (if cnd? n 0))
  (define (handle p recur)
    (match p
      ;; -- S patterns
      [(pat:any) (recur)]
      [(pat:svar name) (recur)]
      [(pat:var/p _ _ argu _ _ opts)
       (ior (bitwhen (+ HAS:CUT EXPOSED:CUT) (not (scopts-delimit-cut? opts)))
            (bitwhen EXPOSED:MULTI (not (scopts-commit? opts)))
            (bitwhen HAS:EXPR (not (equal? argu no-arguments)))
            HAS:UNDO HAS:STXCLASS)]
      [(pat:reflect _ _ _ _ _)
       (ior EXPOSED:MULTI HAS:EXPR HAS:UNDO HAS:STXCLASS (recur))]
      [(pat:datum _) (recur)]
      [(pat:literal _ _ _)
       (ior (bitwhen HAS:EXPR #f) ;; FIXME
            HAS:LITERAL HAS:UNDO
            (recur))]
      [(pat:action a sp) (recur)]
      [(pat:head headp tailp) (ior HAS:HEAD (recur))]
      [(pat:pair headp tailp) (recur)]
      [(pat:vector sp) (recur)]
      [(pat:box sp) (recur)]
      [(pat:pstruct key sp) (recur)]
      [(pat:describe sp desc _ _)
       (ior (bitwhen HAS:EXPR #t) ;; FIXME
            (recur))]
      [(pat:and ps) (recur)]
      [(pat:or _ ps _) (ior EXPOSED:MULTI HAS:OR (recur))]
      [(pat:not sp) (clr (recur) EXPOSED:MULTI)]
      [(pat:dots headps tailp)
       (ior HAS:DOTS
            EXPOSED:MULTI ;; FIXME
            (bitwhen HAS:DOTS:ALTS (> (length headps) 1))
            (recur))]
      [(pat:delimit sp) (clr (recur) EXPOSED:CUT)]
      [(pat:commit sp) (clr (recur) EXPOSED:CUT EXPOSED:MULTI)]
      [(pat:ord sp _ _) (recur)]
      [(pat:post sp) (recur)]
      [(pat:integrated _ _ _ _) (ior HAS:INLSC (recur))]
      ;; -- A patterns
      [(action:cut) (ior HAS:CUT EXPOSED:CUT)]
      [(action:fail cnd msg)
       (ior HAS:EXPR HAS:FAIL)]
      [(action:bind attr expr) (ior HAS:EXPR)]
      [(action:and ps) (recur)]
      [(action:parse sp rhs) (ior HAS:EXPR)]
      [(action:do stmts) (ior HAS:EXPR)]
      [(action:undo stmts) (ior HAS:EXPR HAS:UNDO)]
      [(action:ord sp _ _) (recur)]
      [(action:post sp) (recur)]
      ;; -- H patterns
      [(hpat:var/p _ _ argu _ _ opts)
       (ior (bitwhen (+ HAS:CUT EXPOSED:CUT) (not (scopts-delimit-cut? opts)))
            (bitwhen EXPOSED:MULTI (not (scopts-commit? opts)))
            (bitwhen HAS:EXPR (not (equal? argu no-arguments)))
            HAS:UNDO HAS:STXCLASS)]
      [(hpat:reflect _ _ _ _ _)
       (ior EXPOSED:MULTI HAS:EXPR HAS:UNDO HAS:STXCLASS)]
      [(hpat:seq lp) (recur)]
      [(hpat:action a hp) (recur)]
      [(hpat:describe hp desc _ _)
       (ior (bitwhen HAS:EXPR #t) ;; FIXME
            (recur))]
      [(hpat:and hp sp) (recur)]
      [(hpat:or _ ps _) (ior EXPOSED:MULTI HAS:OR (recur))]
      [(hpat:delimit hp) (clr (recur) EXPOSED:CUT)]
      [(hpat:commit hp) (clr (recur) EXPOSED:CUT EXPOSED:MULTI)]
      [(hpat:ord hp _ _) (recur)]
      [(hpat:post hp) (recur)]
      [(hpat:peek hp) (recur)]
      [(hpat:peek-not hp) (recur)]
      ;; EH patterns
      [(ehpat _ hp repc _)
       (ior (bitwhen (+ HAS:EXPR HAS:DOTS:REPC) repc)  ;; FIXME
            (bitwhen HAS:DOTS:HEAD (head-pattern? hp))
            (recur))]
      ))
  (pattern-reduce handle bitwise-ior p))

(define (pattern-size p)
  (pattern-reduce (lambda (p recur) (+ 1 (recur))) + p))

;; pattern-main-pattern : *Pattern -> *Pattern
(define (pattern-main-pattern p0)
  (let loop ([p p0])
    (match p
      [(pat:and (cons p _)) (loop p)]
      [(pat:ord p _ _) (loop p)]
      [(hpat:and hp _) (loop hp)]
      [(hpat:ord p _ _) (loop p)]
      [_ p])))
