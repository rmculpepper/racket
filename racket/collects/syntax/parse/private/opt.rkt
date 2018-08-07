#lang racket/base
(require (for-template racket/base)
         racket/syntax
         racket/pretty
         racket/string
         syntax/parse/private/residual-ct ;; keep abs. path
         "minimatch.rkt"
         "rep-patterns.rkt"
         "kws.rkt")
(provide (struct-out pk1)
         (rename-out [optimize-matrix0 optimize-matrix]))

(define-logger stxpattern)

;; ----

;; A Matrix is a (listof PK) where each PK has same number of columns
;; A PK is one of
;;  - (pk1 (listof pattern) expr) -- a simple row in a parsing matrix
;;  - (pk/same pattern Matrix)    -- a submatrix with a common first column factored out
;;  - (pk/pair Matrix)            -- a submatrix with pair patterns in the first column unfolded
;;  - (pk/and Matrix)             -- a submatrix with and patterns in the first column unfolded
(struct pk1 (patterns k) #:prefab)
(struct pk/same (pattern inner) #:prefab)
(struct pk/pair (inner) #:prefab)
(struct pk/and (inner) #:prefab)

(define (pk-columns pk)
  (match pk
    [(pk1 patterns k) (length patterns)]
    [(pk/same p inner) (add1 (pk-columns inner))]
    [(pk/pair inner) (sub1 (pk-columns inner))]
    [(pk/and inner) (sub1 (pk-columns inner))]))

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

  (when #t
    (define ps (for/list ([row (in-list rows)]) (car (pk1-patterns row))))
    (define propss (map pattern-props ps))
    (define main-ps (map pattern-main-pattern ps))
    (define main-propss (map pattern-props main-ps))
    (log-stxpattern-debug
     "patterns:\n;! ~s\n~a\n"
     (list (length rows) (decode-pattern-props (apply bitwise-ior propss)))
     (string-join
      (for/list ([p (in-list ps)]
                 [main-p (in-list main-ps)]
                 [props (in-list propss)]
                 [main-props (in-list main-propss)])
        (define (info p props)
          `((size ,(pattern-size p)) (attrs ,(length (pattern-attrs p))) ,(decode-pattern-props props)))
        (format ";@ ~s\n~a"
                (if (eq? main-p p) (list (info p props)) (list (info main-p main-props) (info p props)))
                (if #f
                    (pretty-format (pattern->sexpr p) #:mode 'write)
                    (format "~s" (pattern->sexpr p)))))
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

  (optimize-pattern result))

;; ----------------------------------------

(require (submod "residual.rkt" simple))

(provide optimize-pattern)

(define (optimize-pattern p)

  (define (simple-literal-pattern? p)
    (define (ok-phase-expr? e)
      (syntax-case e (quote syntax-local-phase-level)
        [(syntax-local-phase-level) #t]
        [_ #f]))
    (match p
      [(pat:literal lit-id input-phase literal-phase)
       (and (ok-phase-expr? input-phase) (ok-phase-expr? literal-phase))]
      [else #f]))

  (define simple-size-table (make-hasheq))
  (define (size p) (hash-ref simple-size-table p 0))
  (let ()
    (define (record-size! p size)
      (hash-set! simple-size-table p size))
    (define (for-pattern p recur)
      (recur)
      (match p
        [(pat:any) (record-size! p 1)]
        [(pat:svar _) (record-size! p 1)]
        [(pat:datum '()) (record-size! p 1)]
        [(pat:integrated _ parser desc _)
         (when (member desc '("identifier" "expression" "keyword"))
           (record-size! p 1))]
        [(pat:pair hp tp)
         (when (and (> (size hp) 0) (> (size tp) 0))
           (record-size! p (+ (size hp) (size tp))))]
        [(pat:dots (list (ehpat _ (hpat:single hp) '#f _)) (pat:datum '()))
         (when (> (size hp) 0)
           (record-size! p (+ (size hp) 2)))]
        [(pat:and (list (pat:svar name) (? simple-literal-pattern?)))
         (record-size! p 1)]
        [(? simple-literal-pattern?)
         (record-size! p 1)]
        [_ (void)]))
    (pattern-reduce-left p for-pattern void))

  ;; ordering of pattern-attrs might not be consistent w/ simple-parse
  (define (get-attrs p)
    (match p
      [(pat:pair hp tp) (append (get-attrs hp) (get-attrs tp))]
      [(pat:dots (list (ehpat attrs (hpat:single hp) '#f _)) (pat:datum '()))
       (repc-adjust-attrs (get-attrs hp) #f)]
      [_ (pattern-attrs p)]))

  (define (convert-pattern p)
    (define bind-counter 0) ;; mutated!
    (define literals null) ;; mutated!
    (define (next-bind-index)
      (begin0 bind-counter (set! bind-counter (add1 bind-counter))))
    (define (loop p)
      (match p
        [(pat:any) (sp:triv #f 'any)]
        [(pat:svar name) (sp:triv (next-bind-index) 'any)]
        [(pat:datum '()) '()]
        [(pat:integrated name _ desc _)
         (sp:triv (and (identifier? name) (next-bind-index))
                  (match desc
                    ['"identifier" 'id]
                    ['"keyword"    'kw]
                    ['"expression" 'expr]))]
        [(pat:pair hp tp) (cons (loop hp) (loop tp))]
        [(pat:dots (list (ehpat attrs (hpat:single hp) '#f _)) (pat:datum '()))
         (sp:dots (length attrs) (loop hp))]
        [(pat:and (list (pat:svar name) (pat:literal lit-id _ _)))
         (define index (length literals))
         (set! literals (cons lit-id literals))
         (sp:lit (next-bind-index) index)]
        [(pat:literal lit-id _ _)
         (define index (length literals))
         (set! literals (cons lit-id literals))
         (sp:lit #f index)]))
    (define simple (loop p))
    (values simple (reverse literals)))

  (define (for-pattern p recur)
    (cond [(> (size p) 2)
           (when #t
             (log-syntax-parse-debug "simple: ~v" (pattern->sexpr p)))
           (define-values (simple literals) (convert-pattern p))
           (pat:simple (get-attrs p) simple literals)]
          [else (recur)]))

  (pattern-transform-preorder p for-pattern))

;; ----------------------------------------

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

;; pattern-factorable? : *Pattern -> Boolean
(define (pattern-factorable? p) (not (pattern-unfactorable? p)))

;; pattern-unfactorable? : *Pattern -> Boolean
(define (pattern-unfactorable? p)
  ;; Cannot factor out p if
  ;; - if p can succeed multiple times (factoring changes success order)
  ;; - if p can cut (factoring changes which choice points are discarded (too few))
  ;; Note: presence of sub-expressions handled by pattern-equal?.
  (define (for-pattern p recur)
    (match p
      [(pat:var/p _ _ _ _ _ (scopts _ commit? _ _)) (not commit?)]
      [(pat:action _act _pat) #t]
      [(pat:dots heads tail)
       ;; Conservative approximation for common case: one head pattern
       ;; In general, check if heads don't overlap, don't overlap with tail.
       (or (> (length heads) 1)
           (not (equal? tail (pat:datum '())))
           (recur))]
      [(pat:or _ patterns _) #t]
      [(pat:not pattern) #t]
      [(pat:commit pattern) #f]
      [(? pat:reflect?) #t]
      [(hpat:var/p _ _ _ _ _ (scopts _ commit? _ _)) (not commit?)]
      [(hpat:commit inner) #f]
      [(ehpat _ head repc _)
       (or (not (equal? repc #f))
           (recur))]
      [_ (recur)]))
  (pattern-ormap p for-pattern))

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
          [(and (pat:seq-end? a) (pat:seq-end? b)) #t]
          ;; ---
          [(and (hpat:single? a) (hpat:single? b))
           (pattern-equal? (hpat:single-pattern a) (hpat:single-pattern b))]
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
     (list 'AND (matrix->sexpr inner))]))
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
    [(pat:action action (pat:any)) (pattern->sexpr action)]
    [(pat:action action inner) (list '~AAND (pattern->sexpr action) (pattern->sexpr inner))]
    [(pat:and patterns) (cons '~and (map pattern->sexpr patterns))]
    [(pat:or _ patterns _) (cons '~or (map pattern->sexpr patterns))]
    [(pat:not pattern) (list '~not (pattern->sexpr pattern))]
    [(pat:pair head tail)
     (cons (pattern->sexpr head) (pattern->sexpr tail))]
    [(pat:head head tail)
     (cons (pattern->sexpr head) (pattern->sexpr tail))]
    [(pat:dots (list eh) tail)
     (list* (pattern->sexpr eh) '... (pattern->sexpr tail))]
    [(pat:dots ehs tail)
     (list* (cons '~alt (map pattern->sexpr ehs)) '... (pattern->sexpr tail))]
    [(pat:describe sp _ _ _) (list '~describe (pattern->sexpr sp))]
    [(pat:delimit sp) (list '~delimit-cut (pattern->sexpr sp))]
    [(pat:commit sp) (list '~commit (pattern->sexpr sp))]
    [(pat:ord pattern _ _) (list '~ord (pattern->sexpr pattern))]
    [(pat:post sp) (list '~post (pattern->sexpr sp))]
    [(pat:seq-end) '()]
    [(action:cut) '~!]
    [(action:fail cnd msg) (list '~fail)]
    [(action:bind attr expr) (list '~bind)]
    [(action:and as) (cons '~and (map pattern->sexpr as))]
    [(action:parse sp expr) (list '~parse (pattern->sexpr sp))]
    [(action:do stmts) (list '~do)]
    [(action:undo stmts) (list '~undo)]
    [(action:ord ap _ _) (list '~ord (pattern->sexpr ap))]
    [(action:post ap) (list '~post (pattern->sexpr ap))]
    [(hpat:single sp) (pattern->sexpr sp)]
    [(hpat:var/p name parser _ _ _ _)
     (cond [(and parser (regexp-match #rx"^parser-(.*)$" (symbol->string (syntax-e parser))))
            => (lambda (m) (format-symbol "~a:~a" (or name '_) (cadr m)))]
           [else (if name (syntax-e name) '_)])]
    [(hpat:seq lp) (cons '~seq (pattern->sexpr lp))]
    [(hpat:action ap hp) (list '~AAND (pattern->sexpr ap) (pattern->sexpr hp))]
    [(hpat:and hp sp) (list '~and (pattern->sexpr hp) (pattern->sexpr sp))]
    [(hpat:or _ hps _) (cons '~or (map pattern->sexpr hps))]
    [(hpat:describe hp _ _ _) (list '~describe (pattern->sexpr hp))]
    [(hpat:delimit hp) (list '~delimit-cut (pattern->sexpr hp))]
    [(hpat:commit hp) (list '~commit (pattern->sexpr hp))]
    [(hpat:ord hp _ _) (list '~ord (pattern->sexpr hp))]
    [(hpat:post hp) (list '~post (pattern->sexpr hp))]
    [(hpat:peek hp) (list '~peek (pattern->sexpr hp))]
    [(hpat:peek-not hp) (list '~peek-not (pattern->sexpr hp))]
    [(ehpat _as hpat repc _cn)
     (if (eq? repc #f) (pattern->sexpr hpat) (list '~REPC (pattern->sexpr hpat)))]
    [_ '<Pattern>]))

;; ============================================================

(define (bit n) (arithmetic-shift 1 n))
(define (bitwhen n cnd?) (if cnd? n 0))

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
(define HAS:SSTXCLASS (bit 12))  ;; but not integrated stxclass
(define HAS:HSTXCLASS (bit 13))
(define HAS:REFLECT   (bit 14))
(define HAS:FAIL      (bit 15))  ;; has ~fail check
(define HAS:DOTS      (bit 16))
(define HAS:DOTS:ALTS (bit 17))
(define HAS:DOTS:HEAD (bit 18))
(define HAS:DOTS:REPC (bit 19))
(define HAS:DOTS:NNIL (bit 20))  ;; dots tail is NOT null

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
                (flag 's-class HAS:SSTXCLASS)
                (flag 'h-class HAS:HSTXCLASS)
                (flag 'reflect HAS:REFLECT)
                (flag 'inlsc HAS:INLSC)
                (flag 'fail HAS:FAIL)
                (flag 'dots HAS:DOTS)
                (flag 'dots-alts HAS:DOTS:ALTS)
                (flag 'dots-head HAS:DOTS:HEAD)
                (flag 'dots-repc HAS:DOTS:REPC)
                (flag 'dots-nnil HAS:DOTS:REPC))))

;; pattern-props : *Pattern -> Nat
;; Returns #t if p has expr that needs attr bindings (or do env!)
(define (pattern-props p)
  (define ior bitwise-ior)
  (define (clr n . ks) (bitwise-and n (apply bitwise-xor -1 ks)))
  (define (handle p recur)
    (match p
      ;; -- S patterns
      ;; [(pat:any) (recur)]
      ;; [(pat:svar name) (recur)]
      [(pat:var/p _ _ argu _ _ opts)
       (ior (bitwhen (+ HAS:CUT EXPOSED:CUT) (not (scopts-delimit-cut? opts)))
            (bitwhen EXPOSED:MULTI (not (scopts-commit? opts)))
            (bitwhen HAS:EXPR (not (inv-argu? argu)))
            HAS:UNDO HAS:SSTXCLASS)]
      [(pat:reflect _ _ _ _ _)
       (ior EXPOSED:MULTI HAS:EXPR HAS:UNDO HAS:SSTXCLASS HAS:REFLECT (recur))]
      ;; [(pat:datum _) (recur)]
      [(pat:literal _ ip lp)
       (ior (bitwhen HAS:EXPR (not (and (inv-expr? ip) (inv-expr? lp))))
            HAS:LITERAL HAS:UNDO
            (recur))]
      ;; [(pat:action a sp) (recur)]
      [(pat:head headp tailp) (ior HAS:HEAD (recur))]
      ;; [(pat:pair headp tailp) (recur)]
      ;; [(pat:vector sp) (recur)]
      ;; [(pat:box sp) (recur)]
      ;; [(pat:pstruct key sp) (recur)]
      [(pat:describe sp desc _ _)
       (ior (bitwhen HAS:EXPR (not (inv-expr? desc)))
            (recur))]
      ;; [(pat:and ps) (recur)]
      [(pat:or _ ps _) (ior EXPOSED:MULTI HAS:OR (recur))]
      [(pat:not sp) (clr (recur) EXPOSED:MULTI)]
      [(pat:dots (list (ehpat _ (? single-pattern? headp) repc _)) (pat:datum '()))
       (ior HAS:DOTS (handle-repc repc) (recur))]
      [(pat:dots headps tailp)
       (ior HAS:DOTS
            (bitwhen EXPOSED:MULTI #t)
            (bitwhen HAS:DOTS:ALTS (> (length headps) 1))
            (bitwhen HAS:DOTS:NNIL (not (equal? tailp (pat:datum '()))))
            (recur))]
      [(pat:delimit sp) (clr (recur) EXPOSED:CUT)]
      [(pat:commit sp) (clr (recur) EXPOSED:CUT EXPOSED:MULTI)]
      ;; [(pat:ord sp _ _) (recur)]
      ;; [(pat:post sp) (recur)]
      [(pat:integrated _ _ _ _)
       (ior HAS:INLSC (recur))]
      ;; -- A patterns
      [(action:cut) (ior HAS:CUT EXPOSED:CUT)]
      [(action:fail cnd msg)
       (ior (bitwhen HAS:EXPR (not (and (inv-expr? cnd) (inv-expr? msg))))
            HAS:FAIL)]
      [(action:bind attr expr)
       (ior (bitwhen HAS:EXPR (not (inv-expr? expr)))
            (recur))]
      ;; [(action:and ps) (recur)]
      [(action:parse sp rhs)
       (ior (bitwhen HAS:EXPR (not (inv-expr? rhs)))
            (recur))]
      [(action:do stmts) (ior HAS:EXPR HAS:UNDO (recur))]
      [(action:undo stmts) (ior HAS:EXPR HAS:UNDO (recur))]
      ;; [(action:ord sp _ _) (recur)]
      ;; [(action:post sp) (recur)]
      ;; -- H patterns
      ;; [(hpat:single sp) (recur)]
      [(hpat:var/p _ _ argu _ _ opts)
       (ior (bitwhen (+ HAS:CUT EXPOSED:CUT) (not (scopts-delimit-cut? opts)))
            (bitwhen EXPOSED:MULTI (not (scopts-commit? opts)))
            (bitwhen HAS:EXPR (not (inv-argu? argu)))
            HAS:UNDO HAS:HSTXCLASS)]
      [(hpat:reflect _ _ _ _ _)
       (ior EXPOSED:MULTI HAS:EXPR HAS:UNDO HAS:HSTXCLASS HAS:REFLECT)]
      ;; [(hpat:seq lp) (recur)]
      ;; [(hpat:action a hp) (recur)]
      [(hpat:describe hp desc _ _)
       (ior (bitwhen HAS:EXPR (not (inv-expr? desc)))
            (recur))]
      ;; [(hpat:and hp sp) (recur)]
      [(hpat:or _ ps _) (ior EXPOSED:MULTI HAS:OR (recur))]
      [(hpat:delimit hp) (clr (recur) EXPOSED:CUT)]
      [(hpat:commit hp) (clr (recur) EXPOSED:CUT EXPOSED:MULTI)]
      ;; [(hpat:ord hp _ _) (recur)]
      ;; [(hpat:post hp) (recur)]
      ;; [(hpat:peek hp) (recur)]
      ;; [(hpat:peek-not hp) (recur)]
      ;; EH patterns
      [(ehpat _ hp repc _)
       (ior (bitwhen HAS:DOTS:HEAD (head-pattern? hp))
            (handle-repc repc)
            (recur))]
      [_ (recur)]))
  (define (handle-repc repc)
    (match repc
      [(rep:once name under over)
       (ior HAS:DOTS:REPC
            (bitwhen HAS:EXPR (not (andmap inv-expr? (list name under over)))))]
      [(rep:optional name over defaults)
       (ior HAS:DOTS:REPC
            (bitwhen HAS:EXPR (not (and (inv-expr? name) (inv-expr? over))))
            (apply bitwise-ior (map pattern-props defaults)))]
      [(rep:bounds min max name under over)
       (ior HAS:DOTS:REPC
            (bitwhen HAS:EXPR (not (andmap inv-expr? (list min max name under over)))))]
      ['#f 0]))
  (define (pattern-props p) (pattern-reduce-left p handle bitwise-ior))
  (pattern-props p))

;; pattern-main-pattern : *Pattern -> *Pattern
(define (pattern-main-pattern p0)
  (let loop ([p p0])
    (match p
      [(pat:and (cons p _)) (loop p)]
      [(pat:ord p _ _) (loop p)]
      [(hpat:and hp _) (loop hp)]
      [(hpat:ord p _ _) (loop p)]
      [_ p])))

;; ============================================================

(define (pattern-size p)
  (pattern-reduce-left p (lambda (p recur) (+ 1 (recur))) +))

;; Conservative approximation: Returns #t if the expression is
;; independent of pattern matching: stateless, no references to attrs
;; bound by pattern, etc.
(define (inv-expr? e)
  (cond [(eq? e #f) #t]
        [(not (syntax? e)) #f]
        [else
         (syntax-case e (quote syntax-local-phase-level)
           [(quote _) #t]
           [(quote-syntax _) #t]
           [(syntax-local-phase-level) #t] ;; FIXME: check #%app?
           [datum
            (let ([d (syntax-e #'datum)]) (or (number? d) (boolean? d) (string? d)))
            (free-identifier=? (datum->syntax #'datum '#%datum) #'#%datum)]
           [_ #f])]))

(define (inv-argu? a)
  (match a
    [(arguments pargs kws kwargs)
     (and (andmap inv-expr? pargs) (andmap inv-expr? kwargs))]))

;; ----------------------------------------
;; Abstract matching

;; An AbsMatch is a bitvector encoding of *sets* of AbsValue,
;; where AbsValue ::= null | identifier | keyword | other | (cons AbsValue _).
;; Note: positive numbers encode finite sets; negative encode cofinite sets.

;; The AbsMatch of a pattern represents an upper bound on the terms the pattern
;; can accept. Since it is an upper bound only, the complement is always AM-ALL.

(define AM-NULL  (bit 0))
(define AM-ID    (bit 1))
(define AM-KW    (bit 2))
(define AM-OTHER (bit 3))
(define AM-ALL   -1)
(define (AM-cons a) (arithmetic-shift a 4))
(define (AM-car a)  (arithmetic-shift a -4))
(define AM-PAIR-ALL (AM-cons AM-ALL))

(define (AM-and . xs) (apply bitwise-and xs))
(define (AM-or  . xs) (apply bitwise-ior xs))
(define (AM-andmap f xs)
  (for/fold ([acc -1]) ([x (in-list xs)]) (bitwise-and acc (f x))))
(define (AM-ormap f xs)
  (for/fold ([acc 0]) ([x (in-list xs)]) (bitwise-ior acc (f x))))

(define (AM-overlap? x y) (not (zero? (bitwise-and x y))))

(define (AM->list a)
  (cond [(= a  0) '()]
        [(= a -1) '(ALL)]
        [else (append (if (AM-overlap? a AM-NULL) '(null) '())
                      (if (AM-overlap? a AM-ID)   '(id)   '())
                      (if (AM-overlap? a AM-KW)   '(kw)   '())
                      (if (AM-overlap? a AM-OTHER) '(other) '())
                      (for/list ([x (in-list (AM->list (AM-car a)))])
                        `(cons ,x _)))]))

;; pattern-AM : *Pattern -> AbstractMatch
(define (pattern-AM p)
  (define ior bitwise-ior)
  (match p
    ;; -- S patterns
    [(pat:any) AM-ALL]
    [(pat:svar name) AM-ALL]
    [(pat:var/p name parser argu nested-attrs role opts) AM-ALL]
    [(pat:literal id input-phase lit-phase) AM-ID]
    [(pat:datum datum)
     (let loop ([x datum])
       (cond [(pair? x) (AM-cons (loop (car x)))]
             [(null? x) AM-NULL]
             [(symbol? x) AM-ID]
             [(keyword? x) AM-KW]
             [else AM-OTHER]))]
    [(pat:action ap sp) (pattern-AM sp)]
    [(pat:head headp tailp)
     (define headam (pattern-AM headp))
     (if (AM-overlap? headam AM-NULL)
         (AM-or headam (pattern-AM tailp))
         headam)]
    [(pat:dots heads tailp)
     (AM-or (AM-ormap pattern-AM heads) (pattern-AM tailp))]
    [(pat:andu ps) (AM-andmap pattern-AM ps)]
    [(pat:and ps) (AM-andmap pattern-AM ps)]
    [(pat:or attrs ps attrss) (AM-ormap pattern-AM ps)]
    [(pat:not sp) AM-ALL]
    [(pat:pair headp tailp) (AM-cons (pattern-AM headp))]
    [(pat:vector sp) AM-OTHER]
    [(pat:box sp) AM-OTHER]
    [(pat:pstruct key sp) AM-OTHER]
    [(pat:describe sp description transparent? role) (pattern-AM sp)]
    [(pat:delimit sp) (pattern-AM sp)]
    [(pat:commit sp) (pattern-AM sp)]
    [(pat:reflect obj argu attr-decls name nested-attrs) AM-ALL]
    [(pat:ord sp group index) (pattern-AM sp)]
    [(pat:post sp) (pattern-AM sp)]
    [(pat:integrated name predicate description role)
     ;; FIXME: relies on contents from lib.rkt
     (cond [(equal? description "identifier") AM-ID]
           [(equal? description "keyword") AM-KW]
           [(equal? description "expression") (bitwise-xor AM-ALL AM-KW)]
           [else AM-OTHER])]
    [(pat:fixup stx bind varname scname argu sep role parser*) AM-ALL]
    [(pat:and/fixup stx ps) (AM-andmap pattern-AM ps)]
    [(pat:seq-end) AM-NULL] ;; Should only occur in ListPattern!
    [(? action-pattern?) 0]
    ;; For head pattern, represents list of matched terms.
    [(hpat:single sp) (AM-cons (pattern-AM sp))]
    [(hpat:var/p name parser argu nested-attrs role scopts) AM-ALL]
    [(hpat:seq sp) (pattern-AM sp)]
    [(hpat:action ap sp) (pattern-AM sp)]
    [(hpat:andu ps) (AM-andmap pattern-AM ps)]
    [(hpat:and hp sp) (AM-and (pattern-AM hp) (pattern-AM sp))]
    [(hpat:or attrs ps attrss) (AM-ormap pattern-AM ps)]
    [(hpat:describe sp description transparent? role) (pattern-AM sp)]
    [(hpat:delimit sp) (pattern-AM sp)]
    [(hpat:commit sp) (pattern-AM sp)]
    [(hpat:reflect obj argu attr-decls name nested-attrs) AM-ALL]
    [(hpat:ord sp group index) (pattern-AM sp)]
    [(hpat:post sp) (pattern-AM sp)]
    [(hpat:peek sp) AM-NULL]
    [(hpat:peek-not sp) AM-NULL]
    [(ehpat _ hp repc _) (pattern-AM hp)]))
