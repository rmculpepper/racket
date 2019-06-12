#lang racket/base
(require racket/syntax
         "minimatch.rkt"
         "rep-patterns.rkt"
         "tree-util.rkt")
(provide (all-defined-out))

(define-logger stxpattern)

(struct WAS-SYNTAX (value) #:prefab)
(define (value->writeable v)
  (tree-transform v (lambda (v) (if (syntax? v) (WAS-SYNTAX (syntax->datum v)) v))))
(define (writeable->value w)
  (tree-transform w (lambda (w) (if (WAS-SYNTAX? w) (datum->syntax #f (WAS-SYNTAX-value w)) w))))

(define (log-stxpattern?) (log-level? stxpattern-logger 'debug))
(define-syntax-rule (log-stxpattern subtopic value)
  (log-stxpattern-debug "%%%~a%%%~s" subtopic (value->writeable value)))

(module* parse-log #f
  (require racket/port)
  (provide (all-defined-out))

  (define (parse-stxpattern-line line)
    (cond [(regexp-match #rx"%%%([^%]*)%%%(.*)$" line)
           => (lambda (m)
                (cons (cadr m) (writeable->value (read (open-input-string (caddr m))))))]
          [else #f]))
  (define (parse-log-file file)
    (call-with-input-file file parse-log-input))
  (define (parse-log-input in)
    (filter values (map parse-stxpattern-line (port->lines in)))))

;; ============================================================
;; Pattern -> S-Expression (lossy)

(define current-pvar->symbol
  (make-parameter (lambda (s) (if (identifier? s) (syntax-e s) s))))
(define current-stxclass-parser->symbol
  (make-parameter (lambda (p)
                    (cond [(regexp-match #rx"^parse-(.*)$" (symbol->string (syntax-e p)))
                           => (lambda (m) (string->symbol (cadr m)))]
                          [else "??"]))))
(define current-literal->symbol
  (make-parameter (lambda (s) (if (identifier? s) (syntax-e s) s))))
(define (pvar->symbol s)
  (cond [(or (symbol? s) (identifier? s)) ((current-pvar->symbol) s)]
        [else '_]))
(define (stxclass-parser->symbol s)
  ((current-stxclass-parser->symbol) s))
(define (literal->symbol s)
  ((current-literal->symbol) s))
(define (pattern->sexpr p)
  (match p
    [(pat:any) '_]
    [(pat:integrated name pred desc _)
     (format-symbol "~a:~a" (pvar->symbol name) desc)]
    [(pat:svar name)
     (pvar->symbol name)]
    [(pat:var/p name parser _ _ _ _)
     (cond [(and parser (stxclass-parser->symbol parser))
            => (lambda (scname) (format-symbol "~a:~a" (pvar->symbol name) scname))]
           [else (pvar->symbol name)])]
    [(? pat:literal?)
     `(syntax ,(literal->symbol (pat:literal-id p)))]
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
     (cond [(and parser (stxclass-parser->symbol parser))
            => (lambda (scname) (format-symbol "~a:~a" (pvar->symbol name) scname))]
           [else (pvar->symbol name)])]
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
