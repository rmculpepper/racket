#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/lazy-require
                     "../private/kws.rkt")
         "../private/residual.rkt")
(provide define-primitive-splicing-syntax-class)

(begin-for-syntax
 (lazy-require
  [syntax/parse/private/rep-attrs
   (sort-sattrs)]))
;; FIXME: workaround for phase>0 bug in racket/runtime-path (and thus lazy-require)
;; Without this, dependencies don't get collected.
(require racket/runtime-path (for-meta 2 '#%kernel))
(define-runtime-module-path-index _unused_ 'syntax/parse/private/rep-attrs)

(define-syntax (define-primitive-splicing-syntax-class stx)

  (define-syntax-class attr
    #:commit
    (pattern name:id
             #:with depth #'0)
    (pattern [name:id depth:nat]))

  (syntax-parse stx
    [(dssp (name:id param:id ...)
       (~or (~once (~seq #:attributes (a:attr ...))
                   #:name "attributes declaration")
            (~once (~seq #:description description)
                   #:name "description declaration")) ...
       proc:expr)
     #'(begin
         (define (get-description param ...)
           description)
         (define parser
           (let ([permute (mk-permute '(a.name ...))])
             (lambda (x cx pr es rl param ...)
               (lambda (sk fh cp us)
                 (define stx (datum->syntax cx x cx))
                 (define result
                   (let/ec escape
                     (cons 'ok
                           (proc stx
                                 (lambda ([msg #f] [stx #f])
                                   (escape (list 'error msg stx)))))))
                 (case (car result)
                   ((ok)
                    (apply sk fh fh us
                           (check-result pr 'name (length '(a.name ...)) permute x cx (cdr result))))
                   ((error)
                    (let* ([es (es-add-thing pr (get-description param ...) #f rl es)]
                           [es (es-add-message (cadr result) es)])
                      (fh us (failure pr es)))))))))
         (define-syntax name
           (stxclass 'name (arity (length '(param ...)) (length '(param ...)) '() '())
                     (sort-sattrs '(#s(attr a.name a.depth #f) ...))
                     (quote-syntax parser)
                     #t
                     (scopts (length '(a.name ...)) #t #t #f)
                     #f)))]))

(define (mk-permute unsorted-attrs)
  (let* ([sorted-attrs
          (sort unsorted-attrs string<? #:key symbol->string #:cache-keys? #t)]
         [sorted-attrs (reverse sorted-attrs)])
    (if (equal? unsorted-attrs sorted-attrs)
        values
        (let* ([pos-table
                (for/hasheq ([a (in-list unsorted-attrs)] [i (in-naturals)])
                  (values a i))]
               [indexes
                (for/vector ([a (in-list sorted-attrs)])
                  (hash-ref pos-table a))])
          (lambda (result)
            (for/vector ([index (in-vector indexes)])
              (list-ref result index)))))))

(define (check-result pr name attr-count permute x cx result)
  (unless (list? result)
    (error name "parser returned non-list"))
  (let ([rlength (length result)])
    (unless (= rlength (+ 1 attr-count))
      (error name "parser returned list of wrong length; expected length ~s, got ~e"
             (+ 1 attr-count)
             result))
    (let ([skip (car result)])
      ;; Compute rest-x & rest-cx from skip
      (unless (exact-nonnegative-integer? skip)
        (error name "expected exact nonnegative integer for first element of result list, got ~e"
               skip))
      (let-values ([(rest-x rest-cx) (stx-list-drop/cx x cx skip)])
        (list* rest-x rest-cx (ps-add-cdr pr skip) (permute (cdr result)))))))
