#lang racket/base
(require syntax/parse/private/minimatch)
(provide make-exn:fail:syntax:rich
         (rename-out [make-exn:fail:syntax:rich exn:fail:syntax:rich])
         exn:fail:syntax:rich?
         exn:fail:syntax:rich-richmsg
         raise-rich-syntax-error
         rich-message?
         rich-message->string
         rich-message->termss
         rich-message-term-index->color)

#|
(module rich-exn racket/kernel
  (#%declare #:cross-phase-persistent)
  (#%provide struct:exn:fail:syntax:rich
             make-exn:fail:syntax:rich
             exn:fail:syntax:rich?
             exn:fail:syntax:rich-accessor)
  (define-values (struct:exn:fail:syntax:rich
                  make-exn:fail:syntax:rich
                  exn:fail:syntax:rich?
                  exn:fail:syntax:rich-accessor
                  exn:fail:syntax:rich-mutator)
    (make-struct-type 'exn:fail:syntax:rich struct:exn:fail:syntax 1 0 #f null #f)))
(require (submod "." rich-exn))

(define exn:fail:syntax:rich-richmsg
  (make-struct-field-accessor exn:fail:syntax:rich-accessor 0 'exn:fail:syntax:rich-richmsg))

(define (raise-rich-syntax-error msg stx)
  (unless (rich-message? msg)
    (raise-argument-error 'raise-rich-syntax-error 'rich-message? 0 msg stx))
  (raise (make-exn:fail:syntax:rich
          (rich-message->string msg)
          (current-continuation-marks)
          (list stx)
          msg)))
|#

(define (make-exn:fail:syntax:rich . args)
  (error 'unimplemented))

(define (exn:fail:syntax:rich? exn)
  (and (exn:fail:syntax? exn)
       (continuation-mark-set-first (exn-continuation-marks exn) 'rich-message)
       #t))

(define (exn:fail:syntax:rich-richmsg exn)
  (continuation-mark-set-first (exn-continuation-marks exn) 'rich-message))

(define (raise-rich-syntax-error msg stx [substx #f])
  (unless (rich-message? msg)
    (raise-argument-error 'raise-rich-syntax-error 'rich-message? 0 msg stx))
  (with-continuation-mark 'rich-message msg
    (raise-syntax-error #f (rich-message->string msg) stx substx)))

;; A RichMessage is one of
;; - String
;; - (list 'span RichMessage ...)
;; - (list 'term String (Listof Syntax))

(define (rich-message? x)
  (match x
    [(? string?) #t]
    [(cons 'span (? list? xs))
     (andmap rich-message? xs)]
    [(list 'term (? string?) (? list? stxs))
     (andmap syntax? stxs)]
    [_ #f]))

(define (rich-message->string x)
  (match x
    [(? string?) x]
    [(cons 'span (? list? xs))
     (apply string-append (map rich-message->string xs))]
    [(list 'term (? string? desc) stxs)
     desc]))

;; rich-message->termss : RichMesasge -> (Listof (Listof Syntax))
(define (rich-message->termss x)
  (let loop ([x x] [onto null])
    (match x
      [(? string?) onto]
      [(cons 'span (? list? xs))
       (for/fold ([onto onto]) ([x (in-list (reverse xs))])
         (loop x onto))]
      [(list 'term _ stxs)
       (cons (if (list? stxs) stxs (list stxs)) onto)])))

;; rich-message-term-index->color : Nat -> String
(define (rich-message-term-index->color index)
  (if (< index (length term-colors)) (list-ref term-colors index) "gray"))

(define term-colors
  '("green" "violet" "lightblue"))
