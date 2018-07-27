#lang racket/base

;; A SParser is (Stx Stxish Env Progress ExpectStack SFK SSK -> ANS)
;; A SSK is (SFK Env -> ANS)
;; A SFK is (Failure -> ANS)

(define ((rs:any) x cx env pr es fk sk)
  (sk fk env))

(define ((rs:svar) x cx pr es fk sk)
  (sk fk (cons (datum->syntax cx x) env)))

(define ((rs:pair p1 p2) x cx env pr es fk sk)
  (define d (if (syntax? x) (syntax-e x) x))
  (cond [(pair? d)
         (let ([x1 (car d)]
               [x2 (cdr d)]
               [cx2 (if (syntax? x2) x2 cx)])
           (p1 x1 x1 env (pr-add-car pr) es fk
               (lambda (fk env) (p2 x2 cx2 env (pr-add-cdr pr) es fk sk))))]
        [else (fk ...)]))

(define ((rs:vector p) x cx env pr es fk sk)
  (define d (if (syntax? x) (syntax-e x) x))
  (cond [(vector? d)
         (p (vector->list d) (if (syntax? x) x cx) env pr es fk sk)]
        [else (fk ...)]))

(define ((rs:box p) x cx env pr es fk sk)
  (define d (if (syntax? x) (syntax-e x) x))
  (cond [(box? d)
         (p (unbox d) (if (syntax? x) x cx) env pr es fk sk)]
        [else (fk ...)]))

(define ((rs:pstruct key p) x cx env pr es fk sk)
  (define d (if (syntax? x) (syntax-e x) x))
  (cond [(prefab-struct-key d)
         => (lambda (xkey)
              (cond [(equal? xkey key)
                     (p (cdr (vector->list (struct->vector d)))
                        (if (syntax? x) x cx)
                        env pr es fk sk)]
                    [else (fk ...)]))]
        [else (fk ...)]))

(define ((rs:integrated pred desc) x cx env pr es fk sk)
  (if (pred x)
      (sk fk (cons x env))
      (fk ...)))

(define ((rs:literal lit-id input-phase lit-phase) x cx env pr es fk sk)
  (if (and (identifier? x) (free-identifier=? id lit-id input-phase lit-phase))
      (sk fk env)
      (fk ...)))

(define ((rs:datum datum) x cx env pr es fk sk)
  (if (equal? (syntax->datum (datum->syntax #f x)) datum)
      (sk fk env)
      (fk ...)))

(define ((rs:action ap sp) x cx env pr es fk sk)
  (ap x cx env pr es fk (lambda (fk env) (sp x cx env pr es fk sk))))

;; A HParser is (Stx Stxish Env Progress ExpectStack HFK HSK -> ANS)
;; A HSK is (SFK Env Stx Stxish Progress -> ANS)
;; A HFK is (Failure -> ANS)

(define ((rs:head p1 p2) x cx env pr es fk sk)
  (p1 x cx env pr es fk
      (lambda (fk env x cx pr) (p2 x cx env pr es fk sk))))

(define ((rs:and p1 p2) x cx env pr es fk sk)
  (p1 x cx env pr es fk (lambda (fk env) (p2 x cx env pr es fk sk))))

(define ((r:or p1 p2) x cx env pr es fk sk)
  (p1 x cx env pr es (lambda (f) (p2 x cx env pr es (lambda (f2) (fk (join-failures f1 f2))) sk)) sk))

(define ((rs:not p) x cx env pr es fk sk)
  (p x cx env pr es (lambda (f) (sk fk env)) (lambda (fk* env*) (fk ...))))

(define ((r:describe p) x cx env pr es fk sk)
  (let ([es ....])
    (p x cx env pr es fk sk)))

(define ((rs:commit p) x cx env pr es fk sk)
  (p x cx env pr es fk (lambda (fk* env) (sk fk env))))

(define ((r:ord p group index) x cx env pr es fk sk)
  (p x cx env (pr-add-ord pr group index) es fk sk))

(define ((r:post p) x cx env pr es fk sk)
  (p x cx env (pr-add-post pr) es fk sk))

;;(define-struct pat:var/p (parser opts) #:prefab)
;;(define-struct pat:dots (heads tail) #:prefab)
;;(define-struct pat:delimit (pattern) #:prefab)

;; ----

;; (define ((ra:cut) env pr es fk sk) ...)

(define ((ra:fail pred) env pr es fk sk)
  (cond [(pred env)
         => (lambda (irritant)
              (fk ...))]
        [else (sk fk env)]))

(define ((ra:bind rhs) env pr es fk sk)
  (sk fk (cons (rhs env) env)))

(define ((ra:and p1 p2) env pr es fk sk)
  (p1 env pr es fk (lambda (fk env) (p2 env pr es fk sk))))

(define ((ra:parse p rhs) env pr es fk sk)
  (let ([x (rhs env)])
    (p x (datum->syntax #f x) env pr es fk sk)))

;; ~do just doesn't make sense...

(define ((ra:ord p group index) env pr es fk sk)
  (p env (pr-add-ord pr group index) es fk sk))

(define ((ra:post p) env pr es fk sk)
  (p env (pr-add-post pr) es fk sk))

;; ----

;; rh:seq takes p arg where (rs:datum '()) replaced with (rh:end)!
(define ((rh:seq p) x cx env pr es fk sk)
  (p x cx env pr es fk sk))

(define ((rh:end) x cx env pr es fk sk) (sk fk env x cx pr))

(define (rh:s p) (rs:pair p (lambda (x cx env pr es fk sk) (sk fk env x cx pr))))

(define ((rh:action a p) x cx env pr es fk sk)
  (a env pr es fk (lambda (fk env) (p x cx env pr es fk sk))))

(define ((rh:and p1 p2) ...))

;; SAME AS S: or, describe, ord, post

(define ((rh:commit p) x cx env pr es fk sk)
  (p x cx env pr es fk (lambda (fk* env x cx pr) (fk env x cx pr))))

(define ((rh:peek p) x cx env pr es fk sk)
  (p x cx env pr es fk (lambda (fk env x* cx* pr*) (sk fk env x cx pr))))

(define ((rh:peek-not p) x cx env pr es fk sk)
  (p x cx env pr es
     (lambda (f) (sk fk env))
     (lambda (fk* env x cx pr) (fk ...))))

#|
A HeadPattern is one of 
  (hpat:var/p Id Id Arguments (Listof IAttr) Stx scopts)
  (hpat:seq ListPattern)
  (hpat:delimit HeadPattern)
  (hpat:reflect stx Arguments (listof SAttr) id (listof IAttr))
|#

#|
An EllipsisHeadPattern is
  (ehpat (Listof IAttr) HeadPattern RepConstraint Boolean)

A RepConstraint is one of
  (rep:once stx stx stx)
  (rep:optional stx stx (listof BindAction))
  (rep:bounds nat posint/+inf.0 stx stx stx)
  #f
|#

(define-struct ehpat (attrs head repc check-null?) #:prefab)
(define-struct rep:once (name under-message over-message) #:prefab)
(define-struct rep:optional (name over-message defaults) #:prefab)
(define-struct rep:bounds (min max name under-message over-message) #:prefab)
