#lang racket/load
(require racket/port
         math/statistics)

(define-syntax-rule (inc! x e) (set! x (+ x e)))
(define-syntax-rule (push! x e) (set! x (cons e x)))
(define (I x) (if x 1 0))
(define (hinc! h k e) (hash-set! h k (+ e (hash-ref h k 0))))

;; ClauseSets info
(define cs-count 0)
(define cs-npatternss null)
(define cs-flagh (make-hasheq))

;; Pattern info
(define p-count 0)
(define m-sizes null)
(define w-sizes null)
(define m-flagh (make-hasheq))
(define w-flagh (make-hasheq))

;; ============================================================

(define known-flags
  '(E-cut E-multi cut undo expr or head lit s-class h-class reflect inlsc fail dots
          dots-alts dots-head dots-repc dots-nnil))

(define (process-cs-info info)
  (match info
    [(list npatterns props)
     (push! cs-npatternss npatterns)
     (for ([flag (in-list known-flags)])
       (hinc! cs-flagh flag (I (memq flag props))))]))

(define (process-p-info info)
  (match info
    [(list (list (list 'size main-size)  (list 'attrs main-attrs)  main-props)
           (list (list 'size whole-size) (list 'attrs whole-attrs) whole-props))
     (for ([flag (in-list known-flags)])
       (push! m-sizes main-size)
       (push! w-sizes whole-size)
       (hinc! m-flagh flag (I (memq flag main-props)))
       (hinc! w-flagh flag (I (memq flag whole-props))))]
    [(list info)
     (process-p-info (list info info))]))

(define (process-pattern p-sexpr) (void))

;; ============================================================

(for ([line (in-lines)])
  (cond [(regexp-match? #rx"^;!" line)
         (inc! cs-count 1)
         (process-cs-info (read (open-input-string (substring line 2))))]
        [(regexp-match? #rx"^;@" line)
         (inc! p-count 1)
         (process-p-info (read (open-input-string (substring line 2))))]
        [(regexp-match? #rx"^stxpattern: " line)
         (void)]
        [(regexp-match? #rx"^[ ]*$" line)
         (void)]
        [else
         (process-pattern (read (open-input-string line)))]))

;; ----------------------------------------

(define (print-flag-table flagh total)
  (for ([flag (in-list known-flags)])
    (define flagct (hash-ref flagh flag 0))
    (printf " - ~a: ~a (~a%)\n"
            (~a #:width 12 flag) (~r #:min-width 4 flagct) (~r #:precision 2 (* 100.0 (/ flagct total))))))

(printf "Set count: ~s\n" cs-count)
(printf "Set mean patterns: ~a\n" (~r #:precision 2 (mean cs-npatternss)))
(print-flag-table cs-flagh cs-count)
(newline)
(printf "Pattern count: ~s\n" p-count)
(printf "Whole pattern mean size: ~a\n" (~r #:precision 2 (mean w-sizes)))
(printf "Whole pattern flags:\n")
(print-flag-table w-flagh p-count)
(printf "Main pattern mean size: ~a\n" (~r #:precision 2 (mean m-sizes)))
(printf "Main pattern flags:\n")
(print-flag-table m-flagh p-count)

;; FIXME: dots-head reporting messed up
