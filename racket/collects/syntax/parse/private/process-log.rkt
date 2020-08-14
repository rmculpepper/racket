#lang racket
(require racket/port
         math/statistics
         (only-in "opt.rkt" pattern-size)
         (submod "opt-logging.rkt" parse-log))

;; PLTSTDERR="debug@stxpattern" raco setup -D -j 1 2> STXPATTERN.log

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
  ;; info : (Listof (list Pattern Props MainPattern Props))
  (inc! cs-count 1)
  (push! cs-npatternss (length info))
  (define allprops (remove-duplicates (apply append (map cadr info))))
  (for ([flag (in-list known-flags)])
    (hinc! cs-flagh flag (I (memq flag allprops))))
  (for ([pinfo (in-list info)])
    (process-p-info pinfo)))

(define (process-p-info info)
  (inc! p-count 1)
  (match info
    [(list pattern props main-pattern main-props)
     (push! w-sizes (pattern-size pattern))
     (push! m-sizes (pattern-size main-pattern))
     (for ([flag (in-list known-flags)])
       (hinc! w-flagh flag (I (memq flag props)))
       (hinc! m-flagh flag (I (memq flag main-props))))]))

(define (process-simple p-sexpr) (void))

;; ============================================================

(for ([e (in-list (parse-log-input (current-input-port)))])
  (case (car e)
    [("simple")             ;; Pattern
     (process-simple (cdr e))]
    [("patterns")           ;; (Listof (list Pattern Props MainPattern Props))
     (process-cs-info (cdr e))]
    [("post/subpatterns")   ;; (Listof (list Pattern Props MainPattern Props))
     (void)]
    [else (void)]))

;; ----------------------------------------

(define (print-flag-table flagh total)
  (for ([flag (in-list known-flags)])
    (define flagct (hash-ref flagh flag 0))
    (printf " - ~a: ~a (~a%)\n"
            (~a #:width 12 flag) (~r #:min-width 4 flagct) (~r #:precision 2 (* 100.0 (/ flagct total))))))

(printf "Set count: ~s\n" cs-count)
(unless (zero? cs-count)
  (printf "Set mean patterns: ~a\n" (~r #:precision 2 (mean cs-npatternss)))
  (print-flag-table cs-flagh cs-count))
(newline)
(printf "Pattern count: ~s\n" p-count)
(unless (zero? p-count)
  (printf "Whole pattern mean size: ~a\n" (~r #:precision 2 (mean w-sizes)))
  (printf "Whole pattern flags:\n")
  (print-flag-table w-flagh p-count)
  (printf "Main pattern mean size: ~a\n" (~r #:precision 2 (mean m-sizes)))
  (printf "Main pattern flags:\n")
  (print-flag-table m-flagh p-count))

;; FIXME: dots-head reporting messed up
