#lang racket
(require racket/port
         (only-in "opt.rkt" pattern-prop-symbols pattern-size)
         (submod "opt-logging.rkt" parse-log)
         (only-in "opt-logging.rkt" pattern->sexpr))

;; PLTSTDERR="debug@stxpattern" raco setup -D -j 1 2> STXPATTERN.log

(define-syntax-rule (inc! x e) (set! x (+ x e)))
(define-syntax-rule (push! x e) (set! x (cons e x)))
(define (I x) (if x 1 0))
(define (hinc! h k e) (hash-set! h k (+ e (hash-ref h k 0))))

;; ============================================================

(define known-flags pattern-prop-symbols)

(define collector%
  (class object%
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

    (super-new)

    (define/public (process-cs-info info)
      ;; info : (Listof (list Pattern Props MainPattern Props))
      (inc! cs-count 1)
      (push! cs-npatternss (length info))
      (define allprops (remove-duplicates (apply append (map cadr info))))
      (for ([flag (in-list known-flags)])
        (hinc! cs-flagh flag (I (memq flag allprops))))
      (for ([pinfo (in-list info)])
        (process-p-info pinfo)))

    (define/public (process-p-info info)
      (inc! p-count 1)
      (match info
        [(list pattern props main-pattern main-props)
         (push! w-sizes (pattern-size pattern))
         (push! m-sizes (pattern-size main-pattern))
         (for ([flag (in-list known-flags)])
           (hinc! w-flagh flag (I (memq flag props)))
           (hinc! m-flagh flag (I (memq flag main-props))))]))

    (define/public (process-simple p-sexpr) (void))

    ;; ----------------------------------------

    (define/public (print-flag-table flagh total)
      (printf "Features used:\n")
      (for ([flag (in-list known-flags)])
        (define flagct (hash-ref flagh flag 0))
        (printf " - ~a: ~a (~a%)\n"
                (~a #:width 12 flag)
                (~r #:min-width 4 flagct)
                (~r #:precision 2 (* 100.0 (/ flagct total))))))

    (define/public (print show-clause-sets? show-main?)
      (when show-clause-sets?
        (printf "== Clause-Set Info ==\n")
        (printf "Set count: ~s\n" cs-count)
        (unless (zero? cs-count)
          (printf "Set mean patterns: ~a\n" (~r #:precision 2 (mean cs-npatternss)))
          (for ([md (in-list '(1 2))])
            (let ([ct (for/sum ([n (in-list cs-npatternss)] #:when (= n md)) 1)])
              (printf " w/ ~a patterns: ~a (~a%)\n" md ct (~r #:precision 2 (* 100 ct (/ cs-count))))))
          (print-flag-table cs-flagh cs-count))
        (newline))

      (printf "== Pattern Info ==\n")
      (printf "Pattern count: ~s\n" p-count)
      (unless (zero? p-count)
        (printf "Whole pattern mean size: ~a\n" (~r #:precision 2 (mean w-sizes)))
        (printf "Whole pattern flags:\n")
        (print-flag-table w-flagh p-count)
        (when show-main?
          (printf "Main pattern mean size: ~a\n" (~r #:precision 2 (mean m-sizes)))
          (printf "Main pattern flags:\n")
          (print-flag-table m-flagh p-count))))

    ))

(define (mean xs) (/ (for/sum ([x xs]) x) (for/sum ([x xs]) 1)))

;; ============================================================

(define pre (new collector%))
(define post (new collector%))

(for ([e (in-list (parse-log-input (current-input-port)))])
  (case (car e)
    [("simple")             ;; Pattern
     (eprintf "SIMPLE ~e\n" (pattern->sexpr (cdr e)))]
    [("patterns")           ;; (Listof (list Pattern Props MainPattern Props))
     (send pre process-cs-info (cdr e))]
    [("post/subpatterns")   ;; (Listof (list Pattern Props MainPattern Props))
     (send post process-cs-info (cdr e))]
    [else (void)]))

(printf "** Pre-optimization **\n")
(send pre print #t #t)
(newline)
(printf "** Post-optimization **\n")
(send post print #f #f)

;; ----------------------------------------

;; FIXME: post-optimization "clause set" isn't :(

;; FIXME: dots-head reporting messed up
