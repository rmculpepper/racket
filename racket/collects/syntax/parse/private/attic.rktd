
;; ============================================================
;; Simplify patterns

;; Simplifications:
;; - flatten and patterns, reassociate action:and vs pat:action, etc
;; - make hpat:s explicit?
;; - add pat:no-fail, etc wrapper -- wait, might interfere w/ matrix-based optimization
;; - delete empty action:do, action:undo


;; Compilation step (PAIR):
;; - (pat:head (hpat:s sp) tailp) -> (pat:pair sp tailp)

;; (pat:head (hpat:seq (pat:head h1 t1)) t2) => (pat:head h1 (pat:head (hpat:seq t1) t2))
;; (pat:head (hpat:seq (pat:seq-end)) t)     => t


;; Compilation step (SEQ):
;; - add pat:seq-end
;; - (pat:head (hpat:seq lp[(pat:seq-end)]) tailp) -> lp[tailp]

;; Compilation step (ORD):
;; - add ord patterns

;; Compilation step (OR):
;; - store attributes in or patterns

;; simplify-pattern : *Pattern -> *Pattern
;; Simplifications:
;; - trivial and/or patterns

;; ============================================================

;; Simple patterns:

;; (TP+)          ;; (simple-pattern:list  (Listof TP))
;; (TP+ . TP)     ;; (simple-pattern:list* (Listof TP) TP)
;; (TP* TP ...)   ;; (simple-pattern:list... (Listof TP) TP)

;; where trivial pattern TP = _ | var | var:inlsc  ;; #f | #t | InlSCName

;; Note: these succeed at most once, so can use without making
;; closure for success continuation!

;; Don't do
;; - literals (complicated, adds undos)
;; - vector, box, pstruct (rare, also complicated)
;; - datum???
;; - trees of TPs instead of just linear sequence?

;; Optimize:
;; - drop delimit/commit around simple patterns?

;; Intermediate interpreted patterns:

;; extend to trees of TPs
