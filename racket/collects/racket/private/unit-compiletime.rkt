#lang racket/base

(require syntax/boundmap
         syntax/parse
         syntax/datum
         "unit-syntax.rkt")
(require (for-syntax racket/base))
(require (for-template racket/base
                       "unit-keywords.rkt"
                       "unit-runtime.rkt"))

(provide (struct-out var-info)
         (struct-out signature)
         (struct-out signature-form)
         (struct-out unit-info)
         (struct-out link-record)

         (rename-out [build-siginfo make-siginfo])
         siginfo-names siginfo-ctime-ids siginfo-rtime-ids siginfo-subtype
         unprocess-link-record-bind unprocess-link-record-use
         set!-trans-extract
         process-tagged-import process-tagged-export
         lookup-signature lookup-def-unit make-id-mapper make-id-mappers sig-names sig-int-names sig-ext-names
         map-sig split-requires split-requires* apply-mac complete-exports complete-imports check-duplicate-subs
         process-spec
         make-relative-introducer
         build-init-depend-property)

(begin
  (provide tagged-sig-spec
           sig-spec
           init-depends-decl
           sig-id
           tagged-sig-id)

  ;; ----------------------------------------
  ;; from docs for `unit`:

  (define-syntax-class tagged-sig-spec
    #:attributes ()
    #:literals (tag)
    (pattern :sig-spec)
    (pattern (tag tagname:id spec:sig-spec)))

  (define-syntax-class sig-spec
    #:attributes (sig) ;; Signature, result of `process-spec`
    #:description #f
    (pattern inner:inner-sig-spec
             #:attr sig ((datum inner.make-sig) #'inner (box #f) #t values)))

  (define-syntax-class inner-sig-spec
    #:attributes (make-sig) ;; Syntax (Box ??) Boolean ?? -> Signature
    #:description "sig-spec"
    #:literals (prefix rename only except bind-at)
    (pattern name:sig-id
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               (do-identifier* #'name (datum name.sig)
                               (or spec-bind #'name) res bind? add-prefix)))
    (pattern (prefix pfx:id spec:inner-sig-spec)
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               ((datum spec.make-sig) spec-bind res bind?
                                      (λ (id) (add-prefix (do-prefix id #'pfx))))))
    (pattern (rename spec:inner-sig-spec [internal:id external:id] ...)
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               (define sig-res
                 (do-rename ((datum spec.make-sig) spec-bind res bind? add-prefix)
                            #'(internal ...)
                            (datum->syntax #f (add-prefixes add-prefix #'(external ...)))))
               (define dup (check-duplicate-identifier (sig-int-names sig-res)))
               (when dup
                 (raise-stx-err (format "rename created duplicate identifier ~a" (syntax-e dup))
                                this-syntax))
               sig-res))
    (pattern (only spec:inner-sig-spec only-name:id ...)
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               (do-only/except ((datum spec.make-sig) spec-bind res bind? add-prefix)
                               (add-prefixes add-prefix #'(only-name ...))
                               (lambda (id) id)
                               (lambda (id) (car (generate-temporaries (list id)))))))
    (pattern (except spec:inner-sig-spec except-name:id ...)
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               (do-only/except ((datum spec.make-sig) spec-bind res bind? add-prefix)
                               (add-prefixes add-prefix #'(except-name ...))
                               (lambda (id) (car (generate-temporaries (list id))))
                               (lambda (id) id))))
    ;; internal?
    (pattern (bind-at lctx spec:inner-sig-spec)
             #:attr make-sig
             (λ (spec-bind res bind? add-prefix)
               ((datum spec.make-sig) #'lctx res bind? add-prefix))))

  (define-splicing-syntax-class init-depends-decl
    #:attributes ()
    #:literals (init-depend)
    (pattern (~seq (init-depend dep:tagged-sig-id ...)))
    (pattern (~seq)))

  (define-syntax-class sig-id
    #:attributes (sig) ;; Signature
    #:opaque #:description "signature-id"
    (pattern (~var name (static (lift/maybe-set!-trans signature?) "signature-id"))
             #:attr sig ((lift/maybe-set!-trans values) (datum name.value))))

  (define-syntax-class tagged-sig-id
    #:attributes ()
    #:literals (tag)
    (pattern name:sig-id)
    (pattern (tag tagname:id name:sig-id)))

  (provide lift/maybe-set!-trans)
  (define ((lift/maybe-set!-trans f) v)
    (if (set!-transformer? v) (f (set!-transformer-procedure v)) (f v)))

  ;; ----------------------------------------
  ;; from docs for `compound-unit`:
  (provide link-binding
           tagged-link-id
           linkage-decl)

  (define-syntax-class link-binding
    #:attributes ()
    (pattern (name:id (~datum :) sig:tagged-sig-id)))

  (define-syntax-class tagged-link-id
    #:attributes ()
    #:literals (tag)
    (pattern (tag tagname:id linkname:id))
    (pattern (tag linkname:id)))

  (define-syntax-class linkage-decl
    #:attributes ()
    (pattern ((bind:link-binding ...) unit-expr:expr link:tagged-link-id ...)))

  ;; ----------------------------------------
  ;; from docs for `compound-unit/infer`:
  (provide tagged-infer-link-import
           tagged-infer-link-export
           infer-link-export
           infer-linkage-decl
           unit-id)

  (define-syntax-class tagged-infer-link-import
    #:attributes ()
    (pattern sig:tagged-sig-id)
    (pattern (link (~datum :) sig:tagged-sig-id)))

  (define-syntax-class tagged-infer-link-export
    #:attributes ()
    #:literals (tag)
    (pattern (tag tagname:id export:infer-link-export))
    (pattern export:infer-link-export))

  (define-syntax-class infer-link-export
    #:attributes ()
    (pattern (~and signame:sig-id ~!))
    (pattern linkname:id))

  (define-syntax-class infer-linkage-decl
    #:attributes ()
    (pattern ((bind:link-binding ...) unitname:unit-id link:tagged-link-id ...))
    (pattern unitname:unit-id))

  (define-syntax-class unit-id
    #:attributes ()
    (pattern (~var name (static (lift/maybe-set!-trans unit-info?) "unit"))))

  (begin))

;; XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

(define-syntax (apply-mac stx)
  (syntax-case stx ()
    ((_ f x) ((syntax-e #'f) #'x))))

;; split-requires* : (listof identifier) -> (listof syntax) -> (values (listof syntax) (listof syntax))
;; Parameterized over identifiers for require forms.
(define ((split-requires* req-forms) l)
  (let loop ((l l)
             (requires null))
    (cond
      ((null? l) (cons (reverse requires) l))
      (else
       (syntax-case (car l) ()
         ((r . x)
          (ormap (lambda (req) (free-identifier=? #'r req))
                 req-forms)
          (loop (cdr l) (cons (car l) requires)))
         (_
          (cons (reverse requires) l)))))))

;; split-requires : (listof syntax) -> (values (listof syntax) (listof syntax))
;; Recognizes mzscheme require forms.
(define split-requires
  (split-requires*
   (list #'require #'require-for-syntax #'require-for-template)))

;; (make-var-info bool bool identifier (U #f syntax-object))
(define-struct var-info (syntax? [exported? #:mutable] id [ctc #:mutable]))

(define-syntax define-struct/proc
  (syntax-rules ()
    ((_ name (field ...) p)
     (define-struct name (field ...) #:property prop:procedure p))))

;; An int/ext is
;; - (cons identifier identifier)
;; A def is
;; - (listof (cons (listof int/ext) syntax-object))
;; A ctc is
;; - syntax-object
;; - #f
;; A sig is
;; - (list (listof int/ext) (listof def) (listof def) (listof ctc))
;; A tagged-sig is 
;; - (listof (cons #f siginfo) (cons #f identifier) sig)
;; - (listof (cons symbol siginfo) (cons symbol identifier) sig)

;; A siginfo is
;; - (make-siginfo (listof symbol) (listof symbol) (listof identifier) (hash-tableof symbol bool))
;; where the car of each list represents the signature, and the cdr represents
;; its super signatures.  All lists are non-empty and the same length.
(define-struct siginfo (names ctime-ids rtime-ids super-table))

;; build-siginfo : (listof symbol) (listof symbol) (listof identifier) -> siginfo
(define (build-siginfo names rtime-ids)
  (define ctime-ids 
    (cons (gensym)
          (if (null? (cdr names))
              null
              (siginfo-ctime-ids 
               (signature-siginfo
                (lookup-signature (cadr names)))))))
  (make-siginfo names
                ctime-ids
                rtime-ids 
                (make-immutable-hasheq (map (λ (x) `(,x . #t)) ctime-ids))))

;; siginfo-subtype : siginfo siginfo -> bool
(define (siginfo-subtype s1 s2)
  (hash-ref (siginfo-super-table s1)
            (car (siginfo-ctime-ids s2))
            (λ () #f)))


;; A signature is 
;; (make-signature siginfo
;;                 (listof identifier)
;;                 (listof (cons (listof identifier) syntax-object))
;;                 (listof (cons (listof identifier) syntax-object))
;;                 (listof (cons (listof identifier) syntax-object))
;;                 (listof (U syntax-object #f))
;;                 identifier)
(define-struct/proc signature (siginfo vars val-defs stx-defs post-val-defs ctcs orig-binder)
  (lambda (_ stx)
    (parameterize ((error-syntax stx))
      (raise-stx-err "illegal use of signature name"))))

;; (make-signature-form (syntax-object -> any))
(define-struct/proc signature-form (f)
  (lambda (_ stx)
    (parameterize ((error-syntax stx))
      (raise-stx-err "illegal use of signature form"))))

;; (make-unit-info identifier (listof (cons symbol identifier)) (listof (cons symbol identifier)) identifier boolean)
(define-struct/proc unit-info (unit-id import-sig-ids export-sig-ids deps orig-binder contracted?)
  (lambda (struct stx) 
    (with-syntax ((u (syntax-local-introduce (unit-info-unit-id struct))))
      (syntax-case stx (set!)
        ((set! x y)
         (if (unit-info-contracted? struct)
             (raise-syntax-error 'set!
                                 "cannot set! a contracted unit"
                                 stx
                                 (syntax x))
             #`(begin 
                 #,(syntax/loc #'y (check-unit y 'set!))
                 #,(syntax/loc #'y (check-sigs y (unit-import-sigs u) (unit-export-sigs u) 'set!))
                 (set! u y))))
        ((_ . y)
         (syntax/loc stx (u . y)))
        (x
         (identifier? #'x)
         (quasisyntax/loc stx (values u))))))) ;; The apparently superfluous values is so the certificates aren't
;; too permissive

(define (lookup id err-msg)
  (check-id id)
  (let ((s (set!-trans-extract
            (syntax-local-value
             (syntax-local-introduce id)
             (lambda ()
               (raise-stx-err err-msg id))))))
    s))

;; lookup-signature : syntax-object -> signature
(define (lookup-signature id)
  (let ((s (lookup id "unknown signature")))
    (unless (signature? s)
      (raise-stx-err "not a signature" id))
    s))

(define (set!-trans-extract x)
  (if (set!-transformer? x)
      (set!-transformer-procedure x)
      x))

(define (lookup-def-unit id)
  (let ((u (lookup id "unknown unit definition")))
    (unless (unit-info? u)
      (raise-stx-err "not a unit definition" id))
    u))

;; check-bound-id-subset : (listof syntax-object) (listof identifier) syntax-object -> 
;; ensures each element of i1 is an identifier bound-identifier=? to an identifier in i2
(define (check-bound-id-subset i1 i2)
  (let ((ht (make-bound-identifier-mapping)))
    (for-each (lambda (id)
                (bound-identifier-mapping-put! ht id #t))
              i2)
    (for-each
     (lambda (id)
       (check-id id)
       (unless (bound-identifier-mapping-get ht id (lambda () #f))
         (raise-stx-err "listed identifier not present in signature specification" id)))
     i1)))

;; do-rename : sig syntax-object syntax-object -> sig
;; internals and externals must both be of the form (x ...)
;; ensures that each x above is an identifier
(define (do-rename sig internals externals)
  (check-bound-id-subset (syntax->list externals)
                         (sig-int-names sig))
  (let ((ht (make-bound-identifier-mapping)))
    (for-each
     (lambda (int ext)
       (check-id int)
       (when (bound-identifier-mapping-get ht ext (lambda () #f))
         (raise-stx-err "duplicate renamings" ext))
       (bound-identifier-mapping-put! ht ext int))
     (syntax->list internals)
     (syntax->list externals))
    (map-sig
     (lambda (id)
       (bound-identifier-mapping-get ht id (lambda () id)))
     (lambda (x) x)
     sig)))

;; do-prefix : id id -> id
;; ensures that pid is an identifier
(define (do-prefix stx pid)
  (if (identifier? stx)
      (datum->syntax
       stx
       (string->symbol (format "~a~a" (syntax-e pid) (syntax-e stx)))
       stx)
      stx))

;; do-only/except : sig (listof identifier) -> sig
;; ensures that only-ids are identifiers and are mentioned in the signature
(define (do-only/except sig only/except-ids put get)
  (check-bound-id-subset only/except-ids
                         (sig-int-names sig))
  (let ((ht (make-bound-identifier-mapping)))
    (for-each (lambda (id)
                (bound-identifier-mapping-put! ht id (put id)))
              only/except-ids)
    (map-sig
     (lambda (id)
       (bound-identifier-mapping-get ht id
                                     (lambda () 
                                       (get id))))
     (lambda (x) x)
     sig)))

(define (make-relative-introducer ref-id orig-id)
  (lambda (id)
    ((make-syntax-delta-introducer id orig-id)
     (datum->syntax ref-id
                    (syntax-e id)
                    id
                    id))))

;; do-identifier : identifier syntax (box (cons identifier siginfo)) -> sig
(define (do-identifier spec spec-bind res bind? add-prefix)
  (let* ((sig (lookup-signature spec)))
    (do-identifier* spec sig spec-bind res bind? add-prefix)))

;; do-identifier* : identifier sig syntax (box (cons identifier siginfo)) -> sig
(define (do-identifier* spec sig spec-bind res bind? add-prefix)
  (let* ((vars (signature-vars sig))
         (vals (signature-val-defs sig))
         (stxs (signature-stx-defs sig))
         (p-vals (signature-post-val-defs sig))
         (ctcs  (signature-ctcs sig))
         (delta-introduce (if bind?
                              (make-relative-introducer spec-bind
                                                        (car (siginfo-names (signature-siginfo sig))))
                              (lambda (id)
                                (syntax-local-introduce id)))))
    (set-box! res (cons spec (signature-siginfo sig)))
    (map-sig (lambda (id)
               (add-prefix
                (delta-introduce id)))
             syntax-local-introduce
             (list (map cons vars vars)
                   (map 
                    (λ (val)
                      (cons (map (λ (id) (cons id id))
                                 (car val))
                            (cdr val)))
                    vals)
                   (map 
                    (λ (stx)
                      (cons (map (λ (id) (cons id id))
                                 (car stx))
                            (cdr stx)))
                    stxs)
                   ctcs
                   p-vals))))

(define (sig-names sig)
  (append (car sig)
          (apply append (map car (cadr sig)))
          (apply append (map car (caddr sig)))))


(define (sig-int-names sig)
  (map car (sig-names sig)))

(define (sig-ext-names sig)
  (map cdr (sig-names sig)))

;; map-def : (identifier -> identifier) (syntax-object -> syntax-object) def -> def
(define (map-def f g def)
  (cons (map (lambda (x)
               (cons (f (car x)) (g (cdr x))))
             (car def))
        (g (cdr def))))

;; map-ctc : (identifier -> identifier) (syntax-object -> syntax-object) ctc -> ctc
(define (map-ctc f g ctc)
  (if ctc
      (g ctc)
      ctc))

;; map-sig : (identifier -> identifier) (sytnax-object -> syntax-object)  sig -> sig
;; applies f to the internal parts, and g to the external parts.
(define (map-sig f g sig)
  (list (map (lambda (x) (cons (f (car x)) (g (cdr x)))) (car sig))
        (map (lambda (x) (map-def f g x)) (cadr sig))
        (map (lambda (x) (map-def f g x)) (caddr sig))
        (map (lambda (x) (map-ctc f g x)) (cadddr sig))
        (map (lambda (x) (cons (map f (car x))
                               (g (cdr x))))
             (list-ref sig 4))))

;; An import-spec is one of
;; - signature-name
;; - (only import-spec identifier ...)
;; - (except import-spec identifier ...)
;; - (prefix prefix-identifier import-spec)
;; - (rename import-spec (local-identifier signature-identifier) ...)  

;; An export-spec is one of
;; - signature-name
;; - (prefix prefix-identifier export-spec)
;; - (rename export-spec (local-identifier signature-identifier) ...)

;; A tagged-import-spec is one of
;; - import-spec
;; - (tag symbol import-spec)
;; - (bind-at id tagged-import-spec)

;; A tagged-export-spec is one of
;; - export-spec
;; - (tag symbol export-spec)
;; - (bind-at id tagged-export-spec)

;; process-tagged-import/export : syntax-object boolean -> tagged-sig
(define (process-tagged-import/export spec import? bind?)
  (define res (box #f))
  (let loop ([spec spec] [spec-bind #f])
    (syntax-case spec (bind-at)
      ((bind-at id spec)
       (loop #'spec #'id))
      (_
       (begin
         (check-tagged-spec-syntax spec import? identifier?)
         (syntax-case spec (tag)
           ((tag sym spec)
            (let ([s (process-import/export #'spec spec-bind res bind? values)])
              (list (cons (syntax-e #'sym) (cdr (unbox res)))
                    (cons (syntax-e #'sym) (car (unbox res)))
                    s)))
           ((tag . _)
            (raise-stx-err "expected (tag symbol <import/export-spec>)" spec))
           (_ (let ([s (process-import/export spec spec-bind res bind? values)])
                (list (cons #f (cdr (unbox res)))
                      (cons #f (car (unbox res)))
                      s)))))))))

(define (add-prefixes add-prefix l)
  (map add-prefix (syntax->list l)))

;; process-import/export : syntax-object syntax-object (box (cons identifier) siginfo) -> sig
(define (process-import/export spec spec-bind res bind? add-prefix)
  (syntax-case spec (only except prefix rename bind-at)
    (_
     (identifier? spec)
     (do-identifier spec (or spec-bind spec) res bind? add-prefix))
    ((bind-at spec-bind spec)
     (process-import/export #'spec #'spec-bind res bind? add-prefix))
    ((only sub-spec id ...)
     (do-only/except (process-import/export #'sub-spec spec-bind res bind? add-prefix)
                     (add-prefixes add-prefix #'(id ...))
                     (lambda (id) id)
                     (lambda (id)
                       (car (generate-temporaries #`(#,id))))))
    ((except sub-spec id ...)
     (do-only/except (process-import/export #'sub-spec spec-bind res bind? add-prefix)
                     (add-prefixes add-prefix #'(id ...))
                     (lambda (id)
                       (car (generate-temporaries #`(#,id))))
                     (lambda (id) id)))
    ((prefix pid sub-spec)
     (process-import/export #'sub-spec spec-bind res bind?
                            (lambda (id)
                              (add-prefix (do-prefix id #'pid)))))
    ((rename sub-spec (internal external) ...)
     (let* ((sig-res
             (do-rename (process-import/export #'sub-spec spec-bind res bind? add-prefix)
                        #'(internal ...)
                        (datum->syntax #f (add-prefixes add-prefix #'(external ...)))))
            (dup (check-duplicate-identifier (sig-int-names sig-res))))
       (when dup
         (raise-stx-err
          (format "rename created duplicate identifier ~a" (syntax-e dup))
          spec))
       sig-res))))

(define (process-tagged-import spec)
  (process-tagged-import/export spec #t #t))
(define (process-tagged-export spec)
  (process-tagged-import/export spec #f #t))

;; process-spec : syntax-object -> sig
(define (process-spec spec)
  (check-tagged-spec-syntax spec #f identifier?)
  (process-import/export spec spec (box #f) #t values))


;  ;; extract-siginfo : (union import-spec export-spec) -> ???
;  ;; extracts the identifier that refers to the signature
;  (define (extract-siginfo spec)
;    (syntax-case spec (only except prefix rename)
;      ((only sub-spec . x)
;       (extract-siginfo #'sub-spec))
;      ((except sub-spec . x)
;       (extract-siginfo #'sub-spec))
;      ((prefix pid sub-spec)
;       (extract-siginfo #'sub-spec))
;      ((rename sub-spec . x)
;       (extract-siginfo #'sub-spec))
;      (_ spec)))



;; check-duplicate-subs : (listof (cons symbol siginfo)) (listof syntax-object) ->
(define (check-duplicate-subs tagged-siginfos sources)
  (for-each
   (λ (tinfo1 s1)
     (for-each 
      (λ (tinfo2 s2)
        (unless (eq? tinfo1 tinfo2)
          (when (and (eq? (car tinfo1) (car tinfo2))
                     (siginfo-subtype (cdr tinfo1) (cdr tinfo2)))
            (raise-stx-err (format "the signature of ~a extends this signature"
                                   (syntax->datum s1))
                           s2))))
      tagged-siginfos
      sources))
   tagged-siginfos
   sources))


;; A link-record is
;; (make-link-record (or symbol #f) (or identifier #f) identifier siginfo)
(define-struct link-record (tag linkid sigid siginfo))

;; complete-exports : (listof link-record) (listof link-record) -> (listof link-record)
;; The export-bindings should not contain two bindings that are related as subsignatures.
(define (complete-exports unit-exports given-bindings)
  (define binding-table (make-hash))
  (define used-binding-table (make-hash))
  
  (check-duplicate-subs 
   (map (λ (ts) (cons (link-record-tag ts) (link-record-siginfo ts))) given-bindings)
   (map link-record-sigid given-bindings))
  
  (for-each 
   (λ (b)
     (hash-set! binding-table 
                (cons (link-record-tag b)
                      (car (siginfo-ctime-ids (link-record-siginfo b))))
                (link-record-linkid b)))
   given-bindings)
  
  (begin0
    (map
     (λ (export)
       (define r
         (ormap 
          (λ (ctime-id)
            (define key (cons (link-record-tag export) ctime-id))
            (define used (hash-ref used-binding-table key (λ () #f)))
            (when used
              (raise-stx-err "this export is supplied multiple times by the given unit" used))
            (let ([r (hash-ref binding-table key (λ () #f))])
              (when r
                (hash-set! used-binding-table key r))
              r))
          (siginfo-ctime-ids (link-record-siginfo export))))
       (make-link-record
        (link-record-tag export)
        (cond
          [r r]
          [else (car (generate-temporaries (list (link-record-linkid export))))])
        (link-record-sigid export)
        (link-record-siginfo export)))
     unit-exports)
    
    (hash-for-each
     binding-table
     (λ (k v)
       (unless (hash-ref used-binding-table k (λ () #f))
         (raise-stx-err "this export is not supplied by the given unit" v))))))

(define (name-form n) (syntax->datum n))

;; complete-imports : (hash-tableof symbol (or identifier 'duplicate))
;;                    (listof link-record)
;;                    (listof (list symbol identifier siginfo)) ->
;;                    (listof (cons symbol identifier))
(define (complete-imports sig-table given-links unit-imports src)
  (define linked-sigs-table (make-hash))
  (for-each
   (λ (link)
     (define tag (link-record-tag link))
     (for-each
      (λ (cid)
        (define there? (hash-ref linked-sigs-table (cons tag cid) (λ () #f)))
        (hash-set! linked-sigs-table (cons tag cid) (if there? 'duplicate #t)))
      (siginfo-ctime-ids (link-record-siginfo link))))
   given-links)
  
  (append
   given-links
   (let loop ([unit-imports unit-imports])
     (cond
       [(null? unit-imports) null]
       [else
        (let* ([import (car unit-imports)]
               [ctime-ids (siginfo-ctime-ids (link-record-siginfo import))]
               [tag (link-record-tag import)]
               [there?
                (hash-ref linked-sigs-table
                          (cons tag (car ctime-ids))
                          (λ () #f))])
          (cond
            [(eq? 'duplicate there?)
             (raise-stx-err
              (if tag
                  (format "specified linkages satisfy (tag ~a ~a) import multiple times"
                          tag (name-form (car (siginfo-names (link-record-siginfo import)))))
                  (format "specified linkages satisfy untagged ~a import multiple times"
                          (name-form (car (siginfo-names (link-record-siginfo import))))))
              src)]
            [there?
             (loop (cdr unit-imports))]
            [else
             (let ([there?2 (hash-ref sig-table
                                      (car ctime-ids)
                                      (λ () #f))])
               (cond
                 [(eq? 'duplicate there?2)
                  (raise-stx-err 
                   (if tag
                       (format "multiple linkages satisfy (tag ~a ~a) import"
                               tag (name-form (car (siginfo-names (link-record-siginfo import)))))
                       (format "multiple linkages satisfy untagged ~a import"
                               (name-form (car (siginfo-names (link-record-siginfo import))))))
                   src)]
                 [there?2
                  (for-each
                   (λ (cid)
                     (hash-set! linked-sigs-table
                                (cons tag cid)
                                #t))
                   ctime-ids)
                  (cons (make-link-record (link-record-tag import)
                                          there?2
                                          (link-record-sigid import)
                                          (link-record-siginfo import))
                        (loop (cdr unit-imports)))]
                 [else
                  (raise-stx-err
                   (if tag
                       (format "no linkages satisfy (tag ~a ~a) import"
                               tag (name-form (car (siginfo-names (link-record-siginfo import)))))
                       (format "no linkages satisfy untagged ~a import"
                               (name-form (car (siginfo-names (link-record-siginfo import))))))
                   src)]))]))]))))

(define (unprocess-link-record-bind lr)
  (if (link-record-tag lr)
      #`(#,(link-record-linkid lr) : (tag #,(link-record-tag lr) #,(link-record-sigid lr)))
      #`(#,(link-record-linkid lr) : #,(link-record-sigid lr))))

(define (unprocess-link-record-use lr)
  (if (link-record-tag lr)
      #`(tag #,(link-record-tag lr) #,(link-record-linkid lr))
      (link-record-linkid lr)))

(define (make-id-mappers . make-unbox-stxes)
  (apply values (map make-id-mapper make-unbox-stxes)))

(define (make-id-mapper make-unbox-stx)
  (make-set!-transformer
   (lambda (sstx)
     (syntax-case sstx (set!)
       [x
        (identifier? #'x) 
        (make-unbox-stx sstx)]
       [(set! . x)
        (raise-syntax-error
         'unit
         "cannot set! imported or exported variables"
         sstx)]
       [(_ . x)
        (datum->syntax
         sstx
         (cons (make-unbox-stx sstx) #'x)
         sstx)]))))

;; This utility function returns a list of natural numbers for use as a syntax
;; property needed to support units in Typed Racket
;; Each number in the list is an index into a unit's list of imports signifying
;; that the import at that index is also an init-dependency of the unit
(define (build-init-depend-property init-depends imports)
  (define (sig=? s1 s2)
    (and (eq? (syntax-e (car s1)) (car s2))
         (free-identifier=? (cdr s1) (cdr s2))))
  (for/list ([import (in-list imports)]
             [index (in-naturals)]
             #:when (member import init-depends sig=?))
    index))
