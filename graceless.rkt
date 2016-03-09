#lang racket

(require redex)

(provide (all-defined-out))

;; The core syntax of Graceless.
(define-language Graceless
  (e o
     (request e m e ...)
     (request m e ...)
     self)
  (M (method m (x ...) F ... e))
  (F (def x = e)
     (var x)
     (var x := e))
  (o (object M ... F ...))
  (m variable-not-otherwise-mentioned
     (variable-not-otherwise-mentioned :=))
  (x variable-not-otherwise-mentioned))

;; The runtime syntax of Graceless.
(define-extended-language G Graceless
  (e ....
     (assign e x e e)
     v
     uninitialised)
  (v (ref ℓ))
  ;; The complex contexts and the simple hole are separated here to allow
  ;; uninitialised to cascade without looping back on itself.
  (E⊥ (request E m e ...)
      (request v m v ... E e ...)
      (request m v ... E e ...)
      (assign v x E e))
  (E E⊥
     hole)
  (ℓ natural)
  (σ (Ms ...))
  (p [e σ])
  (Ms [M ...])
  (ms [m ...]))

;; Substitute the location ℓ as a reference for the locally defined self,
;; stopping at nested object expressions.
(define-metafunction G
  subst-self : ℓ e -> e
  [(subst-self ℓ self) (ref ℓ)]
  [(subst-self ℓ (request e m e_a ...))
   (request (subst-self ℓ e) m (subst-self ℓ e_a) ...)]
  [(subst-self ℓ (request m e ...)) (request m (subst-self ℓ e) ...)]
  [(subst-self ℓ (assign e_r x e_v e_n))
   (assign (subst-self ℓ e_r) x (subst-self ℓ e_v) (subst-self ℓ e_n))]
  [(subst-self _ e) e])

;; Substitute the location ℓ as the receiver to unqualified requests in the set
;; of names ms.
(define-metafunction G
  subst : ms ℓ e -> e
  [(subst [m_l ... m m_r ...] ℓ (name o (object _ ... (method m _ _ ... _) M ...
                                                F ...)))
   (subst [m_l ... m_r ...] ℓ o)]
  [(subst [m_l ... x m_r ...] ℓ (name o (object _ ... F _ ...)))
   (subst [m_l ... m_r ...] ℓ o)
   (where [x _ ...] (field-names F))]
  [(subst ms ℓ (object M ... F ...)) (object (subst-method ms ℓ M) ...
                                             (subst-field ms ℓ F) ...)]
  [(subst ms ℓ (request e m e_a ...))
   (request (subst ms ℓ e) m (subst ms ℓ e_a) ...)]
  [(subst (name ms [_ ... m _ ...]) ℓ (request m e ...))
   (subst ms ℓ (request (ref ℓ) m e ...))]
  [(subst ms ℓ (request m e ...)) (request m (subst ms ℓ e) ...)]
  [(subst ms ℓ (assign e_r x e_v e_n))
   (assign (subst ms ℓ e_r) x (subst ms ℓ e_v) (subst ms ℓ e_n))]
  [(subst _ _ e) e])

;; Continue subst through methods into their bodies, removing names which appear
;; in the parameter list.
(define-metafunction G
  subst-method : ms ℓ M -> M
  [(subst-method [m_l ... x m_r ...] ℓ
                 (name M (method m (_ ... x _ ...) _ ... _)))
   (subst-method [m_l ... m_r ...] ℓ M)]
  [(subst-method ms ℓ (method m (x ...) F ... e))
   (method m (x ...) (subst-field ms ℓ F) ... (subst ms ℓ e))])

;; Continue subst through fields into their assignments.
(define-metafunction G
  subst-field : ms ℓ F -> F
  [(subst-field ms ℓ (def x = e)) (def x = (subst ms ℓ e))]
  [(subst-field ms ℓ (var x)) (var x)]
  [(subst-field ms ℓ (var x := e)) (var x := (subst ms ℓ e))])

;; Allocate the object o in the store, returning the newly allocated location
;; and the updated store.
(define-metafunction G
  allocate : σ Ms -> [ℓ σ]
  [(allocate σ Ms) [(fresh-location σ) (store σ Ms)]])

;; Store the object o.  The resulting location is the same as calculated by
;; fresh-location on the same store, before the object is added.
(define-metafunction G
  store : σ Ms -> σ
  [(store (Ms_σ ...) Ms) (Ms_σ ... Ms)])

;; Fetch a fresh location for the store.
(define-metafunction G
  fresh-location : σ -> ℓ
  [(fresh-location σ) ,(length (term σ))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction G
  lookup : σ ℓ -> Ms
  [(lookup σ ℓ) ,(list-ref (term σ) (term ℓ))])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v. This will fail if no field named x in the object.
(define-metafunction G
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (Ms) (term (update-method ,Ms x v))))])

;; Set the method named x in the method list Ms to return the value v.  This
;; will fail if there is no field named x in the object.
(define-metafunction G
  update-method : Ms x v -> Ms
  [(update-method [M_l ... (method x () _) M_r ...] x v)
   [M_l ... (method x () v) M_r ...]])

;; Convert a field to its corresponding getter and (maybe) setter methods.
(define-metafunction G
  field-methods : F -> Ms
  [(field-methods (def x = _)) [(method x () uninitialised)]]
  [(field-methods (var x _ ...))
   [(method x () uninitialised)
    (method (x :=) (x) (assign self x (request x) (request x)))]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; methods.
(define-metafunction G
  fields-methods : [F ...] -> Ms
  [(fields-methods []) []]
  [(fields-methods [F F_r ...]) [M ... M_r ...]
   (where [M ...] (field-methods F))
   (where [M_r ...] (fields-methods [F_r ...]))])

;; Convert a field to its corresponding getter and (maybe) setter method names.
(define-metafunction G
  field-names : F -> ms
  [(field-names (def x = _)) [x]]
  [(field-names (var x _ ...)) [x (x :=)]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; method names.
(define-metafunction G
  fields-names : [F ...] -> ms
  [(fields-names []) []]
  [(fields-names [F F_r ...]) [m ... m_r ...]
   (where [m ...] (field-names F))
   (where [m_r ...] (fields-names [F_r ...]))])

;; Convert a list of fields F to a sequence of assignments to the object at
;; location ℓ, resulting in the final expression e.
(define-metafunction G
  field-assigns : ℓ [F ...] e -> e
  [(field-assigns ℓ [] e) e]
  [(field-assigns ℓ [(def x = e_v) F ...] e)
   (assign (ref ℓ) x e_v (field-assigns ℓ [F ...] e))]
  [(field-assigns ℓ [(var x) F ...] e) (field-assigns ℓ [F ...] e)]
  [(field-assigns ℓ [(var x := e_v) F ...] e)
   (assign (ref ℓ) x e_v (field-assigns ℓ [F ...] e))])

;; Ensure that the given names are unique.
(define-metafunction G
  unique : ms -> boolean
  [(unique [_ ... m _ ... m _ ...]) #f]
  [(unique [_ ...]) #t])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   G
   #:domain p
   ;; Uninitialised terminates the program.
   (--> [(in-hole E⊥ uninitialised) σ]
        [uninitialised σ]
        uninitialised)
   ;; Allocate the object o substituting local requests to this object, and
   ;; return the resulting reference.
   (--> [(in-hole E (object (name M (method m _ _ ... _)) ... F ...))
         σ]
        [(in-hole E (subst [m ... m_f ...] ℓ
                           (subst-self ℓ
                                       (field-assigns ℓ [F ...] (ref ℓ)))))
         σ_p]
        (where ℓ (fresh-location σ))
        (where [m_f ...] (fields-names [F ...]))
        (where [M_f ...] (fields-methods [F ...]))
        (where (M_p ...) (M ... M_f ...))
        (where σ_p (store σ [(subst-method [m ... m_f ...] ℓ M_p) ...]))
        (side-condition (term (unique [m ... m_f ...])))
        object)
   ;; Optimisation for requests which introduce no local variables.
   (--> [(in-hole E (request (ref ℓ) m)) σ]
        [(in-hole E (subst-self ℓ e)) σ]
        (where [_ ... (method m () e) _ ...] (lookup σ ℓ))
        simple-request)
   ;; Allocate an object with getter methods to the parameters whose bodies are
   ;; the arguments, and substitute for unqualified requests to the parameters
   ;; and for self.  Return the body of the method.
   (--> [(in-hole E (request (ref ℓ) m v ..._a)) σ]
        [(in-hole E (subst [x_p ... m_f ...] ℓ_a
                           (subst-self ℓ
                                       (field-assigns ℓ_a [F ...] e))))
         σ_p]
        (where [_ ... (method m (x_p ..._a) F ... e) _ ...]
               (lookup σ ℓ))
        (where [m_f ...] (fields-names [F ...]))
        (where [M_f ...] (fields-methods [F ...]))
        (where [ℓ_a σ_p] (allocate σ [(method x_p () v) ... M_f ...]))
        (side-condition (term (unique [x_p ... m_f ...])))
        ;; Don't apply this rule if the optimisation above applies.
        (side-condition (or (> (length (term (x_p ...))) 0)
                            (> (length (term (F ...))) 0)))
        request)
   ;; Set the field in the object and return the following expression.
   (--> [(in-hole E (assign (ref ℓ) x v e)) σ]
        [(in-hole E e) σ_p]
        (where σ_p (set-field σ ℓ x v))
        assign)))

;; Wrap a term t into an initial program with an empty store.
(define (program t) (term [,t ()]))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Evaluate an expression starting with an empty store.
(define-metafunction G
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->G until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction G
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->G (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error.
(define (eval-->G t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->G t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->G t) (traces -->G (program t)))

;; Test if expressions can cause a Racket error.
(redex-check Graceless e (eval-->G (term e)))
