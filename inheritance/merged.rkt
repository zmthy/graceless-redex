#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Add the methods M to the object at location ℓ in the store σ.
(define-metafunction GI
  set-methods : σ ℓ [M ...] -> σ
  [(set-methods σ ℓ [M ...]) ,(list-set (term σ) (term ℓ) (term [M ...]))])

;; Substitute a self reference as the receiver of an assignment to a field with
;; a reference to the location l in the method M.
(define-metafunction GI
  subst-self-assign : ℓ M -> M
  [(subst-self-assign ℓ (method m (x_p) (assign self x_f e done)))
   (method m (x_p) (assign (ref ℓ) x_f e done))]
  [(subst-self-assign _ M) M])

;; Small-step dynamic semantics of Graceless extended with merged identity
;; inheritance.
(define -->GM
  (extend-reduction-relation
   -->GI
   GI
   #:domain p
   ;; Object literals are permitted to transform into refs in inherits clauses
   ;; under merged identity.
   (--> [(in-hole EI o) σ]
        [(in-hole EI e) σ_p]
        (where ([e σ_p]) ,(apply-reduction-relation -->GM (term [o σ]))))
   ;; Concatenate the new definitions into the inherited object's store
   ;; location (removing overrides), and return the inheriting object's body.
   (--> [(in-hole E (object (s_d ... inherits (ref ℓ))
                            (name M (method m _ _)) ... F ...)) σ]
        ;; The super reference is now the self reference.  Substitutions are the
        ;; inherited and local methods for self/super, and the (shadowed)
        ;; delayed substitutions on the inherits clause.
        [(in-hole E (subst [ℓ_s super] [ℓ self] [ℓ m_i ... m ... m_f ...] s ...
                           (field-assigns ℓ F ... (ref ℓ))))
         ;; Add the new methods into the old location in the store.
         (set-methods σ_s ℓ ,(append (term [M_s ...])
                                     (term [(subst-method s ... M) ...])
                                     (term (field-methods F ...))))]
        ;; Lookup the super object, fetching both its methods and method names.
        (where [(name M_i (method m_i _ _)) ...] (lookup σ ℓ))
        ;; We have to allocate a copy of the inherited object, so it can be used
        ;; as a super-reference.
        (where ℓ_s (fresh-location σ))
        ;; Store the new super object in the store.  Assignments should remain
        ;; bound to the new object in self calls.
        (where σ_s (store σ [(subst-self-assign ℓ_s M_i) ...]))
        ;; Collect the names of the fields in the inheriting object.
        (where (m_f ...) (field-names F ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object, and then forward to the super
        ;; object as self.
        (where [M_s ...] ,(map (λ (M) (term (forward-request-to ℓ_s ,M)))
                               (term (override M_i ... m ... m_f ...))))
        ;; Because we are merging with the existing object, we need to apply
        ;; these substitutions directly to the methods which will be added into
        ;; the store.  So, we need to remove the names in the object from the
        ;; delayed substitutions, as the resulting methods will appear in the
        ;; object and shadow them.
        (where (s ...) (remove-all-shadows s_d ... m ... m_f ...))
        ;; Apply the substitutions to the inheriting object's methods.  It's not
        ;; necessary to apply it to the fields, because their values will not be
        ;; in the generated methods but in the assigns of the object body.
        (where [M_p ...] [(subst-method s ... M) ...])
        ;; The methods of the inheriting object must be unique.
        (side-condition (term (unique m ... m_f ...)))
        inherits)))

;; Progress the program p by one step with the reduction relation -->GM.
(define (step-->GM p) (apply-reduction-relation -->GM p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GI
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->GM until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GI
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GM (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GM,
;; returning the resulting object, stuck program, or error.
(define (eval-->GM t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GM,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GM t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GM.
(define (traces-->GM t) (traces -->GM (program t)))
