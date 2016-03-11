#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with merged identity
;; inheritance.
(define -->GU
  (extend-reduction-relation
   -->GI
   GI
   #:domain p
   ;; Object literals are permitted to process their inherits clauses under
   ;; uniform identity.
   (--> [(in-hole EI o) σ]
        [(in-hole EI o) σ_p]
        (where ([o σ_p]) ,(apply-reduction-relation -->GU (term [o σ]))))
   ;; Concatenate the new definitions into the inherited object's store
   ;; location (removing overrides), and return the inheriting object's body.
   (--> [(in-hole E (name o (object (s_d ... inherits
                                     (name o_i (object M_i ... F_i ...)))
                                    M ... F ...))) σ]
        ;; Concatenate the inherited methods into the object constructor, and
        ;; perform the substitutions into the body of the inheriting object.
        [(in-hole E (object M_s ...
                            (subst-method [ℓ_s super] s ... M) ...
                            ;; The ordering here is important, as the inherited
                            ;; fields must be evaluated first.
                            F_i ...
                            (subst-field [ℓ_s super] s ... F) ...))
         ;; Store the new super object in the store. Assignments should remain
         ;; bound to the new object in super calls.
         (store σ ,(append (term [(subst-self-assign ℓ_s M_i) ...])
                           (term [(subst-self-assign ℓ_s M_f) ...])))]
        ;; Collect the generated getters and setters of the fields.
        (where [M_f ...] (field-methods F_i ...))
        ;; We have to allocate a super object to deal with super calls.
        (where ℓ_s (fresh-location σ))
        ;; Collect the names of the methods in both objects.
        (where (m ...) (object-names o))
        (where (m_i ...) (object-names o_i))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object, and then forward to the super
        ;; object as self.
        (where [M_s ...] ,(map (λ (M) (term (forward-request-to ℓ_s ,M)))
                               (append (term (override M_i ... M_f ...
                                                       m ...)))))
        ;; Because we are merging with the existing object, we need to apply
        ;; these substitutions directly to the methods which will be added into
        ;; the store.  So, we need to remove the names in the object from the
        ;; delayed substitutions, as the resulting methods will appear in the
        ;; object and shadow them.
        (where (s ...) (remove-all-shadows s_d ... m_i ... m ...))
        ;; The methods of the inheriting object must be unique.
        (side-condition (term (unique m ...)))
        inherits)))

;; Progress the program p by one step with the reduction relation -->GU.
(define (step-->GU p) (apply-reduction-relation -->GU p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GI
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->GU until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GI
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GU (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error.
(define (eval-->GU t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GU t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GU.
(define (traces-->GU t) (traces -->GU (program t)))
