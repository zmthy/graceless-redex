#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with uniform identity
;; positional multiple inheritance.
(define -->GU
  (extend-reduction-relation
   -->GPF
   GI
   #:domain p
   ;; Concatenate the body of the inherited objects into the inheriting object's
   ;; store, removing overrides, and update the following expression.
   (--> [σ (in-hole E ((i ... inherits (object s_u ... M ... S ...) as x s ...)
                       e ...))]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and field accessors.
        [(update (store σ (object M_u ... M_f ...))
                 M_u ... M_f ... i_p ...)
         (in-hole E (seq (subst s_u ...
                                [ℓ_d / (self 0)]
                                [(ℓ M ... M_f ... s_u ...) i_p ... / super]
                                [(self 0) / m ...] e_u) ...
                         (subst s ...
                                [i_p ... / super]
                                [(self 0) / m ...]
                                [ℓ as ℓ_d / x] e) ...))]
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; Collect the names of the definitions in the inherited object.
        (where (m ...) (names M ... S ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        ;; Qualify local requests to this object in the super-methods, and
        ;; perform the delayed substitutions.
        (where (M_u ...) ((subst-method s_u ... [(self 0) / m ...] M) ...))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S ...)))
        ;; Collect the field accessor methods and the resulting object body.
        (where (M_f ... e_u ...) (body [S y] ...))
        ;; Fetch the actual self value from the bottom of the inherits contexts.
        (where ℓ_d ,(first (last (term (i ...)))))
        ;; Include the new super alias in the top of the inherits context.
        (where (i_p ...) (add-substitution [ℓ as ℓ_d / x] i ...))
        inherits/positional)))

;; Progress the program p by one step with the reduction relation -->GU.
(define (step-->GU p) (apply-reduction-relation -->GU p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GU until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GU (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error.
(define (eval-->GU t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GU t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GU.
(define (traces-->GU t) (traces -->GU (program t)))
