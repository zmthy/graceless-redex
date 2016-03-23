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
   -->GPF
   GI
   #:domain p
   ;; Concatenate the body of the inherited object into the inheriting object's
   ;; body, removing overrides.
   (--> [σ (in-hole E (object (inherits (object M ... S ...) s_d ...)
                              M_d ... S_d ...))]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and field accessors.
        [(store σ (object M_u ... M_f ...))
         (in-hole E (object M_up ...
                            (subst-method s ...
                                          [ℓ as (self 0) / (super 0)] M_d) ...
                            (subst [(self 0) / m ...] e) ...
                            (subst-stmt s ...
                                        [ℓ as (self 0) / (super 0)] S_d) ...))]
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; Collect the names of the definitions in the inherited object.
        (where (m ...) (names M ... S ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        ;; Qualify local requests to this object in the super-methods.
        (where (M_u ...) ((subst-method [(self 0) / m ...] M) ...))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S ...)))
        ;; Collect the field accessor methods and the resulting object body.
        (where (M_f ... e ...) (body [S y] ...))
        ;; Collect the names of the definitions in the inheriting object.
        (where (m_d ...) (names M_d ... S_d ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object.
        (where (M_up ...) (override M_u ... M_f ... m_d ...))
        ;; Remove the shadowed substitutions before applying them to the body.
        (where (s ...) (all-object-shadows s_d ... (M_up ...)))
        inherits/uniform)))

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
