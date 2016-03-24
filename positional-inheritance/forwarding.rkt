#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with forwarding
;; inheritance.
(define -->GF
  (extend-reduction-relation
   -->GPI
   GO
   #:domain p
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [σ (in-hole E (object s ... B ...))]
        ;; Under forwarding, all references to self and local requests are
        ;; substituted in methods that are placed in the store.
        [(store σ (object (subst-method s ...
                                        [ℓ / (self 0)]
                                        [(self 0) / m ...] M) ...
                          (subst-method [ℓ / (self 0)] M_f) ...))
         (in-hole E (subst s ...
                           [(ℓ M ... M_f ... s ...) / super]
                           [ℓ / (self 0)]
                           [(self 0) / m ...] (seq e ... (ref ℓ))))]
        ;; Split the body into methods and statements.
        (where [(M ...) (S ...)] (split-body B ...))
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; The method names are used for substituting local requests, as well as
        ;; ensuring the resulting object has unique method names.
        (where (m ...) (names M ... S ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S ...)))
        ;; Collect the field accessor methods and the resulting object body.
        (where (M_f ... e ...) (body [S y] ...))
        object/forwarding)))

;; Progress the program p by one step with the reduction relation -->GF.
(define (step-->GF p) (apply-reduction-relation -->GF p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GF until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GF (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GF,
;; returning the resulting object, stuck program, or error.
(define (eval-->GF t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GF,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GF t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GF.
(define (traces-->GF t) (traces -->GF (program t)))
