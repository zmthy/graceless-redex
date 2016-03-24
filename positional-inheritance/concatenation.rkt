#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with concatenating
;; inheritance.
(define -->GC
  (extend-reduction-relation
   -->GPO
   GO
   #:domain p
   ;; Inherits concatenates the methods in the super object into the object
   ;; constructor and returns the resulting concatenation.  The actual object
   ;; reference will be built in the next step. Note that under concatenation,
   ;; there can only ever be one inherits context.
   (--> [σ (in-hole E ((i inherits (ref ℓ) any ...) e ...))]
        ;; Update the self object, add the fields into self, and perform the
        ;; substitutions into the remaining body.
        [(update σ M ... i_p)
         (in-hole E (seq ((ref ℓ_d) x_f <- v) ...
                         (subst s ...
                                [i_p / super]
                                [(self 0) / m ...]
                                s_s ... e) ...))]
        ;; Fetch the optional name and substitutions of the inherits clause.
        (where [(x ...) (s ...)] (optional-name any ...))
        ;; Lookup the super object.
        (where (object [x_f v] ... M ...) (lookup σ ℓ))
        ;; Collect the names of the definitions in the inherited object.
        (where (m ...) (names M ...))
        ;; Fetch the actual self value from the bottom of the inherits contexts.
        (where ℓ_d ,(first (term i)))
        ;; Construct the optional super substitution.
        (where (s_s ...) ([ℓ as ℓ_d / x] ...))
        ;; Include the new super alias in the top of the inherits context.
        (where (i_p) (add-substitution (s_s ...) i))
        inherits/concatenation)))

;; Progress the program p by one step with the reduction relation -->GC.
(define (step-->GC p) (apply-reduction-relation -->GC p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GC until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GC (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GC,
;; returning the resulting object, stuck program, or error.
(define (eval-->GC t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GC,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GC t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GC.
(define (traces-->GC t) (traces -->GC (program t)))
