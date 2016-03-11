#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with delegating
;; inheritance.
(define -->GD
  (extend-reduction-relation
   -->GR
   GO
   #:domain p
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [(in-hole E (name o (object M ... F ...))) σ]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(in-hole E (subst [ℓ self] [ℓ m ...] (field-assigns ℓ F ... (ref ℓ))))
         ;; Under delegation, all references to self and local requests are
         ;; substituted in methods that are placed in the store only for fields.
         (store σ [M ...
                   (subst-method [ℓ self] M_f) ...])]
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; The method names are used for substituting local requests, as well as
        ;; ensuring the resulting object has unique method names.
        (where (m ...) (object-names o))
        ;; The generated getter and setter methods are included in the store.
        (where (M_f ...) (field-methods F ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        object)))

;; Progress the program p by one step with the reduction relation -->GD.
(define (step-->GD p) (apply-reduction-relation -->GD p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->GD until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GD (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GD,
;; returning the resulting object, stuck program, or error.
(define (eval-->GD t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GD,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GD t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GD.
(define (traces-->GD t) (traces -->GD (program t)))
