#lang racket

(require redex)
(require "inheritance.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "inheritance.rkt"))

;; Small-step dynamic semantics of Graceless extended with delegating
;; inheritance.
(define -->GD
  (extend-reduction-relation
   -->GI
   GI
   #:domain p
   ;; Allocate the object o substituting local requests to this object, and
   ;; return the resulting reference.
   (--> [(in-hole E (object (name M (method m _ e)) ... F ...))
         σ]
        [(in-hole E (subst-object ℓ m ... m_f ...
                                  (field-assigns ℓ F ... (ref ℓ))))
         (store σ [M ... (subst-self-rec-method ℓ m ... M_f) ...])]
        (where ℓ (fresh-location σ))
        (where (m_f ...) (fields-names F ...))
        (where (M_f ...) (fields-methods F ...))
        (side-condition (term (unique m ... m_f ...)))
        object)))

;; Progress the program p by one step with the reduction relation -->GD.
(define (step-->GD p) (apply-reduction-relation -->GD p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GI
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->GD until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GI
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
