#lang racket

(require redex)
(require "graceless.rkt")

(provide (all-defined-out)
         (all-from-out "graceless.rkt")
         program)

(define-extended-language Graceless-Inheritance Graceless
  (o ....
     (object I M ... F ...))
  (I (inherits e)))

(define-union-language GIU Graceless-Inheritance G)

(define-extended-language GI GIU
  (E⊥ (object (inherits E) M ... F ...)))

(define-metafunction GI
  override : Ms ms -> Ms
  [(override [] _) []]
  [(override [(method m _ _ ... _) M ...] (name ms [_ ... m _ ...]))
   (override [M ...] ms)]
  [(override [M M_i ...] ms) [M M_p ...]
   (where [M_p ...] (override [M_i ...] ms))])

(define -->GI
  (extend-reduction-relation
   -->G
   GI
   #:domain p
   (--> [(in-hole E (object (inherits (ref ℓ))
                            (name M (method m _ ...)) ... F ...)) σ]
        [(in-hole E (object M_i ... M ... F ...)) σ]
        (where Ms (lookup σ ℓ))
        (where [ms ...] (fields-names [F ...]))
        (where [M_i ...] (override Ms [m ... ms ...]))
        inherits)))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->GI p) (apply-reduction-relation -->GI p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GI
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->G until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GI
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GI (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error.
(define (eval-->GI t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GI t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->GI t) (traces -->GI (program t)))
