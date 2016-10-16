#lang racket

(require redex
         "graceless.rkt")

(provide test-->>G
         (all-from-out "graceless.rkt"))

(define-metafunction Graceless
  not-result : any -> boolean
  [(not-result uninitialised) #f]
  [(not-result v) #f]
  [(not-result _) #t])

(define-metafunction Graceless
  name< : m m -> boolean
  [(name< x_1 x_2) ,(symbol<? (term x_1) (term x_2))]
  [(name< x (_ ≔)) #t]
  [(name< (_ ≔) x) #f]
  [(name< (≔ x_1) (≔ x_2)) ,(symbol<? (term x_1) (term x_2))])

(define (name<? a b) (term (name< ,a ,b)))

(define-metafunction Graceless
  result-equiv : any any -> boolean
  [(result-equiv [_ any] stuck) (not-result any)]
  [(result-equiv [σ y] (m ...))
   ,(equal? (sort (term (m ...)) name<?) (sort (term (m_o ...)) name<?))
   (where (d ...) (lookup σ y))
   (where ((m_o _) ...) ((identify (signature d)) ...))]
  [(result-equiv [σ o] o) #t]
  [(result-equiv [σ _] _) #f]
  [(result-equiv any [σ o]) (result-equiv [σ o] any)])

(define-syntax-rule (test-->>G t r)
  (test-->>
   -->G
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program (term t))
   (term r)))
