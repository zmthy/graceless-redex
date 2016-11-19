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
  test-subtype : (T ...) T -> boolean
  [(test-subtype (S) U) ,(judgment-holds (subtype S U))]
  [(test-subtype _ _) #f])

(define-metafunction Graceless
  test-typed : (Σ ...) o -> (T ...)
  [(test-typed (Σ) o) ,(judgment-holds (typed Σ () o T) T)]
  [(test-typed _ _) ()])

(define-metafunction Graceless
  test-store-typed : σ -> (Σ ...)
  [(test-store-typed σ) ,(judgment-holds (store-typed σ Σ) Σ)])

(define-metafunction Graceless
  result-typed : any any -> boolean
  [(result-typed [σ any] (T))
   (test-subtype (test-typed (test-store-typed σ) any) T)]
  [(result-typed [σ o] _) #f]
  [(result-typed any [σ o]) (result-typed [σ o] any)])

(define-metafunction Graceless
  result-equiv : any any -> boolean
  [(result-equiv [_ any] stuck) (not-result any)]
  [(result-equiv [σ v] T) (result-typed [σ v] (T))]
  [(result-equiv [σ o] o) #t]
  [(result-equiv [σ o] _) #f]
  [(result-equiv any [σ o]) (result-equiv [σ o] any)])

(define-syntax-rule (test-->>G t r)
  (begin
    (test-->>
     -->G
     #:equiv (λ (a b) (term (result-typed ,a ,b)))
     (program (term t))
     (judgment-holds (typed () () t T) T))
    (test-->>
     -->G
     #:equiv (λ (a b) (term (result-equiv ,a ,b)))
     (program (term t))
     (term r))))
