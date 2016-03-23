#lang racket

(require redex
         "graceless.rkt")

(provide test-->>G
         (all-from-out "graceless.rkt"))

(define-metafunction G
  not-result : any -> boolean
  [(not-result uninitialised) #f]
  [(not-result v) #f]
  [(not-result _) #t])

(define-metafunction G
  names : O -> (m ...)
  [(names (object F ... (method m _ _) ...)) (m ...)])

(define-metafunction G
  name< : m m -> boolean
  [(name< x_1 x_2) ,(symbol<? (term x_1) (term x_2))]
  [(name< x (_ :=)) #t]
  [(name< (_ :=) x) #f]
  [(name< (:= x_1) (:= x_2)) ,(symbol<? (term x_1) (term x_2))])

(define (name<? a b) (term (name< ,a ,b)))

(define-metafunction G
  result-equiv : any any -> boolean
  [(result-equiv [_ any] stuck) (not-result any)]
  [(result-equiv stuck [_ any]) (not-result any)]
  [(result-equiv [σ (ref ℓ)] (m ...))
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv (m ...) [σ (ref ℓ)])
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv [σ e] e) #t]
  [(result-equiv e [σ e]) #t]
  [(result-equiv _ _) #f])

(define (test-->>G t r)
  (test-->>
   -->G
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program t)
   r))
