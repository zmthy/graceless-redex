#lang racket

(require redex)
(require "inheritance.rkt")

(provide (all-defined-out))

;; Test if expressions can cause a Racket error.
(redex-check Graceless-Inheritance e (eval-->GI (term e)))

(define-metafunction GI
  names : [M ...] -> [m ...]
  [(names [(method m _ ...) ...]) [m ...]])

(define-metafunction GI
  name< : m m -> boolean
  [(name< x_1 x_2) ,(symbol<? (term x_1) (term x_2))]
  [(name< x (_ :=)) #t]
  [(name< (_ :=) x) #f]
  [(name< (:= x_1) (:= x_2)) ,(symbol<? (term x_1) (term x_2))])

(define (name<? a b) (term (name< ,a ,b)))

(define-metafunction GI
  result-equiv : any any -> boolean
  [(result-equiv [(ref ℓ) σ] [m ...])
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv [m ...] [(ref ℓ) σ])
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv [e σ] e) #t]
  [(result-equiv e [e σ]) #t]
  [(result-equiv _ _) #f])

(define (test-->>GI t r)
  (test-->>
   -->GI
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program t)
   r))

(define empty-inherits
  (term (object
         (inherits (object)))))

(test-->>GI empty-inherits
            (term []))

(define simple-inherits
  (term (object
         (inherits (object
                    (method a () self)))
         (method b () self))))

(test-->>GI simple-inherits
            (term [a b]))

(define simple-override
  (term (object
         (inherits (object
                    (method m () self)))
         (method m () self))))

(test-->>GI simple-override
            (term [m]))

(define field-override
  (term (object
         (inherits (object
                    (var x)))
         (method x () self))))

(test-->>GI field-override
            (term [x (x :=)]))
