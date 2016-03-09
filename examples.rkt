#lang racket

(require redex)
(require "graceless.rkt")

(provide (all-defined-out))

;; Test if expressions can cause a Racket error.
(redex-check Graceless e (eval-->G (term e)))

(define-metafunction G
  names : [M ...] -> [m ...]
  [(names [(method m _ ...) ...]) (m ...)])

(define-metafunction G
  name< : m m -> boolean
  [(name< x_1 x_2) ,(symbol<? (term x_1) (term x_2))]
  [(name< x (_ :=)) #t]
  [(name< (_ :=) x) #f]
  [(name< (:= x_1) (:= x_2)) ,(symbol<? (term x_1) (term x_2))])

(define (name<? a b) (term (name< ,a ,b)))

(define-metafunction G
  result-equiv : any any -> boolean
  [(result-equiv [(ref ℓ) σ] (m ...))
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv (m ...) [(ref ℓ) σ])
   ,(equal? (sort (term [m ...]) name<?) (sort (term [m_o ...]) name<?))
   (where [m_o ...] (names (lookup σ ℓ)))]
  [(result-equiv [e σ] e) #t]
  [(result-equiv e [e σ]) #t]
  [(result-equiv _ _) #f])

(define (test-->>G t r)
  (test-->>
   -->G
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program t)
   r))

(define simple-object
  (term (object)))

(test-->>G simple-object
           (term []))

(define simple-method
  (term (object
          (method m ()
                  self))))

(test-->>G simple-method
           (term [m]))

(define simple-request
  (term (request
          (object
           (method m (x)
                   (request x)))
          m
          (object))))

(test-->>G simple-request
           (term []))

(define scoped
  (term (request
          (object
           (method m (x)
                   (object
                    (method m (x)
                            (request x)))))
          m
          (object))))

(test-->>G scoped
           (term [m]))

(define multiple-args
  (term (request
          (object
           (method const
                   (x y)
                   (request y)))
          const
          (object)
          (object))))

(test-->>G multiple-args
           (term []))

(define local-request
  (term (request
          (object
           (method first ()
                   (request second))
           (method second ()
                   self))
          first)))

(test-->>G local-request
           (term [first second]))

(define simple-field
  (term (object
          (def x = self))))

(test-->>G simple-field
           (term [x]))

(define method-and-field
  (term (object
          (method m ()
                  self)
          (def x = self))))

(test-->>G simple-field
           (term [x]))

(define uninit-request
  (term (object
          (method val ()
                  (request x))
          (def x = (request val)))))

(test-->>G uninit-request
           (term uninitialised))

(define mutable-field
  (term (object
         (var x))))

(test-->>G mutable-field
           (term [x (x :=)]))

(define local-field-assign
  (term (object
         (var x)
         (def y = (request (x :=) self)))))

(test-->>G local-field-assign
           (term [x (x :=) y]))

(define field-assign
  (term (request
         (object
          (var x))
         (x :=)
         (object))))

(test-->>G field-assign
           (term []))
