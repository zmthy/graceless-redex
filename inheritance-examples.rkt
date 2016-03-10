#lang racket

(require redex
         "forwarding.rkt"
         "concatenation.rkt"
         "delegation.rkt")

(provide (all-defined-out)
         (all-from-out "forwarding.rkt")
         (all-from-out "concatenation.rkt")
         (all-from-out "delegation.rkt"))

;; Test if expressions can cause a Racket error.
(redex-check Graceless-Inheritance e (eval-->GF (term e)))
(redex-check Graceless-Inheritance e (eval-->GC (term e)))
(redex-check Graceless-Inheritance e (eval-->GD (term e)))

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

(define (test-->>G a t r)
  (test-->>
   a
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program t)
   r))

(define (test-->>GF t r)
  (test-->>G -->GF t r))

(define (test-->>GC t r)
  (test-->>G -->GC t r))

(define (test-->>GD t r)
  (test-->>G -->GD t r))

(define (test-->>GI t r)
  (test-->>GF t r)
  (test-->>GC t r)
  (test-->>GD t r))

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

(define field-scoped
  (term (object
         (def x = self)
         (def y =
           (object
            (inherits (object))
            (def z = (request x)))))))

(test-->>GI field-scoped
            (term [x y]))

(define method-scoped
  (term (object
         (method m () self)
         (def x =
           (object
            (inherits (object))
            (def x = (request m)))))))

(test-->>GI method-scoped
            (term [m x]))

(define shadowed-by-super-field
  (term (request
         (object
          (def x = self)
          (def y =
            (request
             (object
              (inherits
               (object
                (def x = done)))
              (def z = (request x)))
             z)))
         y)))

(test-->>GI shadowed-by-super-field
            (term done))

(define shadowed-by-super-method
  (term (request
         (object
          (method m () self)
          (def x =
            (request
             (object
              (inherits
               (object
                (method m () done)))
              (def y = (request m)))
             y)))
         x)))

(test-->>GI shadowed-by-super-method
            (term done))

(define down-call
  (term (request
         (object
          (inherits
           (object
            (method m ()
                    (request x))
            (def x = done)))
          (def x = self))
         m)))

(test-->>GF down-call
            (term done))

(test-->>GC down-call
            (term [m x]))

(test-->>GD down-call
            (term [m x]))

(define field-mutation
  (term (request
         (object
          (def a =
            (object
             (var x := done)))
          (def b =
            (object
             (inherits (request a))
             (def y = (request (x :=) self))))
          (def c = (request (request a) x)))
         c)))

(test-->>GF field-mutation
            (term [x (x :=) y]))

(test-->>GC field-mutation
            (term done))

(test-->>GD field-mutation
            (term [x (x :=) y]))

(define super-ref
  (term (request
         (object
          (inherits
           (object))
          (def x = super))
         x)))

(test-->>GI super-ref
            (term []))

(define super-request
  (term (request
         (object
          (inherits
           (object
            (method m () self)))
          (method m () done)
          (def x = (request super m)))
         x)))

(test-->>GI super-request
            (term [m]))

(define shadowed-delayed-direct
  (term (object
         (def x =
           (object
            (inherits
             (object))
            (def x = done)
            (def y = (request x)))))))

(test-->>GI shadowed-delayed-direct
            (term [x]))

(define shadowed-delayed-indirect
  (term (object
         (def x =
           (object
            (inherits
             (object
              (def x = done)))
            (def y = (request x)))))))

(test-->>GI shadowed-delayed-indirect
            (term [x]))
