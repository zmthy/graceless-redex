#lang racket

(require redex
         "forwarding.rkt"
         "concatenation.rkt"
         "delegation.rkt"
         "merged.rkt"
         "uniform.rkt")

(provide (all-defined-out)
         (all-from-out "forwarding.rkt")
         (all-from-out "concatenation.rkt")
         (all-from-out "delegation.rkt")
         (all-from-out "merged.rkt")
         (all-from-out "uniform.rkt"))

;; Test if expressions can cause a Racket error.
(redex-check Graceless-Inheritance e (eval-->GF (term e)))
(redex-check Graceless-Inheritance e (eval-->GC (term e)))
(redex-check Graceless-Inheritance e (eval-->GD (term e)))
(redex-check Graceless-Inheritance e (eval-->GM (term e)))
(redex-check Graceless-Inheritance e (eval-->GU (term e)))

(define-metafunction GI
  not-result : e -> boolean
  [(not-result uninitialised) #f]
  [(not-result v) #f]
  [(not-result _) #t])

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
  [(result-equiv [e _] stuck) (not-result e)]
  [(result-equiv stuck [e _]) (not-result e)]
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

(define (test-->>GO t r)
  (test-->>GF t r)
  (test-->>GC t r)
  (test-->>GD t r))

(define (test-->>GM t r)
  (test-->>G -->GM t r))

(define (test-->>GU t r)
  (test-->>G -->GU t r))

(define (test-->>GI t r)
  (test-->>GM t r)
  (test-->>GU t r))

(define (test-->>GA t r)
  (test-->>GO t r)
  (test-->>GI t r))

(define empty-inherits
  (term (object
         (inherits (object)))))

(test-->>GA empty-inherits
            (term []))

(define simple-inherits
  (term (object
         (inherits (object
                    (method a () self)))
         (method b () self))))

(test-->>GA simple-inherits
            (term [a b]))

(define simple-override
  (term (object
         (inherits (object
                    (method m () self)))
         (method m () self))))

(test-->>GA simple-override
            (term [m]))

(define field-override
  (term (object
         (inherits (object
                    (var x)))
         (method x () self))))

(test-->>GA field-override
            (term [x (x :=)]))

(define field-scoped
  (term (object
         (def x = self)
         (def y =
           (object
            (inherits (object))
            (def z = (request x)))))))

(test-->>GA field-scoped
            (term [x y]))

(define method-scoped
  (term (object
         (method m () self)
         (def x =
           (object
            (inherits (object))
            (def x = (request m)))))))

(test-->>GA method-scoped
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

(test-->>GA shadowed-by-super-field
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

(test-->>GA shadowed-by-super-method
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

(define super-field-mutation-mutates-super
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

(test-->>GF super-field-mutation-mutates-super
            (term [x (x :=) y]))

(test-->>GC super-field-mutation-mutates-super
            (term done))

(test-->>GD super-field-mutation-mutates-super
            (term [x (x :=) y]))

(test-->>GM super-field-mutation-mutates-super
            (term stuck))

(define super-request
  (term (request
         (object
          (inherits
           (object
            (method m () self)))
          (method m () done)
          (def x = (request super m)))
         x)))

(test-->>GF super-request
            (term [m]))

(test-->>GC super-request
            (term [m x]))

(test-->>GD super-request
            (term [m x]))

(test-->>GM super-request
            (term [m x]))

(define shadowed-delayed-direct
  (term (object
         (def x =
           (object
            (inherits
             (object))
            (def x = done)
            (def y = (request x)))))))

(test-->>GA shadowed-delayed-direct
            (term [x]))

(define shadowed-delayed-indirect
  (term (object
         (def x =
           (object
            (inherits
             (object
              (def x = done)))
            (def y = (request x)))))))

(test-->>GA shadowed-delayed-indirect
            (term [x]))

(define field-mutation
  (term (request
         (object
          (inherits (object
                     (var x)))
          (def y = (request (x :=) done)))
         x)))

(test-->>GA field-mutation
            (term done))

(define super-field-mutation
  (term (request
         (object
          (inherits (object
                     (var x)))
          (def y = (request super (x :=) done)))
         x)))

(test-->>GA super-field-mutation
            (term done))

(define super-field-mutation-override
  (term (request
         (object
          (inherits (object
                     (var x)))
          (def x = done)
          (def y = (request super (x :=) self)))
         x)))

(test-->>GF super-field-mutation-override
            (term done))

(test-->>GC super-field-mutation-override
            (term [x (x :=) y]))

(test-->>GD super-field-mutation-override
            (term done))

(test-->>GM super-field-mutation-override
            (term done))

(test-->>GU super-field-mutation-override
            (term done))

(define not-fresh
  (term (object
         (def x = (object))
         (def y = (object
                   (inherits (request x)))))))

(test-->>GO not-fresh
            (term [x y]))

(test-->>GI not-fresh
            (term stuck))

(define override-field
  (term (object
         (inherits
          (object
           (def x = done)))
         (method x (x) (request x)))))

(test-->>GA override-field
            (term [x]))

(test-results)
