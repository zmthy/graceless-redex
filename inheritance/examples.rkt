#lang racket

(require redex
         "test.rkt"
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

(define empty-inherits
  (term (object
         (inherits (object)))))

(test-->>GA empty-inherits
            (term []))

(define simple-inherits
  (term (object
         (inherits
          (object
           (method a () self)))
         (method b () self))))

(test-->>GA simple-inherits
            (term [a b]))

(define simple-override
  (term (object
         (inherits
          (object
           (method m () self)))
         (method m () self))))

(test-->>GA simple-override
            (term [m]))

(define field-override
  (term (object
         (inherits
          (object
           (var x)))
         (method x () self))))

(test-->>GA field-override
            (term [x (x :=)]))

(define field-scoped
  (term (object
         (def x = self)
         (def y = (object
                   (inherits (object))
                   (def z = (x)))))))

(test-->>GA field-scoped
            (term [x y]))

(define method-scoped
  (term (object
         (method m () self)
         (def x = (object
                   (inherits (object))
                   (def x = (m)))))))

(test-->>GA method-scoped
            (term [m x]))

(define shadowed-by-super-field
  (term ((object
          (def x = self)
          (def y = ((object
                     (inherits
                      (object
                       (def x = done)))
                     (def z = (x)))
                    z)))
         y)))

(test-->>GA shadowed-by-super-field
            (term done))

(define shadowed-by-super-method
  (term ((object
          (method m () self)
          (def x =
            ((object
              (inherits
               (object
                (method m () done)))
              (def y = (m)))
             y)))
         x)))

(test-->>GA shadowed-by-super-method
            (term done))

(define down-call
  (term ((object
          (inherits
           (object
            (method m () (x))
            (def x = done)))
          (def x = self))
         m)))

(test-->>GF down-call
            (term done))

(test-->>GC down-call
            (term [m x]))

(test-->>GD down-call
            (term [m x]))

(test-->>GI down-call
            (term [m x]))

(define super-field-mutation-mutates-super
  (term ((object
          (def a =
            (object
             (var x := done)))
          (def b =
            (object
             (inherits (a))
             (def y = ((x :=) self))))
          (def c = ((a) x)))
         c)))

(test-->>GF super-field-mutation-mutates-super
            (term [x (x :=) y]))

(test-->>GC super-field-mutation-mutates-super
            (term done))

(test-->>GD super-field-mutation-mutates-super
            (term [x (x :=) y]))

(test-->>GI super-field-mutation-mutates-super
            (term stuck))

(define super-request
  (term ((object
          (inherits
           (object
            (method m () self)))
          (method m () done)
          (def x = (super m)))
         x)))

(test-->>GF super-request
            (term [m]))

(test-->>GC super-request
            (term [m x]))

(test-->>GD super-request
            (term [m x]))

(test-->>GI super-request
            (term [m x]))

(define shadowed-delayed-direct
  (term (object
         (def x =
           (object
            (inherits
             (object))
            (def x = done)
            (def y = (x)))))))

(test-->>GA shadowed-delayed-direct
            (term [x]))

(define shadowed-delayed-indirect
  (term (object
         (def x =
           (object
            (inherits
             (object
              (def x = done)))
            (def y = (x)))))))

(test-->>GA shadowed-delayed-indirect
            (term [x]))

(define field-mutation
  (term ((object
          (inherits (object
                     (var x)))
          (def y = ((x :=) done)))
         x)))

(test-->>GA field-mutation
            (term done))

(define super-field-mutation
  (term ((object
          (inherits (object
                     (var x)))
          (def y = (super (x :=) done)))
         x)))

(test-->>GA super-field-mutation
            (term done))

(define super-field-mutation-override
  (term ((object
          (inherits (object
                     (var x)))
          (def x = done)
          (def y = (super (x :=) self)))
         x)))

(test-->>GA super-field-mutation-override
            (term done))

(define not-fresh
  (term (object
         (def x = (object))
         (def y = (object
                   (inherits (x)))))))

(test-->>GO not-fresh
            (term [x y]))

(test-->>GI not-fresh
            (term stuck))

(define override-field
  (term (object
         (inherits
          (object
           (def x = done)))
         (method x (x) (x)))))

(test-->>GA override-field
            (term [x]))

(test-results)
