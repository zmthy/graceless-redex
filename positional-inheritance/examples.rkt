#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

;; Test if expressions can cause a Racket error.
(redex-check Graceless-Inheritance e (eval-->GU (term e)))

(define empty-inherits
  (term (object
         (inherits (object) as x))))

(test-->>GU empty-inherits
            (term []))

(define simple-inherits
  (term (object
         (method b () self)
         (inherits
          (object
           (method a () self)) as x))))

(test-->>GU simple-inherits
            (term [a b]))

(define simple-override
  (term (object
         (method m () self)
         (inherits
          (object
           (method m () self)) as x))))

(test-->>GU simple-override
            (term [m]))

(define field-override
  (term (object
         (method x () self)
         (inherits
          (object
           (var x)) as x))))

(test-->>GU field-override
            (term [x (x :=)]))

(define field-scoped
  (term (object
         (def x = self)
         (def y = (object
                   (inherits (object) as y)
                   (def z = (x)))))))

(test-->>GU field-scoped
            (term [x y]))

(define method-scoped
  (term (object
         (method m () self)
         (def x = (object
                   (inherits (object) as y)
                   (def x = (m)))))))

(test-->>GU method-scoped
            (term [m x]))

(define shadowed-by-super-field
  (term ((object
          (def x = self)
          (def y = ((object
                     (inherits
                      (object
                       (def x = done)) as y)
                     (def z = (x)))
                    z)))
         y)))

(test-->>GU shadowed-by-super-field
            (term done))

(define shadowed-by-super-method
  (term ((object
          (method m () self)
          (def x =
            ((object
              (inherits
               (object
                (method m () done)) as x)
              (def y = (m)))
             y)))
         x)))

(test-->>GU shadowed-by-super-method
            (term done))

(define down-call
  (term ((object
          (inherits
           (object
            (method m () (x))
            (def x = done)) as y)
          (def x = self))
         m)))

(test-->>GU down-call
            (term [m x]))

(define super-field-mutation-mutates-super
  (term ((object
          (def a =
            (object
             (var x := done)))
          (def b =
            (object
             (inherits (a) as z)
             (def y = ((x :=) self))))
          (def c = ((a) x)))
         c)))

(test-->>GU super-field-mutation-mutates-super
            (term stuck))

(define super-request
  (term ((object
          (method m () done)
          (inherits
           (object
            (method m () self)) as y)
          (def x = (y m)))
         x)))

(test-->>GU super-request
            (term [m x]))

(define shadowed-delayed-direct
  (term (object
         (def x =
           (object
            (inherits
             (object) as z)
            (def x = done)
            (def y = (x)))))))

(test-->>GU shadowed-delayed-direct
            (term [x]))

(define shadowed-delayed-indirect
  (term (object
         (def x =
           (object
            (inherits
             (object
              (def x = done)) as z)
            (def y = (x)))))))

(test-->>GU shadowed-delayed-indirect
            (term [x]))

(define field-mutation
  (term ((object
          (inherits (object
                     (var x)) as z)
          (def y = ((x :=) done)))
         x)))

(test-->>GU field-mutation
            (term done))

(define super-field-mutation
  (term ((object
          (inherits (object
                     (var x)) as z)
          (def y = (z (x :=) done)))
         x)))

(test-->>GU super-field-mutation
            (term done))

(define super-field-mutation-override
  (term ((object
          (inherits (object
                     (var x)) as z)
          (def x = done)
          (def y = (z (x :=) self)))
         x)))

(test-->>GU super-field-mutation-override
            (term done))

(define not-fresh
  (term (object
         (def x = (object))
         (def y = (object
                   (inherits (x) as z))))))

(test-->>GU not-fresh
            (term stuck))

(define override-field
  (term (object
         (method x (x) (x))
         (inherits
          (object
           (def x = done)) as y))))

(test-->>GU override-field
            (term [x]))

(define multiple-inherits
  (term (object
         (inherits (object) as x)
         (inherits (object) as y))))

(test-->>GU multiple-inherits
            (term []))

(define multiple-requests
  (term (object
         (inherits (object
                    (method a () done)) as x)
         (inherits (object
                    (method b () done)) as y)
         (a)
         (b))))

(test-->>GU multiple-requests
            (term [a b]))

(define multiple-supers
  (term (object
         (inherits (object
                    (method a () done)) as x)
         (inherits (object
                    (method b () done)) as y)
         (x a)
         (y b))))

(test-->>GU multiple-supers
            (term [a b]))

(define second-super-method
  (term ((object
          (inherits (object
                     (method m () self)) as x)
          (inherits (object
                     (method m () done)) as y))
         m)))

(test-->>GU second-super-method
            (term done))

(define overridden-super-fields
  (term ((object
          (method a () done)
          (method b () done)
          (method m () (x a))
          (inherits (object
                     (def a = self)) as x)
          (inherits (object
                     (def b = self)) as y))
         m)))

(test-->>GU overridden-super-fields
            (term [a b m]))

(test-results)
