#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

;; Test if expressions can cause a Racket error.
(redex-check Graceless-Inheritance e (eval-->GU (term e)))

(define empty-inherits
  (term (object
         (inherits (object)))))

(test-->>GU empty-inherits
            (term []))

(define simple-inherits
  (term (object
         (inherits
          (object
           (method a () self)))
         (method b () self))))

(test-->>GU simple-inherits
            (term [a b]))

(define simple-override
  (term (object
         (inherits
          (object
           (method m () self)))
         (method m () self))))

(test-->>GU simple-override
            (term [m]))

(define field-override
  (term (object
         (inherits
          (object
           (var x)))
         (method x () self))))

(test-->>GU field-override
            (term [x (x :=)]))

(define field-scoped
  (term (object
         (def x = self)
         (def y = (object
                   (inherits (object))
                   (def z = (x)))))))

(test-->>GU field-scoped
            (term [x y]))

(define method-scoped
  (term (object
         (method m () self)
         (def x = (object
                   (inherits (object))
                   (def x = (m)))))))

(test-->>GU method-scoped
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

(test-->>GU shadowed-by-super-field
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

(test-->>GU shadowed-by-super-method
            (term done))

(define down-call
  (term ((object
          (inherits
           (object
            (method m () (x))
            (def x = done)))
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
             (inherits (a))
             (def y = ((x :=) self))))
          (def c = ((a) x)))
         c)))

(test-->>GU super-field-mutation-mutates-super
            (term stuck))

(define super-request
  (term ((object
          (inherits
           (object
            (method a () self)) alias (a as b))
          (method a () done)
          (def x = (b)))
         x)))

(test-->>GU super-request
            (term [a b x]))

(define shadowed-delayed-direct
  (term (object
         (def x =
           (object
            (inherits
             (object))
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
              (def x = done)))
            (def y = (x)))))))

(test-->>GU shadowed-delayed-indirect
            (term [x]))

(define field-mutation
  (term ((object
          (inherits (object
                     (var x)))
          (def y = ((x :=) done)))
         x)))

(test-->>GU field-mutation
            (term done))

(define super-field-mutation
  (term ((object
          (inherits (object
                     (var x)))
          (def y = ((x :=) done)))
         x)))

(test-->>GU super-field-mutation
            (term done))

(define super-field-mutation-override
  (term ((object
          (inherits (object
                     (var x)))
          (def x = done)
          (def y = ((x :=) self)))
         x)))

(test-->>GU super-field-mutation-override
            (term done))

(define not-fresh
  (term (object
         (def x = (object))
         (def y = (object
                   (inherits (x)))))))

(test-->>GU not-fresh
            (term stuck))

(define override-field
  (term (object
         (inherits
          (object
           (def x = done)))
         (method x (x) (x)))))

(test-->>GU override-field
            (term [x]))

(define multiple-inherits
  (term (object
         (inherits (object))
         (inherits (object)))))

(test-->>GU multiple-inherits
            (term []))

(define multiple-requests
  (term (object
         (inherits (object
                    (method a () done)))
         (inherits (object
                    (method b () done)))
         (a)
         (b))))

(test-->>GU multiple-requests
            (term [a b]))

(define method-conflict
  (term (object
         (inherits (object
                    (method m () done)))
         (inherits (object
                    (method m () done)))
         (m))))

(test-->>GU method-conflict
            (term stuck))

(define method-conflict-resolved
  (term (object
         (inherits (object
                    (method m () done)))
         (inherits (object
                    (method m () done)))
         (method m () done)
         (m))))

(test-->>GU method-conflict-resolved
            (term [m]))

(define overridden-super-fields
  (term ((object
          (inherits (object
                     (def a = self)) alias (a as x))
          (inherits (object
                     (def b = self)) alias (b as y))
          (method a () done)
          (method b () done)
          (method m () (x)))
         m)))

(test-->>GU overridden-super-fields
            (term [a b m x y]))

(define excluded-method
  (term (object
         (inherits (object
                    (method m () done)) exclude m)
         (m))))

(test-->>GU excluded-method
            (term stuck))

(define exclude-to-resolve-conflict
  (term ((object
         (inherits (object
                    (method m () done)))
         (inherits (object
                    (method m () self)) exclude m))
         m)))

(test-->>GU exclude-to-resolve-conflict
            (term done))

(test-results)
