#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

(define-term simple-object
  (object done))

(test-->>G simple-object
           ())

(define-term simple-method
  (object
   (method (m () → ⊤)
           done)
   done))

(test-->>G simple-method
           (m))

(define-term simple-request
  ((object
    (method (m ([x : ⊤]) → ⊤)
            done)
    done)
   m
   done))

(test-->>G simple-request
           done)

(define-term scoped
  ((object
    (method (a ([x : ⊤]) → ⊤)
            (object
             (method (b ([x : ⊤]) → ⊤) (x))
             done))
    done)
   a
   done))

(test-->>G scoped
           (b))

(define-term multiple-args
  ((object
    (method (const ([x : ⊤] [y : ⊤]) → ⊤) (y))
    done)
   const
   done
   done))

(test-->>G multiple-args
           done)

(define-term local-request
  ((object
    (method (first () → ⊤) (second))
    (method (second () → ⊤) done)
    done)
   first))

(test-->>G local-request
           done)

(define-term simple-field
  (object
   (method (x () → ⊤) uninitialised)
   ((self 0) x ← done)))

(test-->>G simple-field
           (x))

(define-term method-and-field
  (object
   (method (m () → ⊤) done)
   (method (x () → ⊤) uninitialised)
   ((self 0) x ← done)))

(test-->>G method-and-field
           (m x))

(define-term uninit-request
  (object
   (method (x () → ⊤) uninitialised)
   (x)))

(test-->>G uninit-request
           uninitialised)

(define-term mutable-field
  (object
   (method (x () → ⊤) uninitialised)
   (method ((x ≔) ([x : ⊤]) → Done) ((self 0) x ← (x)))
   done))

(test-->>G mutable-field
           (x (x ≔)))

(define-term local-field-assign
  (object
   (method (x () → ⊤) uninitialised)
   (method ((x ≔) ([x : ⊤]) → Done) ((self 0) x ← (x)))
   (method (y () → ⊤) uninitialised)
   ((x ≔) done)))

(test-->>G local-field-assign
           (x (x ≔) y))

(define-term field-assign
  ((object
    (method (x () → ⊤) uninitialised)
    (method ((x ≔) ([x : ⊤]) → Done) ((self 0) x ← (x)))
    done)
   (x ≔)
   done))

(test-->>G field-assign
           done)

(define-term done-argument
  ((object
    (method (m ([x : ⊤]) → ⊤) (x))
    done)
   m
   done))

(test-->>G done-argument
           done)

(define-term scoped-field
  ((object
    (method (m () → ⊤) done)
    (method (x () → ⊤) uninitialised)
    ((self 0) x ← ((object
                    (method (y () → ⊤) uninitialised)
                    ((self 0) y ← (m)))
                   y)))
   x))

(test-->>G scoped-field
           done)

(test-results)
