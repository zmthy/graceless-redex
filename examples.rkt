#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

(define-term simple-object
  (object done))

(test-->>G simple-object
           (type))

(define-term simple-method
  (object
   (method (m () → Done)
           done)
   done))

(test-->>G simple-method
           (type (m () → Done)))

(define-term simple-request
  ((object
    (method (m ([x : ⊤]) → Done)
            done)
    done)
   m
   done))

(test-->>G simple-request
           Done)

(define-term scoped
  ((object
    (method (a ([x : ⊤]) → (type (b ([x : ⊤]) → ⊤)))
            (object
             (method (b ([x : ⊤]) → ⊤) (x))
             done))
    done)
   a
   done))

(test-->>G scoped
           (type (b ([x : ⊤]) → ⊤)))

(define-term multiple-args
  ((object
    (method (const ([x : ⊤] [y : ⊤]) → ⊤) (y))
    done)
   const
   done
   done))

(test-->>G multiple-args
           Done)

(define-term local-request
  ((object
    (method (first () → Done) (second))
    (method (second () → Done) done)
    done)
   first))

(test-->>G local-request
           Done)

(define-term simple-field
  (object
   (method (x () → Done) uninitialised)
   ((self 0) x ← done)))

(test-->>G simple-field
           (type (x () → Done)))

(define-term method-and-field
  (object
   (method (m () → Done) done)
   (method (x () → Done) uninitialised)
   ((self 0) x ← done)))

(test-->>G method-and-field
           (type (m () → Done)
                 (x () → Done)))

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
           (type (x () → ⊤)
                 ((x ≔) ([x : ⊤]) → Done)))

(define-term local-field-assign
  (object
   (method (x () → ⊤) uninitialised)
   (method ((x ≔) ([x : ⊤]) → Done) ((self 0) x ← (x)))
   (method (y () → ⊤) uninitialised)
   ((x ≔) done)))

(test-->>G local-field-assign
           (type (x () → ⊤)
                 ((x ≔) ([x : ⊤]) → Done)
                 (y () → ⊤)))

(define-term field-assign
  ((object
    (method (x () → ⊤) uninitialised)
    (method ((x ≔) ([x : ⊤]) → Done) ((self 0) x ← (x)))
    done)
   (x ≔)
   done))

(test-->>G field-assign
           Done)

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
           Done)

(test-results)
