#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

(define-term simple-object
  (object (self 0)))

(test-->>G simple-object
           ⊤)

(define-term simple-method
  (object
   (method
    (m () → ⊤)
    (self 0))
   (self 0)))

(test-->>G simple-method
           (type (m () → ⊤)))

(define-term simple-request
  ((object
    (method
     (m () → ⊤)
     (self 0))
    (self 0))
   m))

(test-->>G simple-request
           (type (m () → ⊤)))

(define-term scoped
  ((object
    (method (a () → (⋃ (type (b ([x : ⊤]) → ⊤))))
            (object
             (method (b ([x : ⊤]) → ⊤) (x))
             (self 0)))
    (self 0))
   a))

(test-->>G scoped
           (type (b ([x : ⊤]) → ⊤)))

(define-term single-arg
  (object
   ((object
     (method (identity ([x : ⊤]) → ⊤) (x))
     (self 0))
    identity
    (self 0))))

(test-->>G single-arg
           ⊤)

(define-term multiple-args
  (object
   ((object
     (method (const ([x : ⊤] [y : ⊤]) → ⊤) (x))
     (self 0))
    const
    (self 0)
    (self 0))))

(test-->>G multiple-args
           ⊤)

(define-term local-request
  ((object
    (method (first () → ⊤) (second))
    (method (second () → ⊤) (self 0))
    (self 0))
   first))

(test-->>G local-request
           (type (first () → ⊤)
                 (second () → ⊤)))

(define-term simple-field
  (object
   (method (x () → ⊤) (↥ (self 0)))
   ((self 0) ← (method (x () → ⊤) (self 0)))))

(test-->>G simple-field
           (type (x () → ⊤)))

(define-term method-and-field
  (object
   (method (m () → ⊤) (self 0))
   (method (x () → ⊤) (↥ (self 0)))
   ((self 0) ← (method (x () → ⊤) (self 0)))))

(test-->>G method-and-field
           (type (m () → ⊤)
                 (x () → ⊤)))

(define-term uninit-request
  (object
   (method (x () → ⊤) (↥ (self 0)))
   (x)))

(test-->>G uninit-request
           raise)

(define-term mutable-field
  (object
   (method (x () → ⊤) (↥ (self 0)))
   (method ((x ≔) ([v : ⊤]) → ⊤) ((self 0) ← (method (x () → ⊤) (v))))
   (self 0)))

(test-->>G mutable-field
           (type (x () → ⊤)
                 ((x ≔) ([v : ⊤]) → ⊤)))

(define-term local-field-assign
  (object
   (method (x () → ⊤) (↥ (self 0)))
   (method ((x ≔) ([v : ⊤]) → ⊤) ((self 0) ← (method (x () → ⊤) (v))))
   (method (y () → ⊤) (↥ (self 0)))
   ((x ≔) (self 0))))

(test-->>G local-field-assign
           (type (x () → ⊤)
                 ((x ≔) ([v : ⊤]) → ⊤)
                 (y () → ⊤)))

(define-term field-assign
  (object
   ((object
     (method (x () → ⊤) (↥ (self 0)))
     (method ((x ≔) ([v : ⊤]) → ⊤) ((self 0) ← (method (x () → ⊤) (v))))
     (self 0))
    (x ≔)
    (self 0))))

(test-->>G field-assign
           ⊤)

(define-term scoped-field
  ((object
    (method
     (m () → ⊤)
     (self 0))
    (method
     (x () → ⊤)
     (↥ (self 0)))
    (method
     ((x ≔) ([v : ⊤]) → ⊤)
     ((self 0) ← (method (x () → ⊤) (v))))
    ((x ≔) ((object
             (method
              (y () → ⊤)
              (↥ (self 0)))
             (method
              ((y ≔) ([v : ⊤]) → ⊤)
              ((self 0) ← (method (y () → ⊤) (v))))
             ((y ≔) (m)))
            y)))
   x))

(test-->>G scoped-field
           (type (m () → ⊤)
                 (x () → ⊤)
                 ((x ≔) ([v : ⊤]) → ⊤)))

(test-results)
