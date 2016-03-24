#lang racket

(require redex
         "test.rkt")

(provide (all-defined-out)
         (all-from-out "test.rkt"))

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
  (term ((object
          (method m (x) (x)))
         m
         (object))))

(test-->>G simple-request
           (term []))

(define scoped
  (term ((object
          (method m (x)
                  (object
                   (method m (x) (x)))))
         m
         (object))))

(test-->>G scoped
           (term [m]))

(define multiple-args
  (term ((object
          (method const (x y) (y)))
         const
         (object)
         (object))))

(test-->>G multiple-args
           (term []))

(define local-request
  (term ((object
          (method first () (second))
          (method second () self))
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
         (method m () self)
         (def x = self))))

(test-->>G simple-field
           (term [x]))

(define uninit-request
  (term (object
         (def x = (x)))))

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
         (def y = ((x :=) self)))))

(test-->>G local-field-assign
           (term [x (x :=) y]))

(define field-assign
  (term ((object
          (var x))
         (x :=)
         (object))))

(test-->>G field-assign
           (term done))

(define done-argument
  (term ((object
          (method m (x) (x)))
         m
         done)))

(test-->>G done-argument
           (term done))

(define scoped-field
  (term ((object
          (method m () self)
          (def x = ((object
                     (def y = (m)))
                    y)))
         x)))

(test-->>G scoped-field
           (term [m x]))

(test-results)
