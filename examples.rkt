#lang racket

(require redex)
(require "graceless.rkt")

(provide (all-defined-out))

(define simple-object
  (term (object)))

(define simple-method
  (term (object
          (method m ()
                  self))))

(define simple-request
  (term (request
          (object
           (method m (x)
                   (request x)))
          m
          (object))))

(define scoped
  (term (request
          (object
           (method m (x)
                   (object
                    (method m (x)
                            (request x)))))
          m
          (object))))

(define multiple-args
  (term (request
          (object
           (method const
                   (x y)
                   (request y)))
          const
          (object)
          (object))))

(define local-request
  (term (request
          (object
           (method first ()
                   (request second))
           (method second ()
                   self))
          first)))

(define simple-field
  (term (object
          (var x (= self)))))

(define method-and-field
  (term (object
          (method m ()
                  self)
          (var x (= self)))))

(define uninit-request
  (term (object
          (method val ()
                  (request x))
          (var x (= (request val))))))

(define mutable-field
  (term (object
         (var x))))

(define field-assign
  (term (request
         (object
          (var x))
         (x :=)
         (object))))
