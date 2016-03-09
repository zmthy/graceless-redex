#lang racket

(require redex)
(require "graceless.rkt")

(provide (all-defined-out))

(define-metafunction G
  names : Ms -> ms
  [(names [(method m _ _ ... _) ...]) [m ...]])

(define-metafunction G
  result-equiv : any any -> boolean
  [(result-equiv [(ref ℓ) σ] ms) #t
   (where ms (names (lookup σ ℓ)))]
  [(result-equiv ms [(ref ℓ) σ]) #t
   (where ms (names (lookup σ ℓ)))]
  [(result-equiv [e σ] e) #t]
  [(result-equiv e [e σ]) #t]
  [(result-equiv _ _) #f])

(define (test-->>G t r)
  (test-->>
   -->G
   #:equiv (λ (a b) (term (result-equiv ,a ,b)))
   (program t)
   r))

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
  (term (request
          (object
           (method m (x)
                   (request x)))
          m
          (object))))

(test-->>G simple-request
           (term []))

(define scoped
  (term (request
          (object
           (method m (x)
                   (object
                    (method m (x)
                            (request x)))))
          m
          (object))))

(test-->>G scoped
           (term [m]))

(define multiple-args
  (term (request
          (object
           (method const
                   (x y)
                   (request y)))
          const
          (object)
          (object))))

(test-->>G multiple-args
           (term []))

(define local-request
  (term (request
          (object
           (method first ()
                   (request second))
           (method second ()
                   self))
          first)))

(test-->>G local-request
           (term [first second]))

(define simple-field
  (term (object
          (var x (= self)))))

(test-->>G simple-field
           (term [x]))

(define method-and-field
  (term (object
          (method m ()
                  self)
          (var x (= self)))))

(test-->>G simple-field
           (term [x]))

(define uninit-request
  (term (object
          (method val ()
                  (request x))
          (var x (= (request val))))))

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
         (var y (= (request (x :=) self))))))

(test-->>G local-field-assign
           (term [x (x :=) y]))

(define field-assign
  (term (request
         (object
          (var x))
         (x :=)
         (object))))

(test-->>G field-assign
           (term []))

(define local-variable
  (term (request
         (object
          (method m ()
                  (var x (= self))
                  (request x)))
         m)))

(test-->>G local-variable
           (term [m]))

(define local-mutable-variable
  (term (request
         (object
          (method m ()
                  (var x)
                  (request (x :=) self)))
         m)))

(test-->>G local-mutable-variable
            (term [m]))
