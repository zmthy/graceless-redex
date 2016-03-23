#lang racket

(require redex
         (only-in "single-inheritance/test.rkt"
                  test-->>GF
                  test-->>GD
                  test-->>GC
                  test-->>GO
                  test-->>GM
                  test-->>GU
                  test-->>GI)
         (only-in (rename-in "multiple-inheritance/test.rkt"
                             [test-->>GU test-->>GMU])
                  test-->>GMU)
         (only-in (rename-in "transform-inheritance/test.rkt"
                             [test-->>GU test-->>GTU])
                  test-->>GTU))

(provide (all-defined-out))

;; Registration
(define registration
  (term ((object
          (method parent ()
                  (object
                   (def x = ((registered :=) self))))
          (var registered)
          (def x = (object
                    (inherits (parent))
                    (method worked () done))))
         registered)))

(test-->>GO registration
           (term [x]))

(test-->>GI registration
            (term [x worked]))

;; Preëxisting
(define preexisting
  (term (object
         (def parent = (object))
         (def child = (object
                       (inherits (parent)))))))

(test-->>GO preexisting
            (term [parent child]))

(test-->>GI preexisting
            (term stuck))

;; Downcalls during construction
(define downcalls-during
  (term ((object
          (method parent ()
                  (object
                   (method test ()
                           ((downcall :=)
                            (object
                             (method isParent () done))))
                   (def x = (test))))
          (def child =
            (object
             (inherits (parent))
             (method test ()
                     ((downcall :=)
                      (object
                       (method isChild () done))))))
          (var downcall))
         downcall)))

(test-->>GO downcalls-during
            (term [isParent]))

(test-->>GM downcalls-during
           (term [isParent]))

(test-->>GU downcalls-during
            (term [isChild]))

;; Downcalls after construction
(define downcalls-after
  (term ((object
          (method parent ()
                  (object
                   (method test ()
                           ((downcall :=)
                            (object
                             (method isParent () done))))
                   (method try () (test))))
          (def child =
            (object
             (inherits (parent))
             (method test ()
                     ((downcall :=)
                      (object
                       (method isChild () done))))))
          (def x = ((child) try))
          (var downcall))
         downcall)))

(test-->>GF downcalls-after
            (term [isParent]))

(test-->>GD downcalls-after
            (term [isChild]))

(test-->>GC downcalls-after
            (term [isChild]))

(test-->>GI downcalls-after
            (term [isChild]))

;; Action at a distance, downwards
(define distance-down
  (term (((object
           (def parent =
             (object
              (var x := (object))))
           (def child =
             (object
              (inherits (parent))))
           (def y =
             ((parent)
              (x :=)
              (object
               (method distance () done)))))
          child)
         x)))

(test-->>GF distance-down
            (term [distance]))

(test-->>GD distance-down
            (term [distance]))

(test-->>GC distance-down
            (term []))

(test-->>GI distance-down
            (term stuck))

;; Action at a distance, upwards
(define distance-up
  (term (((object
           (def parent =
             (object
              (var x := (object))))
           (def child =
             (object
              (inherits (parent))
              (def y =
                ((x :=)
                 (object
                  (method distance () done)))))))
          parent)
         x)))

(test-->>GF distance-up
            (term [distance]))

(test-->>GD distance-up
            (term [distance]))

(test-->>GC distance-up
            (term []))

(test-->>GI distance-up
            (term stuck))

;; Multiple inheritance with the standard syntax.
(define multiple-inheritance
  (term ((object
          (method parent1 ()
                  (object
                   (method from1 () done)))
          (method parent2 ()
                  (object
                   (method from2 () done)))
          (def child =
            (object
             (inherits (parent1) as x)
             (inherits (parent2) as y))))
         child)))

(test-->>GMU multiple-inheritance
            (term [from1 from2]))

;; Multiple inheritance with the method transformation syntax.
(define transform-inheritance
  (term ((object
          (method parent1 ()
                  (object
                   (method from1 () done)))
          (method parent2 ()
                  (object
                   (method from2 () done)))
          (def child =
            (object
             (inherits (parent1))
             (inherits (parent2)))))
         child)))

(test-->>GTU transform-inheritance
             (term [from1 from2]))

(test-results)
