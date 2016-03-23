#lang racket

(require redex
         "test.rkt")

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

;; Multiple inheritance
(define multiple-inheritance
  (term (request
         (object
          (method parent1 ()
                  (object
                   (method from1 ())))
          (method parent2 ()
                  (object
                   (method from2 ())))
          (def child =
            (object
             (inherits (request parent1))
             (inherits (request parent2)))))
         child)))

;; We don't bother testing the single inheritance systems here, as this isn't
;; valid syntax for them.

(test-results)
