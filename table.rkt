#lang racket

;; This file contains tests demonstrating the behaviours of the
;; different models with respect to the columns of Table 1 in the
;; paper.
;;
;; Each test case defines an expression in Graceless, and then for
;; each model evaluates the expression and verifies that a
;; particular result is obtained. The possible results used in
;; these tests are:
;; - stuck, indicating that the evaluation could not proceed.
;; - [method names here], indicating that the resulting object
;;   has exactly the methods listed.
;; Different behaviours for a property are detected by returning
;; objects with different method sets for each case.
;;
;; Comments with each defined term, and next to each test call,
;; describe the expected behaviour in each condition. Models with
;; different behaviours are given different expected return values.
;;
;; We do not test for the -first column, as all our models are
;; objects-first, for Overload, as it is by construction, or for
;; Stable, because it is determined by the other columns.

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
                  test-->>GTU)
         (only-in (rename-in "positional-inheritance/test.rkt"
                             [test-->>GU test-->>GPU])
                  test-->>GPU))

(provide (all-defined-out))

;; Registration
;; This expression has methods "x" and "worked" if registration succeeds,
;; and only "x" if it does not.
;;
;; It assigns "self" to a field in the outer object called "registered"
;; during the initialisation of a parent, and detects whether the
;; value assigned is the parent or child object.
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

(test-->>GO registration         ;; Forwarding, delegation, and concatenation
           (term [x]))           ;; do not support registration.

(test-->>GI registration         ;; Merged and uniform identity do support
            (term [x worked]))   ;; registration.

(test-->>GMU registration        ;; Multiple uniform identity does support
             (term [x worked]))  ;; registration.

(test-->>GTU registration        ;; Method transformation multiple inheritance
             (term [x worked]))  ;; does support registration.

(test-->>GPU registration        ;; Positional inheritance does support
             (term [x worked]))  ;; registration.

;; Preëxisting
;; This expression has methods "parent" and "child" if inheritance from
;; preëxisting objects is supported, and gets stuck otherwise.
;;
;; It simply attempts to inherit from a previously-created object,
;; and succeeds when that is permitted.
(define preexisting
  (term (object
         (def parent = (object))
         (def child = (object
                       (inherits (parent)))))))

(test-->>GO preexisting            ;; Forwarding, delegation, and concatenation
            (term [parent child])) ;; support inheriting from existing objects.

(test-->>GI preexisting   ;; All other models do not.
            (term stuck))

(test-->>GMU preexisting
            (term stuck))

(test-->>GTU preexisting
            (term stuck))

(test-->>GPU preexisting
             (term stuck))

;; Downcalls during construction
;; This expression has a method "isParent" if the version of "test"
;; in the parent executes (indicating downcalls are not supported),
;; and a method "isChild" if the overriding version executes, which
;; means that downcalls are supported.
;;
;; This test attempts to make a downcall during construction,
;; defining a method "test" in both the parent and child. The version
;; in the parent assigns an object with an "isParent" method to the
;; "downcall" field in the outer object, while the version in the
;; child assigns one with "isChild". Depending on which version is
;; accessed, a different method set is on the object stored in the
;; field.
(define downcalls-during
  (term ((object
          (method parent ()
                  (object
                   (method test ()
                           ((downcall :=)
                            (object
                             (method isParent () done))))
                   (def x = (test))))
          (def child = (object
                        (inherits (parent))
                        (method test ()
                                ((downcall :=)
                                 (object
                                  (method isChild () done))))))
          (var downcall))
         downcall)))

(test-->>GO downcalls-during   ;; Forwarding, delegation, and concatenation
            (term [isParent])) ;; do not support downcalls during construction.

(test-->>GM downcalls-during   ;; Merged identity does not support downcalls
           (term [isParent]))  ;; during construction.

(test-->>GU downcalls-during   ;; Uniform identity supports downcalls during
            (term [isChild]))  ;; construction.

(test-->>GMU downcalls-during  ;; Multiple uniform supports downcalls.
             (term [isChild]))

(test-->>GTU downcalls-during  ;; Method transformation supports downcalls.
             (term [isChild]))

(test-->>GPU downcalls-during  ;; Positional supports downcalls.
             (term [isChild]))

;; Downcalls after construction
;; This expression has a method "isParent" if the version of "test"
;; in the parent executes (indicating downcalls are not supported),
;; and a method "isChild" if the overriding version executes, which
;; means that downcalls are supported.
;;
;; This test attempts to make a downcall after construction is done,
;; defining a method "test" in both the parent and child. The version
;; in the parent assigns an object with an "isParent" method to the
;; "downcall" field in the outer object, while the version in the
;; child assigns one with "isChild". The "try" method in the parent
;; calls test: if downcalls are supported, the child version of
;; "test" runs. The expression calls "try" on the child object and
;; measures the effect on the field.
(define downcalls-after
  (term ((object
          (method parent ()
                  (object
                   (method test ()
                           ((downcall :=)
                            (object
                             (method isParent () done))))
                   (method try () (test))))
          (def child = (object
                        (inherits (parent))
                        (method test ()
                                ((downcall :=)
                                 (object
                                  (method isChild () done))))))
          (def x = ((child) try))
          (var downcall))
         downcall)))

(test-->>GF downcalls-after    ;; Forwarding does not support downcalls even
            (term [isParent])) ;; after construction.

(test-->>GD downcalls-after    ;; All other models support downcalls after
            (term [isChild]))  ;; construction.

(test-->>GC downcalls-after
            (term [isChild]))

(test-->>GI downcalls-after
            (term [isChild]))

(test-->>GMU downcalls-after
             (term [isChild]))

(test-->>GTU downcalls-after
             (term [isChild]))

(test-->>GPU downcalls-after
             (term [isChild]))

;; Action at a distance, downwards
;; This expression has a method "distance" if action at a distance allows
;; modifying the child by modifying the parent, no methods if it does not,
;; and is stuck if no independent reference to the parent can exist.
;;
;; This expression externally mutates a field in the parent object and
;; reads that field through the child.
(define distance-down
  (term (((object
           (def parent = (object
                          (var x := (object))))
           (def child = (object
                         (inherits (parent))))
           (def y = ((parent)
                     (x :=)
                     (object
                      (method distance () done)))))
          child)
         x)))

(test-->>GF distance-down      ;; Forwarding shows action at a distance
            (term [distance])) ;; from parent to child.

(test-->>GD distance-down      ;; Delegation shows action at a distance
            (term [distance])) ;; from parent to child.

(test-->>GC distance-down      ;; Concatenation does not show action at
            (term []))         ;; a distance downwards.

(test-->>GI distance-down      ;; All other models do not allow the
            (term stuck))      ;; circumstance to arise in the first place.

(test-->>GMU distance-down
             (term stuck))

(test-->>GTU distance-down
             (term stuck))

(test-->>GPU distance-down
             (term stuck))

;; Action at a distance, upwards
;; This expression has a method "distance" if action at a distance allows
;; modifying the parent by modifying the child, no methods if it does not,
;; and is stuck if no independent reference to the parent can exist.
;;
;; This test assigns to an inherited field inside the child, and tests
;; whether the value of the field in the parent has been updated also.
(define distance-up
  (term (((object
           (def parent =
             (object
              (var x := (object))))
           (def child =
             (object
              (inherits (parent))
              (def y = ((x :=)
                        (object
                         (method distance () done)))))))
          parent)
         x)))

(test-->>GF distance-up        ;; Forwarding shows action at a distance
            (term [distance])) ;; from child to parent.

(test-->>GD distance-up        ;; Delegation shows action at a distance
            (term [distance])) ;; from child to parent.

(test-->>GC distance-up        ;; Concatenation does not show action at
            (term []))         ;; a distance from child to parent.

(test-->>GI distance-up        ;; All other models do not allow the
            (term stuck))      ;; circumstance to arise in the first place.

(test-->>GMU distance-up
             (term stuck))

(test-->>GTU distance-up
            (term stuck))

(test-->>GPU distance-up
             (term stuck))

;; Multiple inheritance without custom syntax.
;; This expression succeeds if multiple inheritance is supported.
(define multiple-inheritance
  (term ((object
          (method parent1 ()
                  (object
                   (method from1 () done)))
          (method parent2 ()
                  (object
                   (method from2 () done)))
          (def child = (object
                        (inherits (parent1))
                        (inherits (parent2)))))
         child)))

(test-->>GMU multiple-inheritance  ;; Multiple uniform supports multiple
            (term [from1 from2]))  ;; inheritance with optional "as" clauses.

(test-->>GTU multiple-inheritance  ;; Transform supports multiple inheritance
             (term [from1 from2])) ;; with optional transform clauses.

(test-->>GPU multiple-inheritance  ;; Positional supports multiple inheritance
            (term [from1 from2]))  ;; with optional "as" clauses.

;; Inheriting from something inherited from a parent.
;; This expression has methods "from2", "subparent", and "fromsubparent"
;; if it is possible to inherit from something you have yourself obtained
;; through inheritance, and gets stuck otherwise.
;;
;; Method parent1 returns an object with an inheritable "subparent"
;; method. The child object first inherits from parent1, and then tries
;; to inherit from subparent. This is only permitted in the positional
;; system, as in all others inheritance is resolved before it is possible
;; to make a selfcall.
(define parent-inheritance
  (term ((object
          (method parent1 ()
                  (object
                   (method subparent ()
                           (object
                             (method fromsubparent () done)))))
          (method parent2 ()
                  (object
                   (method from2 () done)))
          (def child = (object
                        (inherits (parent1))
                        (inherits (subparent))
                        (inherits (parent2)))))
         child)))

(test-->>GMU parent-inheritance ;; Multiple uniform does not allow inheriting
            (term stuck))       ;; from something acquired from a parent.

(test-->>GTU parent-inheritance ;; Method transformation does not allow
             (term stuck))      ;; parent inheritance.

(test-->>GPU parent-inheritance ;; Positional does.
            (term [from2 subparent fromsubparent]))

(test-results)
