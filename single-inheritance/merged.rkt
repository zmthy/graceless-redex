#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with merged identity
;; inheritance.
(define -->GM
  (extend-reduction-relation
   -->GPF
   GM
   #:domain p
   ;; Concatenate the new definitions into the inherited object's store
   ;; location (removing overrides), and return the inheriting object's body.
   (--> [σ (in-hole E (object (inherits (ref ℓ) s_d ...) M ... S ...))]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and original fields.  The new super object contains just the
        ;; methods that were in the object when it was inherited from, and not
        ;; its fields.
        [(store-at (store σ (object M_u ...))
                   ℓ (object F ...
                             M_up ...
                             (subst-method s ...
                                           [(self 0) / m] ...
                                           [ℓ_u as (self 0) / (super 0)] M) ...
                             M_f ...))
         ;; We also have to process the actual object expression as well.
         (in-hole E (seq (subst s ...
                                [ℓ / (self 0)]
                                [(self 0) / m] ...
                                [ℓ_u as (self 0) / (super 0)]
                                e) ...
                                (ref ℓ)))]
        ;; Lookup the super object, fetching both its methods and method names.
        (where (object F ... M_u ...) (lookup σ ℓ))
        ;; Fetch a fresh location.
        (where ℓ_u (fresh-location σ))
        ;; Collect the names of the definitions in the inheriting object.
        (where (m_d ...) (names M ... S ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object.
        (where (M_up ...) (override M_u ... m_d ...))
        ;; Fetch the names of all the methods in the resulting object.
        (where (m ...) ,(append (term (m_d ...))
                                (term (names M_up ...))))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S ...)))
        ;; Collect the field accessor methods and the resulting object body.
        (where (M_f ... e ...) (body [S y] ...))
        ;; Remove the shadowed substitutions before applying them to the body.
        (where (s ...) (all-object-shadows s_d ... (M_up ...)))
        inherits/merged)))

;; Progress the program p by one step with the reduction relation -->GM.
(define (step-->GM p) (apply-reduction-relation -->GM p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GM until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GM (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GM,
;; returning the resulting object, stuck program, or error.
(define (eval-->GM t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GM,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GM t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GM.
(define (traces-->GM t) (traces -->GM (program t)))
