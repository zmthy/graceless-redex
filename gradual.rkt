#lang racket

(require redex)

(require "graceless.rkt"
         (prefix-in pre: "graceless.rkt"))

(provide (all-defined-out))

(define-extended-language Graceless? Graceless
  ;; Types extended with the gradual type, and structural types which can now be
  ;; exact and/or have a gradual row.
  (T ....
     ?
     (typeτδ D ...))
  ;; This allows us to match on the existing type syntax while adding the two
  ;; new forms of structural type.  We have to extrapolate each possible
  ;; combination of variability into a different non-terminal in order to match
  ;; on the same sort of patterns used in the paper rules.
  (typeτδ type
          type!
          type?)
  ;; A type that is inexact but may have a gradual row.
  (typeδ type
         type?)
  ;; A type that may be exact but has no gradual row.
  (typeτ type
         type!)
  ;; We could also do with a pattern to match exact types.
  (T! ⊥
      Done
      (type! D ...))
  ;; Terms extended with casts and match/case.
  (t ....
     (t ∷ T)
     (match t (case z : T → t) ...))
  ;; Intrinsically-typed term.
  (tt (t T))
  ;; Intrinsically-typed simple value.
  (ut (v T))
  ;; Intrinsically-typed value.
  (vt u
      (u ∷ T))
  ;; Evaluation outcome.
  (o tt
     uninitialised
     blame))

;; Intersection between inexact structural types keeps any gradual row.
(define-metafunction Graceless?
  ∧-δ : typeδ typeδ -> typeδ
  ;; No gradual row.
  [(∧-δ type type) type]
  ;; Must be a gradual row.
  [(∧-δ _ _) type?])

;; Extend intersection to include the gradual extensions.
(define-metafunction/extension pre:∧ Graceless?
  ∧ : T T -> T
  ;; Unknown doesn't affect types we already know everything about.
  [(∧ ? T!) T!]
  [(∧ T! ?) T!]
  ;; Two exact types must contain the same information.
  [(∧ (type! D_1 ...) (type! D_2 ...)) (type! D_1 ...)
   (side-condition (equal? (list->set (term (D_1 ...)))
                           (list->set (term (D_2 ...)))))]
  ;; Otherwise they resolve to bottom.
  [(∧ (type! _ ...) (type! _ ...)) ⊥]
  ;; Exact types subsume structural types if there is no new information.
  [(∧ (type! D_1 ...) (type D_2 ...)) (type! D_1 ...)
   (side-condition (andmap (λ (D2)
                             (ormap (λ (D1)
                                      (judgment-holds (subsig ,D1 ,D2)))
                                    (term (D_1 ...))))
                           (term (D_2 ...))))]
  [(∧ (type D_1 ...) (type! D_2 ...)) (type! D_2 ...)
   (side-condition (andmap (λ (D1)
                             (ormap (λ (D2)
                                      (judgment-holds (subsig ,D2 ,D1)))
                                    (term (D_2 ...))))
                           (term (D_1 ...))))]
  ;; Any other combination with an exact type fails.
  [(∧ (type! _ ...) T) ⊥]
  [(∧ T (type! _ ...)) ⊥]
  ;; Combining the unknown type with a structural type adds a gradual row,
  ;; regardless of what was there before.
  [(∧ (typeδ D ...) ?) (type? D ...)]
  [(∧ ? (typeδ D ...)) (type? D ...)]
  ;; Structural types join their signatures together, keeping a gradual row if
  ;; it is present on either side.  This subsumes the original structural rule.
  [(∧ (typeδ_1 D_1 ...) (typeδ_2 D_2 ...)) ((∧-δ typeδ_1 typeδ_2) D ...)
   (where (D ...) (∧-sig (D_1 ...) (D_2 ...)))])

;; Extend signature intersection to use the extended intersection.
(define-metafunction/extension pre:∧-sig Graceless?
  ∧-sig : (D ...) (D ...) -> (D ...)
  ;; Intersect signatures with a matching identity.  There's guaranteed to be at
  ;; most one match by the well-formedness properties of structural types.
  [(∧-sig ((m ([x_1 : S_1] ..._x) → U_1) D_1 ...)
          (D_2 ... (m ([x_2 : S_2] ..._x) → U_2) D_3 ...))
   ((m ([x_1 : (∨ S_1 S_2)] ...) → (∧ U_1 U_2)) D ...)
   (where (D ...) (∧-sig (D_1 ...) (D_2 ... D_3 ...)))]
  ;; Copy this over as well to avoid reapplying the old form of the rule above.
  [(∧-sig (D_1 D_2 ...) (D_3 ...)) (D_1 D ...)
   (where (D ...) (∧-sig (D_2 ...) (D_3 ...)))])

(define -->G
  (reduction-relation
   Graceless?
   #:domain [σ o]
   #:arrow :-->
   ;; (-->c (v ∷ T) v
   ;;       Irrelevant)
   (--> [σ ])
   with [(:--> (in-hole E fst) (in-hole E snd))
         (--> fst snd)]))

;; (define -->G
;;   (extend-reduction-relation
;;    pre:-->G
;;    Graceless?
;;    #:domain [σ o]
;;    #:arrow :-->
;;    ;; Blame the label if the coercion is unsatisfiable.
;;    (:--> [σ (u [⊥ ℓ])]
;;          [σ (blame ℓ)]
;;          Blame)
;;    ;; Remove an irrelevant coercion through unknown.
;;    (-->c [σ ((u [T !]) [T ? ℓ])]
;;          [σ u]
;;          Irrelevant)
;;    ;; Split a coercion composition into its component coercions.
;;    (-->c [σ ((u ))]
;;          [σ ([U ⇐ (∧ T_1 T_2) ═ S] t)]
;;          Split)
;;    with [(:--> (in-hole F fst) (in-hold F snd))
;;          (-->c fst snd)]))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->G t) (traces -->G (program t)))
