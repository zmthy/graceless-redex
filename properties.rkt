#lang racket

(require redex
         "graceless.rkt")

(define (typed? p)
  (let ([σ (first p)]
        [t (second p)])
    (match (judgment-holds (store-typed ,σ Σ) Σ)
      [(list Σ)
       (judgment-holds (typed ,Σ () ,t T))]
      [else #f])))

(define value? (redex-match Graceless v))
(define error? (redex-match Graceless uninitialised))

(define (reduces? p)
  (not (null? (apply-reduction-relation -->G (term ,p)))))

(define (progress? p)
  (if (typed? p)
      (or (value? (second p))
          (error? (second p))
          (reduces? p))
      #t))

(define-metafunction Graceless
  generate-type : -> T
  [(generate-type) ,(generate-term Graceless T 5)])

(define-metafunction Graceless
  count-self : Γ -> n
  [(count-self ()) 0]
  [(count-self (G ... D)) (count-self (G ...))]
  [(count-self (G ... (self → T))) ,(add1 (term (count-self (G ...))))])

(define-metafunction Graceless
  generate-self : Γ n -> [t z] ∪ #f
  [(generate-self Γ 0) #f]
  [(generate-self Γ n)
   ()
   (self )
   (where i ,(random (term (count-self Γ))))
   (select-self Γ i T)])

(define-metafunction Graceless
  generate-reference : Σ -> y
  [(generate-reference Σ) ,(random (length (term Σ)))])

(define-metafunction Graceless
  generate-assignment-pair : Σ Γ -> [t z] ∪ #f
  [(generate-assignment-pair Σ Γ) (generate-self-pair Γ)
   (side-condition (= 0 (random 2)))]
  [(generate-assignment-pair Σ Γ) (generate-reference-pair Σ)])

(define-metafunction Graceless
  build-assignment : Σ Γ ([t z] ∪ #f) -> t ∪ #f
  [(build-assignment Σ Γ [t z]) (t z ← (generate-expression Σ Γ))]
  [(build-assignment Σ Γ #f) #f])

(define-metafunction Graceless
  generate-assignment : Σ Γ -> t ∪ #f
  [(generate-assignment Σ Γ)
   (build-assignment (generate-assignment-pair Σ Γ))])

(define-metafunction Graceless
  generate-constructor : Σ Γ T -> t
  [(generate-constructor Σ Γ ⊥) uninitialised]
  [(generate-constructor Σ Γ (∨ T_1 T_2)) (generate-constructor Σ Γ T_1)
   (side-condition (= 0 (random 2)))]
  [(generate-constructor Σ Γ (∨ T_1 T_2)) (generate-constructor Σ Γ T_2)]
  [(generate-constructor Σ Γ (type D ...))
   (object (generate-method Σ Γ D) ...
           (generate-expression Σ Γ (generate-type)))])

(define-metafunction Graceless
  generate-expression : Σ Γ T -> t
  [(generate-expression Σ Γ Done) (generate-assignment Σ Γ)
   (side-condition (= 0 (random 2)))]
  [(generate-expression Σ Γ Done) done]
  [(generate-expression Σ Γ T) (generate-constructor Σ Γ T)
   (side-condition (= 0 (random 2)))]
  [(generate-expression Σ Γ T) (generate-request Σ Γ T)])

(define-metafunction Graceless
  generate-body : Σ Γ T -> o
  [(generate-body Σ Γ T) uninitialised
   (side-condition (= 0 (random 10)))]
  [(generate-body Σ Γ T) (generate-expression Σ Γ T)])

(define-metafunction Graceless
  generate-method : Σ Γ D -> d
  [(generate-method Σ (G ...) (m ([x : S] ...) → U))
   (method (m ([x : S] ...) → U)
           (generate-body Σ (G ... (x () → S) ...) U))])

(define-metafunction Graceless
  generate-object : Σ (D ...) -> (d ...)
  [(generate-object Σ (D ...))
   ((generate-method Σ Γ D) ...)
   (where Γ ((self → (type D ...))))])

(define-metafunction Graceless
  generate-store : Σ Σ -> σ
  [(generate-store Σ ((D ...) ...))
   ((generate-object Σ (D ...)) ...)])

(define-term store-type
  ,(generate-term Graceless Σ 5))

(term (generate-store store-type store-type))

(define-term empty-env
  (term ()))

;; (for ([i (term store-type)])
;;   (displayln (length i)))
;; (generate-term Graceless #:satisfying (store-typed σ Σ) 5)

;; (let ([c (make-coverage -->G)])
;;   (parameterize ([relation-coverage (list c)])
;;     (check-reduction-relation -->G (λ (p) (progress? p))))
;;   (covered-cases c))
