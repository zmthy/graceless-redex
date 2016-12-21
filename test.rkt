#lang racket

(require redex
         "graceless.rkt")

(provide test-->>G
         (all-from-out "graceless.rkt"))

;; Test if a term is a 'result', that is either a value or a raise of a value.
(define-metafunction Graceless
  value? : t -> boolean
  [(value? v) #t]
  [(value? _) #f])

;; Test if a term is a raise of some value.
(define-metafunction Graceless
  raise-value? : t -> boolean
  [(raise-value? (↥ v)) #t]
  [(raise-value? _)     #f])

;; Test if a program has the given type.
(define-metafunction Graceless
  program-typed? : any any -> boolean
  [(program-typed? p     S)   (program-typed? p (⋃ S))]
  [(program-typed? p     (T)) (program-typed? p T)]
  [(program-typed? [σ t] T)   ,(judgment-holds (has-type Γ t T))
   (where (Γ) ,(judgment-holds (assign-env σ Γ) Γ))]
  [(program-typed? any   p)   (program-typed? p any)]
  [(program-typed? _     _)   #f])

;; Assign a term a type, failing if not well-typed.
(define-metafunction Graceless
  term-type : t -> (T ...)
  [(term-type t) ,(judgment-holds (assign-type () t T) T)])

;; Test if the result of an execution matches the expected output.
(define-metafunction Graceless
  result-match? : any any -> boolean
  [(result-match? [σ t] stuck) (not (or (value? t) (raise-value? t)))]
  [(result-match? [σ t] raise) (raise-value? t)]
  [(result-match? [σ t] t)     #t]
  [(result-match? [σ v] any)   (program-typed? [σ v] any)]
  [(result-match? any   p)     (result-match? p any)])

;; Test that the first term reduces to the state described in the second, and
;; that the type of the resulting reduction matches the type assigned to the
;; first term.  The second form may be a term, an expected type, or the special
;; terms 'stuck', indicating a non-result that is not a redex; and 'raise',
;; indicating a raise of any value.
(define-syntax-rule (test-->>G t r)
  (begin
    (test-->>
     -->G
     #:equiv (λ (a b) (term (program-typed? ,a ,b)))
     (program (term t))
     (term (term-type t)))
    (test-->>
     -->G
     #:equiv (λ (a b) (term (result-match? ,a ,b)))
     (program (term t))
     (term r))))
