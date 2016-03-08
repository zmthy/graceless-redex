#lang racket

(require redex)

;; The core syntax of Graceless.
(define-language Graceless
  (e (object M ...)
     (request e m e ...)
     (request m e ...)
     self)
  (M (method m (x ...) e))
  (m variable-not-otherwise-mentioned
     (variable-not-otherwise-mentioned :=))
  (x variable-not-otherwise-mentioned))

;; The runtime syntax of Graceless.
(define-extended-language G Graceless
  (E (request E m e ...)
     (request v m v ... E e ...)
     (request m v ... E e ...)
     hole)
  (e ....
     v)
  (v (ref ℓ))
  (ℓ number)
  (o (object M ...))
  (σ (o ...))
  (ms [m ...]))

;; Substitute the location ℓ as a reference for the locally defined self,
;; stopping at nested object expressions.
(define-metafunction G
  subst-self : ℓ e -> e
  [(subst-self ℓ self) (ref ℓ)]
  [(subst-self ℓ (request e m e_a ...))
   (request (subst-self ℓ e) m (subst-self ℓ e_a) ...)]
  [(subst-self ℓ (request m e ...)) (request m (subst-self ℓ e) ...)]
  [(subst-self _ e) e])

;; Substitute the location ℓ as the receiver to unqualified requests in the set
;; of names ms.
(define-metafunction G
  subst : ms ℓ e -> e
  [(subst ms ℓ (object M ...)) (object (subst-method ms ℓ M) ...)]
  [(subst ms ℓ (request e m e_a ...))
   (request (subst ms ℓ e) m (subst ms ℓ e_a) ...)]
  [(subst (name ms [_ ... m _ ...]) ℓ (request m e ...))
   (subst ms ℓ (request (ref ℓ) m e ...))]
  [(subst ms ℓ (request m e ...)) (request m (subst ms ℓ e) ...)]
  [(subst _ _ e) e])

;; Continue subst through methods into their bodies, removing names which appear
;; in the parameter list.
(define-metafunction G
  subst-method : ms ℓ M -> M
  [(subst-method [m_l ... x m_r ...] ℓ
                 (name M (method m (_ ... x _ ...) e)))
   (subst-method [m_l ... m_r ...] ℓ M)]
  [(subst-method ms ℓ (method m (x ...) e)) (method m (x ...) (subst ms ℓ e))])

;; Allocate the object o in the store, returning the newly allocated location
;; and the updated store.
(define-metafunction G
  allocate : σ o -> [ℓ σ]
  [(allocate (name σ (o_σ ...)) o) [(store-size σ) (o_σ ... o)]])

;; Calculate the size of the store.
(define-metafunction G
  store-size : σ -> ℓ
  [(store-size ()) 0]
  [(store-size (_ o ...)) ,(+ 1 (term (store-size (o ...))))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction G
  lookup : σ ℓ -> o
  [(lookup (o _ ...) 0) o]
  [(lookup (_ o ...) ℓ) (lookup (o ...) ,(- (term ℓ) 1))])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   G
   #:domain [e σ]
   ;; Allocate the object o and return the resulting reference.
   (--> [(in-hole E o) σ]
        [(in-hole E (ref ℓ)) σ_p]
        (where [ℓ σ_p] (allocate σ o))
        object)
   ;; Allocate an object with getter methods to the parameters whose bodies are
   ;; the arguments, and substitute for unqualified requests to the parameters
   ;; and for self.  Return the body of the method.
   (--> [(in-hole E (request (ref ℓ) m v ...)) σ]
        [(in-hole E (subst [x ...] ℓ_a (subst-self ℓ e))) σ_p]
        (where (object _ ... (method m (x ...) e) _ ...) (lookup σ ℓ))
        (where [ℓ_a σ_p] (allocate σ (object (method x () v) ...)))
        request)))

;; Evaluate an expression starting with an empty store.
(define-metafunction G
  eval : e -> v
  [(eval e) (run [e ()])])

;; Apply the reduction relation -->G until the result is a value.
(define-metafunction G
  run : [e σ] -> v
  [(run [v σ]) v]
  [(run any_pair) (run any_again)
   (where (any_again) ,(apply-reduction-relation -->G (term any_pair)))])

;; Progress the term t by one step with the reduction relation -->G.
(define (step t) (apply-reduction-relation -->G t))

;; Examples:

(define simple-object (term [(object) ()]))

(define simple-request (term [(request (object
                                        (method m (x)
                                                (request x)))
                                       m (object)) ()]))

(define scoped (term [(request (object
                                (method m (x)
                                        (object
                                         (method m (x)
                                                 (request x)))))
                               m
                               (object))
                      ()]))

(define multiple-args (term [(request (object
                                       (method const
                                               (x y)
                                               (request y)))
                                      const
                                      (object)
                                      (object))
                             ()]))
