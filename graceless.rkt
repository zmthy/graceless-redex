#lang racket

(require redex)

;; The core syntax of Graceless.
(define-language Graceless
  (e o
     (request e m e ...)
     (request m e ...)
     self)
  (M (method m (x ...) e))
  (F (var x A))
  (A ()
     (= e)
     (:= e))
  (o (object M ... F ...))
  (m variable-not-otherwise-mentioned
     (variable-not-otherwise-mentioned :=))
  (x variable-not-otherwise-mentioned))

;; The runtime syntax of Graceless.
(define-extended-language G Graceless
  (e ....
     (assign e x e e)
     v
     uninitialised)
  (v (ref ℓ))
  ;; The complex contexts and the simple hole are separated here to allow
  ;; uninitialised to cascade without looping back on itself.
  (E⊥ (request E m e ...)
      (request v m v ... E e ...)
      (request m v ... E e ...)
      (assign v x E e))
  (E E⊥
     hole)
  (ℓ number)
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
  [(subst-self ℓ (assign e_r x e_v e_n))
   (assign (subst-self ℓ e_r) x (subst-self ℓ e_v) (subst-self ℓ e_n))]
  [(subst-self _ e) e])

;; Substitute the location ℓ as the receiver to unqualified requests in the set
;; of names ms.
(define-metafunction G
  subst : ms ℓ e -> e
  [(subst [m_l ... m m_r ...] ℓ (name o (object _ ... (method m _ _) M ...
                                                F ...)))
   (subst [m_l ... m_r ...] ℓ o)]
  [(subst [m_l ... x m_r ...] ℓ (name o (object M ...
                                                F ... (var x _) _ ...)))
   (subst [m_l ... m_r ...] ℓ o)]
  [(subst ms ℓ (object M ... F ...)) (object (subst-method ms ℓ M) ...
                                             (subst-field ms ℓ F) ...)]
  [(subst ms ℓ (request e m e_a ...))
   (request (subst ms ℓ e) m (subst ms ℓ e_a) ...)]
  [(subst (name ms [_ ... m _ ...]) ℓ (request m e ...))
   (subst ms ℓ (request (ref ℓ) m e ...))]
  [(subst ms ℓ (request m e ...)) (request m (subst ms ℓ e) ...)]
  [(subst ms ℓ (assign e_r x e_v e_n))
   (assign (subst ms ℓ e_r) x (subst ms ℓ e_v) (subst ms ℓ e_n))]
  [(subst _ _ e) e])

;; Continue subst through methods into their bodies, removing names which appear
;; in the parameter list.
(define-metafunction G
  subst-method : ms ℓ M -> M
  [(subst-method [m_l ... x m_r ...] ℓ
                 (name M (method m (_ ... x _ ...) _)))
   (subst-method [m_l ... m_r ...] ℓ M)]
  [(subst-method ms ℓ (method m (x ...) e))
   (method m (x ...) (subst ms ℓ e))])

;; Continue subst through fields into their assignments.
(define-metafunction G
  subst-field : ms ℓ F -> F
  [(subst-field ms ℓ (var x A)) (var x (subst-assign ms ℓ e))])

;; Continue subst through assignments.
(define-metafunction G
  subst-assign : ms ℓ A -> A
  [(subst-assign _ _ ()) ()]
  [(subst-assign ms ℓ (= e)) (= (subst ms ℓ e))]
  [(subst-assign ms ℓ (:= e)) (:= (subst ms ℓ e))])

;; Allocate the object o in the store, returning the newly allocated location
;; and the updated store.
(define-metafunction G
  allocate : σ o -> [ℓ σ]
  [(allocate σ o) [(fresh-location σ) (store σ o)]])

;; Store the object o.  The resulting location is the same as calculated by
;; fresh-location on the same store, before the object is added.
(define-metafunction G
  store : σ o -> σ
  [(store (o_σ ...) o) (o_σ ... o)])

;; Fetch a fresh location for the store.
(define-metafunction G
  fresh-location : σ -> ℓ
  [(fresh-location ()) 0]
  [(fresh-location (_ o ...)) ,(+ 1 (term (fresh-location (o ...))))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction G
  lookup : σ ℓ -> o
  [(lookup (o _ ...) 0) o]
  [(lookup (_ o ...) ℓ) (lookup (o ...) ,(- (term ℓ) 1))])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v.  This will fail if no such field exists in the
;; object.
(define-metafunction G
  set-field : σ ℓ x v -> σ
  [(set-field ((object M_l ... (method x () _) M_r ...) o ...) 0 x v)
   ((object M_l ... (method x () v) M_r ...) o ...)]
  [(set-field (o_l o_r ...) ℓ x v) (o_l o_p ...)
   (where (o_p ...) (set-field (o_r ...) ,(- (term ℓ) 1) x v))])

;; Convert a field to its corresponding getter and (maybe) setter methods.
(define-metafunction G
  field-methods : F -> [M ...]
  [(field-methods (var x (= _))) [(method x () uninitialised)]]
  [(field-methods (var x _))
   [(method x () uninitialised)
    (method (x :=) (y) (assign self x (request y) self))]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; methods.
(define-metafunction G
  fields-methods : [F ...] -> [M ...]
  [(fields-methods []) []]
  [(fields-methods [F F_r ...]) [M ... M_r ...]
   (where [M ...] (field-methods F))
   (where [M_r ...] (fields-methods [F_r ...]))])

;; Convert a list of fields F to a sequence of assignments to the object at
;; location ℓ, resulting in the final expression e.
(define-metafunction G
  field-assigns : ℓ [F ...] e -> e
  [(field-assigns ℓ [] e) e]
  [(field-assigns ℓ [(var x ()) F ...] e) (field-assigns ℓ [F ...] e)]
  [(field-assigns ℓ [(var x (= e_v)) F ...] e)
   (assign (ref ℓ) x e_v (field-assigns ℓ [F ...] e))]
  [(field-assigns ℓ [(var x (:= e_v)) F ...] e)
   (assign (ref ℓ) x e_v (field-assigns ℓ [F ...] e))])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   G
   #:domain [e σ]
   ;; Uninitialised terminates the program.
   (--> [(in-hole E⊥ uninitialised) σ]
        [uninitialised σ]
        uninitialised)
   ;; Allocate the object o substituting local requests to this object, and
   ;; return the resulting reference.
   (--> [(in-hole E (object (name M (method m _ _)) ...
                            (name F (var x _)) ...))
         σ]
        [(in-hole E (subst [m ... x ...] ℓ
                           (subst-self ℓ
                                       (field-assigns ℓ [F ...] (ref ℓ)))))
         σ_p]
        (where ℓ (fresh-location σ))
        (where [M_f ...] (fields-methods [F ...]))
        (where (M_p ...) (M ... M_f ...))
        (where σ_p (store σ (object (subst-method [m ... x ...] ℓ M_p) ...)))
        object)
   ;; Allocate an object with getter methods to the parameters whose bodies are
   ;; the arguments, and substitute for unqualified requests to the parameters
   ;; and for self.  Return the body of the method.
   (--> [(in-hole E (request (ref ℓ) m v ..._a)) σ]
        [(in-hole E (subst [x ...] ℓ_a (subst-self ℓ e))) σ_p]
        (where (object _ ... (method m (x ..._a) e) _ ...) (lookup σ ℓ))
        (where [ℓ_a σ_p] (allocate σ (object (method x () v) ...)))
        request)
   (--> [(in-hole E (assign (ref ℓ) x v e)) σ]
        [(in-hole E e) σ_p]
        (where σ_p (set-field σ ℓ x v))
        assign)))

;; Evaluate an expression starting with an empty store.
(define-metafunction G
  eval : e -> v or uninitialised
  [(eval e) (run [e ()])])

;; Apply the reduction relation -->G until the result is a value.
(define-metafunction G
  run : [e σ] -> v or uninitialised
  [(run [uninitialised σ]) uninitialised]
  [(run [v σ]) v]
  [(run any_pair) (run any_again)
   (where (any_again) ,(apply-reduction-relation -->G (term any_pair)))])

;; Wrap a term t into an initial program with an empty store.
(define (program t) (term [,t ()]))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Run the term t as an initial program with the reduction relation -->G.
(define (eval-->G t) (term (eval ,(program t))))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->G t) (traces -->G (program t)))

;; Examples:

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
