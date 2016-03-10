#lang racket

(require redex)
(require (only-in "graceless.rkt"
                  Graceless
                  G
                  program))

(provide (all-defined-out)
         program)

(define-extended-language Graceless-Inheritance Graceless
  (o ....
     (object I M ... F ...))
  (I (inherits e)))

(define-union-language GIU Graceless-Inheritance G)

(define-extended-language GI GIU
  (I (s ... inherits e))
  (s [ℓ m ...]
     [x v])
  (E⊥ ....
      (object (s ... inherits E) M ... F ...)))

(define-metafunction GI
  override : M ... m ... -> [M ...]
  [(override m ...) []]
  [(override (method m _ _) M ... m_l ... m m_r ...)
   (override M ... m_l ... m m_r ...)]
  [(override M M_i ... m ...) [M M_p ...]
   (where [M_p ...] (override M_i ... m ...))])

;; Perform the substitutions s through the methods and fields M and F, in the
;; order they're provided.
(define-metafunction GI
  subst-inherits : s ... M ... F ... -> [M ... F ...]
  [(subst-inherits M ... F ...) [M ... F ...]]
  [(subst-inherits [x v] s ... M ... F ...) [M_q ... F_q ...]
   (where (object M_p ... F_p ...) (subst [x v] (object M ... F ...)))
   (where [M_q ... F_q ...] (subst-inherits s ... M_p ... F_p ...))]
  [(subst-inherits [ℓ m ...] s ... M ... F ...) [M_q ... F_q ...]
   (where (object M_p ... F_p ...) (subst-rec ℓ m ... (object M ... F ...)))
   (where [M_q ... F_q ...] (subst-inherits s ... M_p ... F_p ...))])

;; Perform an object substitution in the expression e, replacing local
;; references to self and qualifying local requests to ℓ.
(define-metafunction GI
  subst-object : ℓ m ... e -> e
  [(subst-object ℓ m ... e) (subst-rec ℓ m ... (subst-self ℓ e))])

;; Perform a request substitution in the expression e, replacing local
;; references to self with ℓ and unqualified requests to each x with the
;; corresponding v.
(define-metafunction GI
  subst-request : ℓ [x v] ... e -> e
  [(subst-request ℓ [x v] ... e) (subst [x v] ... (subst-self ℓ e))])

;; Substitute local requests for self and its methods in the method M.
(define-metafunction GI
  subst-self-rec-method : ℓ m ... M -> M
  [(subst-self-rec-method ℓ m_s ... (method m (x ...) e))
   (subst-rec-method ℓ m_s ... (method m (x ...) (subst-self ℓ e)))])

;; Substitute any local request for each x with the corresponding v.
(define-metafunction GI
  subst : [x v] ... e -> e
  [(subst [x v] ... (object (s ... inherits e) M ... F ...))
   (object ([x v] ... s ... inherits (subst [x v] ... e)) M ... F ...)]
  [(subst [x_l v_l] ... [x _] [x_r v_r] ...
          (name o (object _ ... (method x _ _) _ ...)))
   (subst [x_l v_l] ... [x_r v_r] ... o)]
  [(subst [x_l v_l] ... [x _] [x_r v_r] ...
          (name o (object _ ... F _ ...)))
   (subst [x_l v_l] ... [x_r v_r] ... o)
   (where [x _ ...] (field-names F))]
  [(subst [x v] ... (object M ... F ...))
   (object (subst-method [x v] ... M) ... (subst-field [x v] ... F) ...)]
  [(subst [x v] ... (request e m e_a ...))
   (request (subst [x v] ... e) m (subst [x v] ... e_a) ...)]
  [(subst _ ... [x v] _ ... (request x)) v]
  [(subst [x v] ... (request m e ...)) (request m (subst [x v] ... e) ...)]
  [(subst [x v] ... (assign e x_a e_a e_n))
   (assign (subst [x v] ... e)
           x_a
           (subst [x v] ... e_a)
           (subst [x v] ... e_n))]
  [(subst _ ... e) e])

;; Continue subst through methods into method bodies, removing names which
;; appear in the parameter list.
(define-metafunction GI
  subst-method : [x v] ... M -> M
  [(subst-method [x_l v_l] ... [x v] [x_r v_r] ...
                 (name M (method _ (_ ... x _ ...) _)))
   (subst-method [x_l v_l] ... [x_r v_r] ... M)]
  [(subst-method [x_s v] ... (method m (x ...) e))
   (method m (x ...) (subst [x_s v] ... e))])

;; Continue subst through fields into their assignments.
(define-metafunction GI
  subst-field : [x v] ... F -> F
  [(subst-field [x_s v] ... (def x = e)) (def x = (subst [x_s v] ... e))]
  [(subst-field _ ... (var x)) (var x)]
  [(subst-field [x_s v] ... (var x := e)) (var x := (subst [x_s v] ... e))])

;; Substitute the location ℓ as a reference for the locally defined self,
;; stopping at nested object expressions.
(define-metafunction GI
  subst-self : ℓ e -> e
  [(subst-self ℓ (object (s ... inherits e) M ... F ...))
   (object (s ... inherits (subst-self ℓ e)) M ... F ...)]
  [(subst-self ℓ (request e m e_a ...))
   (request (subst-self ℓ e) m (subst-self ℓ e_a) ...)]
  [(subst-self ℓ (request m e ...)) (request m (subst-self ℓ e) ...)]
  [(subst-self ℓ (assign e_r x e_v e_n))
   (assign (subst-self ℓ e_r) x (subst-self ℓ e_v) (subst-self ℓ e_n))]
  [(subst-self ℓ self) (ref ℓ)]
  [(subst-self _ e) e])

;; Substitute the location ℓ as the receiver to unqualified requests in the set
;; of names m.
(define-metafunction GI
  subst-rec : ℓ m ... e -> e
  [(subst-rec ℓ m ... (object (s ... inherits e) M ... F ...))
   (object ([ℓ m ...] s ... inherits (subst-rec ℓ m ... e)) M ... F ...)]
  [(subst-rec ℓ m_l ... m m_r ... (name o (object _ ... (method m _ _) _ ...)))
   (subst-rec ℓ m_l ... m_r ... o)]
  [(subst-rec ℓ m_l ... x m_r ... (name o (object _ ... F _ ...)))
   (subst-rec ℓ m_l ... m_r ... o)
   (where [x _ ...] (field-names F))]
  [(subst-rec ℓ m ... (object M ... F ...))
   (object (subst-rec-method ℓ m ... M) ...
           (subst-rec-field ℓ m ... F) ...)]
  [(subst-rec ℓ m_s ... (request e m e_a ...))
   (request (subst-rec ℓ m_s ... e) m (subst-rec ℓ m_s ... e_a) ...)]
  [(subst-rec ℓ m_l ... m m_r ... (request m e ...))
   (subst-rec ℓ m_l ... m m_r ... (request (ref ℓ) m e ...))]
  [(subst-rec ℓ m_s ... (request m e ...))
   (request m (subst-rec ℓ m_s ... e) ...)]
  [(subst-rec ℓ m ... (assign e_r x e_v e_n))
   (assign (subst-rec ℓ m ... e_r)
           x
           (subst-rec ℓ m ... e_v)
           (subst-rec ℓ m ... e_n))]
  [(subst-rec _ ... e) e])

;; Continue subst-rec through methods into their bodies, removing names which
;; appear in the parameter list.
(define-metafunction GI
  subst-rec-method : ℓ m ... M -> M
  [(subst-rec-method ℓ m_l ... x m_r ...
                 (name M (method m (_ ... x _ ...) _)))
   (subst-rec-method ℓ m_l ... m_r ... M)]
  [(subst-rec-method ℓ m_s ... (method m (x ...) e))
   (method m (x ...) (subst-rec ℓ m_s ... e))])

;; Continue subst through fields into their assignments.
(define-metafunction GI
  subst-rec-field : ℓ m ... F -> F
  [(subst-rec-field ℓ m ... (def x = e)) (def x = (subst-rec ℓ m ... e))]
  [(subst-rec-field ℓ m ... (var x)) (var x)]
  [(subst-rec-field ℓ m ... (var x := e)) (var x := (subst-rec ℓ m ... e))])

;; Allocate the object o in the store, returning the newly allocated location
;; and the updated store.
(define-metafunction GI
  allocate : σ [M ...] -> [ℓ σ]
  [(allocate σ [M ...]) [(fresh-location σ) (store σ [M ...])]])

;; Store the object o.  The resulting location is the same as calculated by
;; fresh-location on the same store, before the object is added.
(define-metafunction GI
  store : σ [M ...] -> σ
  [(store ([M_σ ...] ...) [M ...]) ([M_σ ...] ... [M ...])])

;; Fetch a fresh location for the store.
(define-metafunction GI
  fresh-location : σ -> ℓ
  [(fresh-location σ) ,(length (term σ))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction GI
  lookup : σ ℓ -> [M ...]
  [(lookup σ ℓ) ,(list-ref (term σ) (term ℓ))])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v. This will fail if no field named x in the object.
(define-metafunction GI
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (Ms) (term (update-method ,Ms x v))))])

;; Set the method named x in the method list of M to return the value v.  This
;; will fail if there is no field named x in the object.
(define-metafunction GI
  update-method : [M ...] x v -> [M ...]
  [(update-method [M_l ... (method x () _) M_r ...] x v)
   [M_l ... (method x () v) M_r ...]])

;; Convert a field to its corresponding getter and (maybe) setter methods.
(define-metafunction GI
  field-methods : F -> [M ...]
  [(field-methods (def x = _)) [(method x () uninitialised)]]
  [(field-methods (var x _ ...))
   [(method x () uninitialised)
    (method (x :=) (x) (assign self x (request x) done))]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; methods.
(define-metafunction GI
  fields-methods : F ... -> (M ...)
  [(fields-methods) ()]
  [(fields-methods F F_r ...) (M ... M_r ...)
   (where (M ...) (field-methods F))
   (where (M_r ...) (fields-methods F_r ...))])

;; Convert a field to its corresponding getter and (maybe) setter method names.
(define-metafunction GI
  field-names : F -> [m ...]
  [(field-names (def x = _)) [x]]
  [(field-names (var x _ ...)) [x (x :=)]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; method names.
(define-metafunction GI
  fields-names : F ... -> (m ...)
  [(fields-names) ()]
  [(fields-names F F_r ...) (m ... m_r ...)
   (where (m ...) (field-names F))
   (where (m_r ...) (fields-names F_r ...))])

;; Convert a list of fields F to a sequence of assignments to the object at
;; location ℓ, resulting in the final expression e.
(define-metafunction GI
  field-assigns : ℓ F ... e -> e
  [(field-assigns ℓ e) e]
  [(field-assigns ℓ (def x = e_v) F ... e)
   (assign (ref ℓ) x e_v (field-assigns ℓ F ... e))]
  [(field-assigns ℓ (var x) F ... e) (field-assigns ℓ F ... e)]
  [(field-assigns ℓ (var x := e_v) F ... e)
   (assign (ref ℓ) x e_v (field-assigns ℓ F ... e))])

;; Ensure that the given names are unique.
(define-metafunction GI
  unique : m ... -> boolean
  [(unique _ ... m _ ... m _ ...) #f]
  [(unique _ ...) #t])

;; Partial small-step dynamic semantics of Graceless extended with inheritance.
(define -->GI
  (reduction-relation
   GI
   #:domain p
   ;; Uninitialised terminates the program.
   (--> [(in-hole E⊥ uninitialised) σ]
        [uninitialised σ]
        uninitialised)
   ;; Inherits concatenates the methods in the super object into the object
   ;; constructor and returns that.
   (--> [(in-hole E (object (s ... inherits (ref ℓ))
                            (name M (method m _ _)) ... F ...)) σ]
        [(in-hole E (object M_s ... M_p ... F_p ...)) σ]
        (where [(name M_i (method m_i _ _)) ...] (lookup σ ℓ))
        (where [m_f ...] (fields-names F ...))
        (where [M_s ...] (override M_i ... m ... m_f ...))
        (where [M_p ... F_p ...] (subst-inherits [ℓ m_i ...] s ... M ... F ...))
        inherits)
   ;; Substitute for unqualified requests to the parameters, and return the body
   ;; of the method.
   (--> [(in-hole E (request (ref ℓ) m v ..._a)) σ]
        [(in-hole E (subst-request ℓ [x v] ... e)) σ]
        (where [_ ... (method m (x ..._a) e) _ ...] (lookup σ ℓ))
        (side-condition (term (unique x ...)))
        request)
   ;; Set the field in the object and return the following expression.
   (--> [(in-hole E (assign (ref ℓ) x v e)) σ]
        [(in-hole E e) σ_p]
        (where σ_p (set-field σ ℓ x v))
        assign)))
