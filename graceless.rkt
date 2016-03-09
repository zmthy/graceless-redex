#lang racket

(require redex)

(provide (all-defined-out))

;; The core syntax of Graceless.
(define-language Graceless
  (e o
     (request e m e ...)
     (request m e ...)
     self
     done)
  (M (method m (x ...) e))
  (F (def x = e)
     (var x)
     (var x := e))
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
  (v (ref ℓ)
     done)
  ;; The complex contexts and the simple hole are separated here to allow
  ;; uninitialised to cascade without looping back on itself.
  (E⊥ (request E m e ...)
      (request v m v ... E e ...)
      (request m v ... E e ...)
      (assign v x E e))
  (E E⊥
     hole)
  (ℓ natural)
  (σ ([M ...] ...))
  (p [e σ]))

;; Perform an object substitution in the expression e, replacing local
;; references to self and qualifying local requests to ℓ.
(define-metafunction G
  subst-object : ℓ m ... e -> e
  [(subst-object ℓ m ... e) (subst-rec ℓ m ... (subst-self ℓ e))])

;; Perform a request substitution in the expression e, replacing local
;; references to self with ℓ and unqualified requests to each x with the
;; corresponding v.
(define-metafunction G
  subst-request : ℓ [x v] ... e -> e
  [(subst-request ℓ [x v] ... e) (subst [x v] ... (subst-self ℓ e))])

;; Substitute any local request for each x with the corresponding v.
(define-metafunction G
  subst : [x v] ... e -> e
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
(define-metafunction G
  subst-method : [x v] ... M -> M
  [(subst-method [x_l v_l] ... [x v] [x_r v_r] ...
                 (name M (method _ (_ ... x _ ...) _)))
   (subst-method [x_l v_l] ... [x_r v_r] ... M)]
  [(subst-method [x_s v] ... (method m (x ...) e))
   (method m (x ...) (subst [x_s v] ... e))])

;; Continue subst through fields into their assignments.
(define-metafunction G
  subst-field : [x v] ... F -> F
  [(subst-field [x_s v] ... (def x = e)) (def x = (subst [x_s v] ... e))]
  [(subst-field _ ... (var x)) (var x)]
  [(subst-field [x_s v] ... (var x := e)) (var x := (subst [x_s v] ... e))])

;; Substitute the location ℓ as a reference for the locally defined self,
;; stopping at nested object expressions.
(define-metafunction G
  subst-self : ℓ e -> e
  [(subst-self ℓ (request e m e_a ...))
   (request (subst-self ℓ e) m (subst-self ℓ e_a) ...)]
  [(subst-self ℓ (request m e ...)) (request m (subst-self ℓ e) ...)]
  [(subst-self ℓ (assign e_r x e_v e_n))
   (assign (subst-self ℓ e_r) x (subst-self ℓ e_v) (subst-self ℓ e_n))]
  [(subst-self ℓ self) (ref ℓ)]
  [(subst-self _ e) e])

;; Substitute the location ℓ as the receiver to unqualified requests in the set
;; of names m.
(define-metafunction G
  subst-rec : ℓ m ... e -> e
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
(define-metafunction G
  subst-rec-method : ℓ m ... M -> M
  [(subst-rec-method ℓ m_l ... x m_r ...
                 (name M (method m (_ ... x _ ...) _)))
   (subst-rec-method ℓ m_l ... m_r ... M)]
  [(subst-rec-method ℓ m_s ... (method m (x ...) e))
   (method m (x ...) (subst-rec ℓ m_s ... e))])

;; Continue subst through fields into their assignments.
(define-metafunction G
  subst-rec-field : ℓ m ... F -> F
  [(subst-rec-field ℓ m ... (def x = e)) (def x = (subst-rec ℓ m ... e))]
  [(subst-rec-field ℓ m ... (var x)) (var x)]
  [(subst-rec-field ℓ m ... (var x := e)) (var x := (subst-rec ℓ m ... e))])

;; Allocate the object o in the store, returning the newly allocated location
;; and the updated store.
(define-metafunction G
  allocate : σ [M ...] -> [ℓ σ]
  [(allocate σ [M ...]) [(fresh-location σ) (store σ [M ...])]])

;; Store the object o.  The resulting location is the same as calculated by
;; fresh-location on the same store, before the object is added.
(define-metafunction G
  store : σ [M ...] -> σ
  [(store ([M_σ ...] ...) [M ...]) ([M_σ ...] ... [M ...])])

;; Fetch a fresh location for the store.
(define-metafunction G
  fresh-location : σ -> ℓ
  [(fresh-location σ) ,(length (term σ))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction G
  lookup : σ ℓ -> [M ...]
  [(lookup σ ℓ) ,(list-ref (term σ) (term ℓ))])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v. This will fail if no field named x in the object.
(define-metafunction G
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (Ms) (term (update-method ,Ms x v))))])

;; Set the method named x in the method list of M to return the value v.  This
;; will fail if there is no field named x in the object.
(define-metafunction G
  update-method : [M ...] x v -> [M ...]
  [(update-method [M_l ... (method x () _) M_r ...] x v)
   [M_l ... (method x () v) M_r ...]])

;; Convert a field to its corresponding getter and (maybe) setter methods.
(define-metafunction G
  field-methods : F -> [M ...]
  [(field-methods (def x = _)) [(method x () uninitialised)]]
  [(field-methods (var x _ ...))
   [(method x () uninitialised)
    (method (x :=) (x) (assign self x (request x) done))]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; methods.
(define-metafunction G
  fields-methods : F ... -> (M ...)
  [(fields-methods) ()]
  [(fields-methods F F_r ...) (M ... M_r ...)
   (where (M ...) (field-methods F))
   (where (M_r ...) (fields-methods F_r ...))])

;; Convert a field to its corresponding getter and (maybe) setter method names.
(define-metafunction G
  field-names : F -> [m ...]
  [(field-names (def x = _)) [x]]
  [(field-names (var x _ ...)) [x (x :=)]])

;; Convert a list of fields to their corresponding getter and (maybe) setter
;; method names.
(define-metafunction G
  fields-names : F ... -> (m ...)
  [(fields-names) ()]
  [(fields-names F F_r ...) (m ... m_r ...)
   (where (m ...) (field-names F))
   (where (m_r ...) (fields-names F_r ...))])

;; Convert a list of fields F to a sequence of assignments to the object at
;; location ℓ, resulting in the final expression e.
(define-metafunction G
  field-assigns : ℓ F ... e -> e
  [(field-assigns ℓ e) e]
  [(field-assigns ℓ (def x = e_v) F ... e)
   (assign (ref ℓ) x e_v (field-assigns ℓ F ... e))]
  [(field-assigns ℓ (var x) F ... e) (field-assigns ℓ F ... e)]
  [(field-assigns ℓ (var x := e_v) F ... e)
   (assign (ref ℓ) x e_v (field-assigns ℓ F ... e))])

;; Ensure that the given names are unique.
(define-metafunction G
  unique : m ... -> boolean
  [(unique _ ... m _ ... m _ ...) #f]
  [(unique _ ...) #t])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   G
   #:domain p
   ;; Uninitialised terminates the program.
   (--> [(in-hole E⊥ uninitialised) σ]
        [uninitialised σ]
        uninitialised)
   ;; Allocate the object o substituting local requests to this object, and
   ;; return the resulting reference.
   (--> [(in-hole E (object (name M (method m _ _)) ... F ...))
         σ]
        [(in-hole E (subst-object ℓ m ... m_f ...
                                  (field-assigns ℓ F ... (ref ℓ))))
         (store σ [(subst-rec-method ℓ m ... m_f ... M_p) ...])]
        (where ℓ (fresh-location σ))
        (where (m_f ...) (fields-names F ...))
        (where (M_f ...) (fields-methods F ...))
        (where (M_p ...) (M ... M_f ...))
        (side-condition (term (unique m ... m_f ...)))
        object)
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

;; Wrap a term t into an initial program with an empty store.
(define (program t) (term [,t ()]))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Evaluate an expression starting with an empty store.
(define-metafunction G
  eval : e -> e
  [(eval e) ,(car (term (run [e ()])))])

;; Apply the reduction relation -->G until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction G
  run : p -> [e σ]
  [(run [uninitialised σ]) [uninitialised σ]]
  [(run [(ref ℓ) σ]) [(object M ...) σ]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->G (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error.
(define (eval-->G t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->G t) (term (run [,t ()])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->G t) (traces -->G (program t)))
