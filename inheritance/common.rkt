#lang racket

(require redex
         "../graceless.rkt"
         (prefix-in graceless: "../graceless.rkt"))

(provide (all-defined-out)
         remove-shadows
         not-in-subst
         unique
         program)

;; The core syntax of Graceless extended with inheritance.
(define-extended-language Graceless-Inheritance Graceless
  (e ....
     super)
  (o ....
     (object I M ... F ...))
  (I (inherits e)))

;; The extended inheritance language extended with the runtime system of
;; Graceless.
(define-union-language GIU Graceless-Inheritance G)

;; The Graceless runtime extended with inheritance core and runtime syntax.
(define-extended-language GI GIU
  (e ....
     (ref ℓ as e))
  (I (s ... inherits e))
  (v ....
     (ref ℓ as v))
  (E⊥ ....
      (object (s ... inherits E) M ... F ...))
  ;; The complex contexts and the simple hole are separated here to prevent hole
  ;; from appearing directly in an inherits clause of EF.
  (EF⊥ (request EF m e ...)
       (request v m v ... EF e ...)
       (request m v ... EF e ...)
       (assign v x EF e)
       (object (s ... inherits EF⊥) M ... F ...))
  (EF EF⊥
      hole)
  ;; This context is used for anything which is directly in an inherits clause.
  (EI (request EI m e ...)
      (request v m v ... EI e ...)
      (request m v ... EI e ...)
      (assign v x EI e)
      (object (s ... inherits hole) M ... F ...))
  (s ....
     [ℓ super]))

;; The languages without the freshness restriction just redefine EF to be E.
(define-extended-language GO GI
  (EF E))

;; Apply remove-shadows for the names m to each substitution s.
(define-metafunction GI
  remove-all-shadows : s ... m ... -> (s ...)
  [(remove-all-shadows s ... m ...)
   ,(append-map (λ (s) (term (remove-shadows ,s m ...)))
                (term (s ...)))])

;; Remove any names from the substitution s which are shadowed by a definition
;; in the object o.  If the substitution still has names remaining, it is
;; returned as the sole element of the list, otherwise the list is empty.  Any
;; substitution for self is guaranteed to be removed, as the new object context
;; implicitly shadows it.
(define-metafunction GI
  remove-object-shadows : s o -> (s ...)
  ;; Self is always removed.
  [(remove-object-shadows [_ self] _) ()]
  ;; Super is always removed.
  [(remove-object-shadows [_ super] _) ()]
  ;; Otherwise collect the method names of the object, and remove-shadows.
  [(remove-object-shadows s o) (remove-shadows s m ...)
   (where (m ...) (object-names o))])

;; Apply remove-object-shadows for the object o to each substitution s.
(define-metafunction GI
  remove-all-object-shadows : s ... o -> (s ...)
  [(remove-all-object-shadows s ... o)
   ,(append-map (λ (s) (term (remove-object-shadows ,s o)))
                (term (s ...)))])

;; Perform substitutions s through an expression e.
(define-metafunction GI
  subst : s ... e -> e
  ;; Substitutions get delayed in object bodies by an inherits clause, though
  ;; the substitution continues into the clause's expression.  Names which will
  ;; definitely be shadowed in the object body are removed in the delayed
  ;; substitution.
  [(subst s ... (name o (object (s_i ... inherits e) M ... F ...)))
   (object (s_p ... s_i ... inherits (subst s ... e)) M ... F ...)
   (where (s_p ...) (remove-all-object-shadows s ... o))]
  ;; Continue the substitution into an object body, removing substitutions
  ;; shadowed by the object.
  [(subst s ... (name o (object M ... F ...)))
   (object (subst-method s_p ... M) ... (subst-field s_p ... F) ...)
   (where (s_p ...) (remove-all-object-shadows s ... o))]
  ;; Continue the substitution into a request.
  [(subst s ... (request e m e_a ...))
   (request (subst s ... e) m (subst s ... e_a) ...)]
  ;; Substitute out an unqualified request with no arguments for a value v as
  ;; long as there is no earlier substitution in the list.
  [(subst s ... [v x] _ ... (request x)) v
   (side-condition (term (not-in-subst x s ...)))]
  ;; Substitute out an unqualified request for one qualified in a reference to
  ;; ℓ, so long as there is no earlier substitution in the list.  Continue the
  ;; substitution into the arguments afterwards.
  [(subst s_l ... (name s [ℓ _ ... m _ ...]) s_r ... (request m e ...))
   (request (ref ℓ) m (subst s_l ... s s_r ... e) ...)
   (side-condition (term (not-in-subst m s_l ...)))]
  ;; Continue the substitution into a request when no substitution applies.
  [(subst s (request m e ...)) (request m (subst s e) ...)]
  ;; Continue the substitution into an assignment.
  [(subst s ... (assign e_r x e_a e))
   (assign (subst s ... e_r) x (subst s ... e_a) (subst s ... e))]
  ;; Substitute out self for the given reference, so long as there is no earlier
  ;; substitution in the list.
  [(subst s ... [ℓ self] _ ... self) (ref ℓ)
   (side-condition (term (not-in-subst self s ...)))]
  ;; Substitute out super for the given reference, so long as there is no
  ;; earlier substitution in the list, then continue the substitutions into the
  ;; resulting alias expression.
  [(subst s_l ... [ℓ super] s_r ... super)
   (ref ℓ as (subst s_l ... s_r ... self))
   (side-condition (term (not-in-subst super s_l ...)))]
  ;; Continue substitutions into alias expressions.
  [(subst s ... (ref ℓ as e)) (ref ℓ as (subst s ... e))]
  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... e) e])

;; Continue subst through methods into method bodies, removing names which
;; appear in the parameter list.
(define-metafunction GI
  subst-method : s ... M -> M
  [(subst-method s ... (method m (x ...) e))
   (method m (x ...) (subst s_p ... e))
   (where (s_p ...) (remove-all-shadows s ... x ...))])

;; Continue substitution through fields into their assignments.  This ignores
;; their names, as that will already have been taken care of by the rule for
;; object in the subst function.
(define-metafunction GI
  subst-field : s ... F -> F
  [(subst-field s ... (def x = e)) (def x = (subst s ... e))]
  [(subst-field _ ... (var x)) (var x)]
  [(subst-field s ... (var x := e)) (var x := (subst s ... e))])

;; Store a new object with the methods M.  The resulting location is the same as
;; calculated by fresh-location on the same store, before the object is added.
(define-metafunction/extension graceless:store GI
  store : σ [M ...] -> σ)

;; Fetch a fresh location for the store.
(define-metafunction/extension graceless:fresh-location GI
  fresh-location : σ -> ℓ)

;; Search for the object at the location ℓ in the store σ.
(define-metafunction/extension graceless:lookup GI
  lookup : σ ℓ -> [M ...])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v. This will fail if no field named x in the object.
(define-metafunction GI
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (Ms) (term (update-method ,Ms x v))))])

;; Set the method named x in the method list of M to return the value v.  This
;; will fail if there is no field named x in the object.
(define-metafunction/extension graceless:update-method GI
  update-method : [M ...] x v -> [M ...])

;; Collect all of the method names in the object o, including those generated by
;; getter and setter methods of fields, but not those included by the inherits
;; clause, as that must be evaluated to determine the names it introduces.
(define-metafunction GI
  object-names : o -> (m ...)
  [(object-names (object I ... (method m _ _) ... F ...))
   ,(append (term (m ...)) (term (field-names F ...)))])

;; Convert the field F into getter and (maybe) setter methods.
(define-metafunction/extension graceless:field-to-methods GI
  field-to-methods : F -> (M ...))

;; Collect the corresponding getter and (maybe) setter methods of the fields F.
(define-metafunction GI
  field-methods : F ... -> (M ...)
  [(field-methods F ...)
   ,(append-map (λ (F) (term (field-to-methods ,F))) (term (F ...)))])

;; Convert the field F into getter and (maybe) setter method names.
(define-metafunction/extension graceless:field-to-names GI
  field-to-names : F -> (m ...))

;; Collect the corresponding getter and (maybe) setter method names of the
;; fields F.
(define-metafunction GI
  field-names : F ... -> (m ...)
  [(field-names F ...)
   ,(append-map (λ (F) (term (field-to-names ,F))) (term (F ...)))])

;; Convert a field F to an assignment in the object at location ℓ, which then
;; executes the expression e.
(define-metafunction/extension graceless:field-to-assign GI
  field-to-assign : ℓ F e -> e)

;; Convert a list of fields F to a sequence of assignments in the object at
;; location ℓ, finally executing the final expression e.
(define-metafunction GI
  field-assigns : ℓ F ... e -> e
  [(field-assigns ℓ F ... e)
   ,(foldr (λ (F e) (term (field-to-assign ℓ ,F ,e))) (term e) (term (F ...)))])

;; Remove any methods named m from M.
(define-metafunction GI
  override : M ... m ... -> [M ...]
  [(override m ...) []]
  [(override (method m _ _) M ... m_l ... m m_r ...)
   (override M ... m_l ... m m_r ...)]
  [(override M M_i ... m ...) [M M_p ...]
   (where [M_p ...] (override M_i ... m ...))])

;; Replace the body of the method M with a request to method m in the object at
;; location ℓ with the same arguments.
(define-metafunction GI
  forward-request-to : ℓ M -> M
  [(forward-request-to ℓ (method m (x ...) _))
   (method m (x ...) (request (ref ℓ as self) m (request x) ...))])

;; Convert either form of reference to an aliased one.  If the original
;; reference is not an alias, it aliases itself.
(define-metafunction GI
  as-alias : e -> e
  [(as-alias (ref ℓ)) (ref ℓ as (ref ℓ))]
  [(as-alias e) e])

;; Partial small-step dynamic semantics of Graceless inheritance.  Must be
;; extended with rules for inherits clauses object literals.
(define -->GP
  (reduction-relation
   GI
   #:domain p
   ;; Uninitialised terminates the program.
   (--> [(in-hole E⊥ uninitialised) σ]
        [uninitialised σ]
        uninitialised)
   ;; Substitute for unqualified requests to the parameters, and return the body
   ;; of the method.
   (--> [(in-hole EF (request v_r m v ..._a)) σ]
        ;; It's important that the local references come first in the
        ;; substitution, as the parameters shadow local methods in the body.
        [(in-hole EF (subst [v x] ... [ℓ_a self] [ℓ_a m_o ...] e)) σ]
        ;; Get the lookup and binding references from the receiver.
        (where (ref ℓ as (ref ℓ_a)) (as-alias v_r))
        ;; Collect all the names of the methods in the receiver.
        (where [(name M (method m_o _ _)) ...] (lookup σ ℓ))
        ;; And fetch the one method with the name given in the request.
        (where [_ ... (method m (x ..._a) e) _ ...] [M ...])
        ;; A method's parameters must be unique.
        (side-condition (term (unique x ...)))
        request)
   ;; Set the field in the object and return the following expression.
   (--> [(in-hole E (assign (ref ℓ) x v e)) σ]
        [(in-hole E e) (set-field σ ℓ x v)]
        assign)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; simple object inheritance.  Must be extended with rules for object literals.
(define -->GO
  (extend-reduction-relation
   -->GP
   GO
   #:domain p
   ;; Inherits concatenates the methods in the super object into the object
   ;; constructor and returns the resulting concatenation.  The actual object
   ;; reference will be built in the next step.
   (--> [(in-hole E (object (s_d ... inherits (ref ℓ))
                            (name M (method m _ _)) ... F ...)) σ]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and substituted fields.
        [(in-hole E (object M_s ...
                            (subst-method [ℓ super] s ... M) ...
                            (subst-field [ℓ super] s ... F) ...)) σ]
        ;; Lookup the super object, fetching both its methods and method names.
        (where [(name M_i (method m_i _ _)) ...] (lookup σ ℓ))
        ;; Collect the names of the fields in the inheriting object.
        (where (m_f ...) (field-names F ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object.
        (where [M_s ...] (override M_i ... m ... m_f ...))
        ;; Definitions introduced by the inherits clause don't have a reference
        ;; to substitute in yet: that will be produced by the following
        ;; reduction step on the inheriting object.  So, we need to remove the
        ;; names in the inherits clause from the delayed substitutions, as the
        ;; resulting methods will appear in the object and shadow them.
        (where (s ...) (remove-all-shadows s_d ... m_i ...))
        inherits)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; simple method forwarding.  Must be extended with rules for object literals.
(define -->GR
  (extend-reduction-relation
   -->GP
   GO
   #:domain p
   ;; Inherits concatenates the methods in the super object into the object
   ;; constructor and returns the resulting concatenation.  The actual object
   ;; reference will be built in the next step.
   (--> [(in-hole E (object (s_d ... inherits (ref ℓ))
                            (name M (method m _ _)) ... F ...)) σ]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and substituted fields.
        [(in-hole E (object M_s ...
                            (subst-method [ℓ super] s ... M) ...
                            (subst-field [ℓ super] s ... F) ...)) σ]
        ;; Lookup the super object, fetching both its methods and method names.
        (where [(name M_i (method m_i _ _)) ...] (lookup σ ℓ))
        ;; Collect the names of the fields in the inheriting object.
        (where (m_f ...) (field-names F ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object, and then forward to the super
        ;; object as self.
        (where [M_s ...] ,(map (λ (M) (term (forward-request-to ℓ ,M)))
                               (term (override M_i ... m ... m_f ...))))
        ;; Definitions introduced by the inherits clause don't have a reference
        ;; to substitute in yet: that will be produced by the following
        ;; reduction step on the inheriting object.  So, we need to remove the
        ;; names in the inherits clause from the delayed substitutions, as the
        ;; resulting methods will appear in the object and shadow them.
        (where (s ...) (remove-all-shadows s_d ... m_i ...))
        inherits)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; fresh object construction.  Must be extended with rules for inherits clauses
;; with object literals.
(define -->GI
  (extend-reduction-relation
   -->GP
   GI
   #:domain p
   ;; A request directly in an inherits clause is only allowed to proceed if it
   ;; results in a fresh object.
   (--> [(in-hole EI (name e (request v m v_a ...))) σ]
        [(in-hole EI o) σ_p]
        (where [o σ_p] ,(apply-reduction-relation -->GP (term [e σ]))))
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.  Note that this in the hole EF, which ensures that it
   ;; is not executed if it appears directly in an inherits clause.
   (--> [(in-hole EF (name o (object M ... F ...))) σ]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(in-hole EF (subst [ℓ self] [ℓ m ...] (field-assigns ℓ F ... (ref ℓ))))
         (store σ [M ... M_f ...])]
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; The method names are used for substituting local requests, as well as
        ;; ensuring the resulting object has unique method names.
        (where (m ...) (object-names o))
        ;; The generated getter and setter methods are included in the store.
        (where (M_f ...) (field-methods F ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        object)))
