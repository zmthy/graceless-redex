#lang racket

(require redex
         "../graceless.rkt"
         (prefix-in graceless: "../graceless.rkt"))

(provide (all-defined-out)
         unique
         program)

;; The core syntax of Graceless extended with multiple inheritance.
(define-extended-language Graceless-Inheritance Graceless
  ;; Any element of an object expression body.
  (B M
     S)
  ;; Inherits clauses are now statements.
  (S ....
     (inherits e)
     (inherits e as x))
  (e ....
     abstract)
  ;; An object can now have methods anywhere in its body.
  (o (object B ...))
  ;; Super references are now permitted to be any name.
  (r ....
     x))

;; The extended multiple inheritance language extended with the runtime system
;; of Graceless.
(define-union-language GIU Graceless-Inheritance G)

;; The Graceless runtime extended with multiple inheritance core and runtime
;; syntax.
(define-extended-language GI GIU
  ;; Inherits clauses are expressions at runtime when they are translated from
  ;; statements.  Each variant has an optional name.
  (e ....
     (super inherits e s ...)
     (super inherits e as x s ...)
     (i ... inherits e s ...)
     (i ... inherits e as x s ...))
  ;; Substitutions are delayed in objects.
  (o (object s ... B ...))
  ;; Aliases are still receivers at runtime, but now we always have the
  ;; reference that will be aliasing.
  (r ....
     (ref ℓ as ℓ))
  ;; Not really, but helps ensure the existing evaluations continue working.
  (v ....
     (ref ℓ as ℓ))
  ;; We can't write a where clause on the evaluation context, so the inherits
  ;; context is included directly here, and we use EF to handle requests.
  (E ....
     (i ... inherits E any ...))
  ;; The context EF is used for anything which is not directly in an inherits
  ;; clause.  The complex contexts EG and the simple hole in EF are separated to
  ;; prevent a hole from appearing directly in an inherits clause of EF.
  (EG (EF m e ...)
      (v m v ... EF e ...)
      (m v ... EF e ...)
      (EF e ...)
      (v x <- EF)
      (i ... inherits EG any ...))
  (EF EG
      hole)
  (s ....
     [ℓ as ℓ / x]
     [i ... / super])
  ;; Inherits context.
  (i (ℓ M ... s ...)))

;; The languages without the freshness restriction redefine EF to be E.
(define-extended-language GO GI
  (EF E))

;; Remove any names from the substitution s which are shadowed by the names m.
;; If the substitution still has names remaining, it is returned as the sole
;; element of the list, otherwise the list is empty.
(define-metafunction/extension graceless:remove-shadows GI
  remove-shadows : s m ... -> (s ...))

;; Apply remove-shadows for the names m to each substitution s.
(define-metafunction GI
  remove-all-shadows : s ... m ... -> (s ...)
  [(remove-all-shadows s ... m ...)
   ,(append-map (λ (s) (term (remove-shadows ,s m ...)))
                (term (s ...)))])

;; Remove any names from the substitution s which are shadowed by a definition
;; in the given set.  If the substitution still has names remaining, it is
;; returned as the sole element of the list, otherwise the list is empty.  Any
;; substitution for self is incremented, as the object it refers to will be
;; further away inside the inner object.
(define-metafunction GI
  object-shadows : s (B ...) -> (s ...)
  ;; Substitutions of self are incremented.
  [(object-shadows [ℓ / e] _) ([ℓ / (inc-self e)])]
  ;; Substitutions of super need not enter another object.
  [(object-shadows [_ ... / super] _) ()]
  ;; Substitutions to an alias are removed if a definition with the same name
  ;; appears in the object.
  [(object-shadows [ℓ as ℓ_a / x] (B ...)) ()
   (where (_ ... x _ ...) (names B ...))]
  ;; Otherwise the substitution is preserved.
  [(object-shadows [ℓ as ℓ_a / x] _) ([ℓ as ℓ_a / x])]
  ;; Otherwise collect the method names of the object, remove-shadows, and
  ;; increment if the substitution is to self.
  [(object-shadows [e / m_s ...] (B ...))
   (remove-shadows [(inc-self e) / m_s ...] m_o ...)
   (where (m_o ...) (names B ...))])

;; Apply remove-object-shadows for the object o to each substitution s.
(define-metafunction GI
  all-object-shadows : s ... (B ...) -> (s ...)
  [(all-object-shadows s ... (B ...))
   ,(append-map (λ (s) (term (object-shadows ,s (B ...))))
                (term (s ...)))])

;; Determine whether the given thing appears in the substitutions s.
(define-metafunction/extension graceless:not-in-subst GI
  not-in-subst : any s ... -> boolean
  ;; Check for substitutions of super.
  [(not-in-subst super [i ... / super]) #f])

;; Perform substitutions through an expression e.
(define-metafunction GI
  subst : s ... e -> e
  ;; Substitutions are delayed by an object expression.  Any substitution which
  ;; will clearly be shadowed in the object is removed.
  [(subst s ... (object s_o ... B ...))
   (object s_o ... s_p ... B ...)
   (where (s_p ...) (all-object-shadows s ... (B ...)))]
  ;; Substitutions to an unprocessed inherits clause replace super with the
  ;; given context, process the clause's expression, and then delay the
  ;; remaining substitutions.
  [(subst s_l ... [i ... / super] s_r ... (super inherits e any ...))
   (i ... inherits (subst s_l ... s_r ... e) any ... s_p ...)
   (side-condition (term (not-in-subst super s_r ...)))
   ;; Fetch the optional name on the inherits caluse.
   (where ((x ...) _) (optional-name any ...))
   (where (s_p ...) (remove-all-shadows s_l ... s_r ... x ...))]
  ;; Otherwise the clause is processed under all of the substitutions.
  [(subst s ... (i ... inherits e any ...))
   (i ... inherits (subst s ... e) any ... s_p ...)
   (where (s_p ...) (remove-all-shadows s ... x))]
  ;; Continue the substitution into a request.
  [(subst s ... (r m e ...))
   ((subst-receiver s ... r) m (subst s ... e) ...)]
  ;; Substitute out an unqualified request with no arguments for a value v as
  ;; long as there is no later substitution in the list.
  [(subst _ ... [v / x] s ... (x)) v
   (side-condition (term (not-in-subst x s ...)))]
  ;; Substitute out an unqualified request for one qualified in a reference to
  ;; ℓ, so long as there is no later substitution in the list.  Continue the
  ;; substitution into the arguments afterwards.
  [(subst s_l ... (name s [(self n) / _ ... m _ ...]) s_r ... (m e ...))
   (subst s_l ... s s_r ... ((self n) m e ...))
   (side-condition (term (not-in-subst m s_r ...)))]
  ;; Just continue the substitution into a request when no substitution applies.
  [(subst s ... (m e ...)) (m (subst s ... e) ...)]
  ;; Continue the substitution into a sequence, stopping if any of the
  ;; expressions is an inherits clause.
  [(subst s ... ((name e (_ ... inherits _ ...)) e_r ...))
   ((subst s ... e) e_r ...)]
  ;; Handle the special case where there's only a single expression left in the
  ;; sequence.
  [(subst s ... (e e_r)) ((subst s ... e) (subst s ... e_r))]
  ;; Process the rest of a sequence by passing it back to subst.
  [(subst s ... (e e_r ...)) ((subst s ... e) e_p ...)
   (where (e_p ...) (subst s ... (e_r ...)))]
  ;; Continue the substitution into a field lookup.
  [(subst s ... (e y ->)) ((subst s ... e) y ->)]
  ;; Continue the substitution into an assignment.
  [(subst s ... (e y <- e_a))
   ((subst s ... e) y <- (subst s ... e_a))]
  ;; Substitute out self for the given reference, so long as there is no later
  ;; substitution in the list.
  [(subst _ ... [ℓ / (self n)] s ... (self n)) (ref ℓ)
   (side-condition (term (not-in-subst (self n) s ...)))]
  ;; As above, for the direct self sugar.
  [(subst _ ... [ℓ / (self 0)] s ... self) (ref ℓ)
   (side-condition (term (not-in-subst (self 0) s ...)))]
  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... e) e])

;; Continue subst through a request receiver.
(define-metafunction GI
  subst-receiver : s ... r -> r
  ;; Continue the substitution into an expression.
  [(subst-receiver s ... e) (subst s ... e)]
  ;; Substitute out a super name for the given reference, so long as there is no
  ;; later substitution in the list, then continue the substitutions into the
  ;; resulting alias expression.
  [(subst-receiver s_l ... [ℓ as ℓ_a / x] s_r ... x)
   (subst-receiver s_l ... [ℓ as ℓ_a / x] s_r ... (ref ℓ as ℓ_a))
   (side-condition (term (not-in-subst x s_r ...)))]
  ;; Return any other thing, either an alias (which no longer has any
  ;; substitutable children) or a super reference.
  [(subst-receiver _ ... any) any])

;; Continue subst through a method into its body, removing names which appear
;; in the parameter list.
(define-metafunction GI
  subst-method : s ... M -> M
  [(subst-method s ... (method m (x ...) e ...))
   (method m (x ...) (subst s_p ... e) ...)
   (where (s_p ...) (remove-all-shadows s ... x ...))])

;; Store the object O in the store σ. The resulting location is the same as
;; calculated by fresh-location on the same store, before the object is added.
(define-metafunction/extension graceless:store GI
  store : σ O -> σ)

;; Store the object O at the location ℓ in the store σ. The resulting location
;; is the same as calculated by fresh-location on the same store, before the
;; object is added.
(define-metafunction GI
  store-at : σ ℓ O -> σ
  [(store-at σ ℓ O) ,(list-set (term σ) (term ℓ) (term O))])

;; Fetch a fresh location for the store σ.
(define-metafunction/extension graceless:fresh-location GI
  fresh-location : σ -> ℓ)

;; Search for the object at the location ℓ in the store σ.
(define-metafunction/extension graceless:lookup GI
  lookup : σ ℓ -> O)

;; Retrieve the value of the field x in the object at the location ℓ in the
;; store σ.
(define-metafunction GI
  get-field : σ ℓ x -> v or uninitialised
  [(get-field σ ℓ x) (get-field-in (lookup σ ℓ) x)])

;; Retrieve the value of the field x in the object O.
(define-metafunction/extension graceless:get-field-in GI
  get-field-in : O x -> v or uninitialised)

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v.  This will fail if no field named x in the object.
(define-metafunction GI
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (O) (term (set-field-in ,O x v))))])

;; Set the field x in the object O to have the value v.
(define-metafunction/extension graceless:set-field-in GI
  set-field-in : O x v -> O)

;; Collect all of the method names of the methods M and generated accessors of
;; fields in the statement list S.
(define-metafunction GI
  names : B ... -> (m ...)
  [(names B ...)
   ,(append (term (method-names M ...)) (term (stmt-method-names S ...)))
   (where [(M ...) (S ...)] (split-body B ...))])

;; Collect all of the method names in the object o, including those generated by
;; getter and setter methods of fields.
(define-metafunction/extension graceless:method-names GI
  method-names : M ... -> (m ...))

;; Collect the corresponding method names of generated accessor methods in the
;; statements S.
(define-metafunction GI
  stmt-method-names : S ... -> (m ...)
  [(stmt-method-names S ...)
   ,(append-map (λ (S) (term (stmt-to-method-names ,S))) (term (S ...)))])

;; Convert the statement S into the names of generated accessor methods if it is
;; a field, otherwise an empty list.
(define-metafunction/extension graceless:stmt-to-method-names GI
  stmt-to-method-names : S -> (m ...))

;; Convert the statements S into accessor methods M and an object body e.
(define-metafunction/extension graceless:body GI
  body : [S y] ... -> (M ... e ...)
  ;; Inherits clauses are replaced by their unsubstituted expression form.
  [(body [(inherits e any ...) _] [S y_r] ...)
   (M ... (super inherits e any ...) e_r ...)
   (where (M ... e_r ...) (body [S y_r] ...))])

;; Sequence a series of expressions into a single expression.
(define-metafunction/extension graceless:seq GI
  seq : e ... -> e)

;; Check that each of lists of names have unique elements.
(define-metafunction GI
  all-unique : (m ...) ... -> boolean
  [(all-unique (m ...) ...)
   ,(andmap (λ (m) (term (unique . ,m))) (term ((m ...) ...)))])

;; Remove any methods named m from M.
(define-metafunction GI
  override : M ... m ... -> (M ...)
  [(override m ...) []]
  [(override (method m _ _) M ... m_l ... m m_r ...)
   (override M ... m_l ... m m_r ...)]
  [(override M M_i ... m ...) (M M_p ...)
   (where (M_p ...) (override M_i ... m ...))])

;; Split an object body into methods and statements, preserving ordering.
(define-metafunction GI
  split-body : B ... -> [(M ...) (S ...)]
  ;; Once there are no more body elements, return empty pairs.
  [(split-body) [() ()]]
  ;; If the next body element is a method, add it to the front.
  [(split-body M B ...) [(M M_p ...) (S_p ...)]
   (where [(M_p ...) (S_p ...)] (split-body B ...))]
  ;; Otherwise add the statement to the front of the statement portion.
  [(split-body S B ...) [(M_p ...) (S S_p ...)]
   (where [(M_p ...) (S_p ...)] (split-body B ...))])

;; Update all of the objects in the inherits contexts.
(define-metafunction GI
  update : σ M ... i ... -> σ
  ;; No more contexts to process.
  [(update σ M ...) σ]
  ;; Otherwise process the next context (coming down the hierarchy).
  [(update σ M_u ... (ℓ M ... s ...) i ...)
   ;; Update the object in the store with the new inherited and old but
   ;; re-substituted methods, and continue processing the remaining contexts.
   (update (store-at σ ℓ (object F ... M_up ... M_p ... M_dp ...))
           M_up ... M_p ... i ...)
   ;; Fetch the names of the original methods in the object.
   (where (m ...) (names M ...))
   ;; Fetch the names of the methods that are being inherited.
   (where (m_u ...) (names M_u ...))
   ;; Filter out inherited methods that were already defined in this object.
   (where (M_up ...) (override M_u ... m ...))
   ;; Lookup the original object, fetching its post-substituted methods.
   (where (object F ... M_d ...) (lookup σ ℓ))
   ;; Fetch the names of all of the methods that are currently in the object.
   (where (m_d ...) (names M_d ...))
   ;; Throw out all of the existing methods that have been redefined, either by
   ;; being in the object originally, or freshly inherited.  This is necessary
   ;; because we want to keep methods that were inherited from somewhere
   ;; earlier, but haven't been overridden here, but we need to get rid of
   ;; everything being otherwise processed now.
   (where (M_dp ...) (override M_d ... m ... m_u ...))
   ;; Re-substitute the methods in this new context.
   (where (M_p ...) ((subst-method s ...
                                  ;; The original methods will now execute in
                                  ;; the updated scope of all of the included
                                  ;; methods.
                                  [(self 0) / m_d ... m_u ...] M) ...))])

;; Handle the optional name on an inherits clause, returning either an empty or
;; singleton list for the name, and the remaining delayed substitutions.
(define-metafunction GI
  optional-name : any ... -> [(x ...) (s ...)]
  ;; No name, return an empty list and the substitutions.
  [(optional-name s ...) (() (s ...))]
  ;; A name, return a singleton list and the substitutions.
  [(optional-name _ x s ...) ((x) (s ...))])

;; Add an optional substitution s to the top of the inherits context i.
(define-metafunction GI
  add-substitution : (s ...) i ... -> (i ...)
  ;; If there's no substitution, don't do anything.
  [(add-substitution () i ...) (i ...)]
  ;; Otherwise, add it to the first context.
  [(add-substitution (s_n) (ℓ M ... s ...) i ...) ((ℓ M ... s ... s_n) i ...)])

;; Partial small-step dynamic semantics of Graceless inheritance.  Must be
;; extended with rules for inherits clauses and object literals.  In order for
;; this relation to be common to all of the inherits extensions, we cannot
;; extend -->G, because we have to ensure that requests are not evaluated
;; normally when they are directly in an inherits clause.  As explained above,
;; extensions of the GO language will have normal behaviour for requests.
(define -->GP
  (reduction-relation
   GI
   #:domain p
   ;; Move to the next expression in a sequence when the first expression has
   ;; completed evaluating.
   (--> [σ (in-hole E (v e ...))]
        [σ (in-hole E (seq e ...))]
        next)
   ;; Set the field in the object and return the following expression.
   (--> [σ (in-hole E ((ref ℓ) x <- v))]
        [(set-field σ ℓ x v) (in-hole E done)]
        assign)
   ;; Get the field in the object.
   (--> [σ (in-hole E ((ref ℓ) x ->))]
        [σ (in-hole E (get-field σ ℓ x))]
        ;; Fetch the field.
        (where e (get-field σ ℓ x))
        ;; Check that the result is initialised.
        (side-condition (term (initialised e)))
        fetch)
   ;; Crash the program if the field is not initialised.
   (--> [σ (in-hole E ((ref ℓ) x ->))]
        [σ uninitialised]
        ;; Check that the result is uninitialised.
        (where uninitialised (get-field σ ℓ x))
        uninitialised)
   ;; Substitute for unqualified requests to the parameters, and return the body
   ;; of the method.
   (--> [σ (in-hole EF ((ref ℓ) m v ..._a))]
        ;; Substitute the variable names for the arguments and the receiver for
        ;; self.  This rule is slightly different from the text, which assumes
        ;; that the body is interpreted as a single sequenced expression.  Here
        ;; we manually sequence the body.
        [σ (in-hole EF (subst [ℓ / (self 0)] [v / x] ... (seq e ...)))]
        ;; Fetch the one method with the name given in the request.
        (where (object _ ... (method m (x ..._a) e ...) _ ...) (lookup σ ℓ))
        request)
   ;; As above, but with self bound as the alias ℓ_d.
   (--> [σ (in-hole EF ((ref ℓ_u as ℓ_d) m v ..._a))]
        ;; Substitute the variable names for the arguments and the receiver for
        ;; self.  This rule is slightly different from the text, which assumes
        ;; that the body is interpreted as a single sequenced expression.  Here
        ;; we manually sequence the body.
        [σ (in-hole EF (subst [ℓ_d / (self 0)] [v / x] ... (seq e ...)))]
        ;; Fetch the one method with the name given in the request.
        (where (object _ ... (method m (x ..._a) e ...) _ ...) (lookup σ ℓ_u))
        request/super)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; uninherited object construction.  Must be extended with rules for inherits
;; clauses.
(define -->GPO
  (extend-reduction-relation
   -->GP
   GI
   #:domain p
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [σ (in-hole EF (object s ... B ...))]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(store σ (object (subst-method s ...
                                        [(self 0) / m ...] M) ... M_f ...))
         (in-hole EF (subst s ...
                            [(ℓ M ... M_f ... s ...) / super]
                            [ℓ / (self 0)]
                            [(self 0) / m ...] (seq e ... (ref ℓ))))]
        ;; Split the body into methods and statements.
        (where [(M ...) (S ...)] (split-body B ...))
        ;; Fetch a fresh location.
        (where ℓ (fresh-location σ))
        ;; The method names are used for substituting local requests, as well as
        ;; ensuring the resulting object has unique method names.
        (where (m ...) (names M ... S ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique m ...)))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S ...)))
        ;; Collect the field accessor methods and the resulting object body.
        ;; The sugared inherits clauses are treated as normal expressions here,
        ;; with a placeholder name which won't be used.
        (where (M_f ... e ...) (body [S y] ...))
        object)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; positional object inheritance. Must be extended with rules for object
;; literals.
(define -->GPI
  (extend-reduction-relation
   -->GP
   GO
   #:domain p
   ;; Concatenate the body of the inherited objects into the inheriting object's
   ;; store, removing overrides, and update the following expression.  Note that
   ;; under object inheritance, there can only ever be one inherits context.
   (--> [σ (in-hole E ((i inherits (ref ℓ) any ...) e ...))]
        ;; Update the self object, and perform the substitutions into the
        ;; remaining body.
        [(update σ M ... i_p)
         (in-hole E (seq (subst s ...
                                [i_p / super]
                                [(self 0) / m ...]
                                s_s ... e) ...))]
        ;; Fetch the optional name and substitutions of the inherits clause.
        (where [(x ...) (s ...)] (optional-name any ...))
        ;; Lookup the super object.
        (where (object F ... M ...) (lookup σ ℓ))
        ;; Collect the names of the definitions in the inherited object.
        (where (m ...) (names M ...))
        ;; Fetch the actual self value from the bottom of the inherits contexts.
        (where ℓ_d ,(first (term i)))
        ;; Construct the optional super substitution.
        (where (s_s ...) ([ℓ as ℓ_d / x] ...))
        ;; Include the new super alias in the top of the inherits context.
        (where (i_p) (add-substitution (s_s ...) i))
        inherits/positional)))

;; Determine if the given expression is a fresh object expression, or is a
;; sequence of expressions which ends in an object expression.
(define-metafunction GI
  is-fresh : e -> boolean
  [(is-fresh o) #t]
  [(is-fresh (e ... e_o)) (is-fresh e_o)]
  [(is-fresh _) #f])

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; fresh object construction.  Must be extended with rules for inherits clauses.
(define -->GPF
  (extend-reduction-relation
   -->GPO
   GI
   #:domain p
   ;; A request directly in an inherits clause is only allowed to proceed if it
   ;; results in a fresh object.
   (--> [σ (in-hole E (i ... inherits (v m v_a ...) any ...))]
        [σ_p (in-hole E (i ... inherits e any ...))]
        ;; We can't pattern match here, because the result could be either a
        ;; single object or an expression sequence.
        (where ([σ_p e])
               ,(apply-reduction-relation -->GP (term [σ (v m v_a ...)])))
        ;; Ensure the resulting expression is fresh.
        (side-condition (term (is-fresh e)))
        inherits/positional-fresh)))
