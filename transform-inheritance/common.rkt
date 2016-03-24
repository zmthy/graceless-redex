#lang racket

(require redex
         "../graceless.rkt"
         (prefix-in graceless: "../graceless.rkt"))

(provide (all-defined-out)
         unique
         program)

;; The core syntax of Graceless extended with multiple inheritance.
(define-extended-language Graceless-Inheritance Graceless
  ;; Allows you to omit the transform clauses if you're not using them.
  (I (inherits e)
     (inherits e alias (m as m) ...)
     (inherits e exclude m ...)
     (inherits e alias (m as m) ... exclude m ...))
  (e ....
     abstract)
  ;; Same as before, just to point out that there aren't any super references.
  (r e)
  (o ....
     (object I ... M ... S ...)))

;; The extended multiple inheritance language extended with the runtime system
;; of Graceless.
(define-union-language GIU Graceless-Inheritance G)

;; The Graceless runtime extended with multiple inheritance core and runtime
;; syntax.
(define-extended-language GI GIU
  ;; Inherits clause ready to be processed.
  (Io (inherits (object M ... S ...) any ...))
  ;; Substitutions are delayed in objects.
  (o (object I ... s ... M ... S ...))
  ;; We can't write a where clause on the evaluation context, so the inherits
  ;; context is included directly here, and we use EF to handle requests.
  (E ....
     (object Io ... (inherits E any ...) I ... s ... M ... S ...))
  ;; The context EF is used for anything which is not directly in an inherits
  ;; clause.  The complex contexts EG and the simple hole in EF are separated to
  ;; prevent a hole from appearing directly in an inherits clause of EF.
  (EG (EF m e ...)
      (v m v ... EF e ...)
      (m v ... EF e ...)
      (EF e ...)
      (v x <- EF)
      (object Io ... (inherits EG any ...) I ... M ... S ...))
  (EF EG
      hole))

;; The languages without the freshness restriction redefine EF to be E, and Io
;; to be an inherits to a value.
(define-extended-language GO GI
  (Io (inherits v any ...))
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
  object-shadows : s (m ... M ... S ...) -> (s ...)
  ;; Substitutions of self are incremented.
  [(object-shadows [ℓ / e] _) ([ℓ / (inc-self e)])]
  ;; Otherwise collect the method names of the object, remove-shadows, and
  ;; increment if the substitution is to self.
  [(object-shadows [e / m_s ...] (m ... M ... S ...))
   (remove-shadows [(inc-self e) / m_s ...] m ... m_o ...)
   (where (m_o ...) (names M ... S ...))])

;; Apply remove-object-shadows for the object o to each substitution s.
(define-metafunction GI
  all-object-shadows : s ... (m ... M ... S ...) -> (s ...)
  [(all-object-shadows s ... (m ... M ... S ...))
   ,(append-map (λ (s) (term (object-shadows ,s (m ... M ... S ...))))
                (term (s ...)))])

;; Determine whether the given thing appears in the substitutions s.
(define-metafunction/extension graceless:not-in-subst GI
  not-in-subst : any s ... -> boolean)

;; Continue subst through expressions e.  This is necessary to avoid confusing
;; Redex with multiple ellipses in multiple inheritance.
(define-metafunction GI
  substs : s ... (e ...) -> (e ...)
  [(substs s ... (e ...)) ((subst s ... e) ...)])

;; Fetch the names bound by aliases in the transform clauses.
(define-metafunction GI
  alias-names : any ... -> (m ...)
  ;; No alias means no names.
  [(alias-names exclude ... any ...) ()]
  ;; Otherwise fetch the names, stopping at the optional exclude.
  [(alias-names alias (_ as m) ... exclude ... any ...) (m ...)])

;; Perform substitutions through an expression e.
(define-metafunction GI
  subst : s ... e -> e
  ;; Continue the substitution into an object body, removing substitutions
  ;; shadowed by the object.
  [(subst s ... (name o (object M ... S ...)))
   (object (subst-method s_p ... M) ... (subst-stmt s_p ... S) ...)
   (where (s_p ...) (all-object-shadows s ... (M ... S ...)))]
  ;; Substitutions get delayed in object bodies by an inherits clause, though
  ;; the substitution continues into the clause's expression.  Substitutions
  ;; that will obviously be removed from the object are immediately removed.
  [(subst s ... (name o (object (inherits e any ...) ... s_i ... M ... S ...)))
   (object (inherits (subst s ... e) any ...) ... s_i ... s_p ... M ... S ...)
   ;; Fetch the names bound by aliases.
   (where (m ...) (concat (alias-names any ...) ...))
   (where (s_p ...) (all-object-shadows s ... (m ... M ... S ...)))]
  ;; Continue the substitution into a request.
  [(subst s ... (r m e ...)) ((subst s ... r) m (subst s ... e) ...)]
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
  ;; Continue the substitution into a sequence.
  [(subst s ... (e ...)) ((subst s ... e) ...)]
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

;; Continue subst through methods into method bodies.  This is necessary to
;; avoid confusing Redex with multiple ellipses in multiple inheritance.
(define-metafunction GI
  subst-methods : s ... (M ...) -> (M ...)
  [(subst-methods s ... (M ...)) ((subst-method s ... M) ...)])

;; Continue subst through a method into its body, removing names which appear
;; in the parameter list.
(define-metafunction GI
  subst-method : s ... M -> M
  [(subst-method s ... (method m (x ...) e ...))
   (method m (x ...) (subst s_p ... e) ...)
   (where (s_p ...) (remove-all-shadows s ... x ...))])

;; Continue substitution into statements.  This ignores field names when
;; considering shadowing, as that will already have been taken care of by the
;; rule for objects in the subst function.
(define-metafunction GI
  subst-stmt : s ... S -> S
  [(subst-stmt s ... (def x = e)) (def x = (subst s ... e))]
  [(subst-stmt _ ... (var x)) (var x)]
  [(subst-stmt s ... (var x := e)) (var x := (subst s ... e))]
  [(subst-stmt s ... e) (subst s ... e)])

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
  names : M ... S ... -> (m ...)
  [(names M ... S ...)
   ,(append (term (method-names M ...)) (term (stmt-method-names S ...)))])

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
  body : [S y] ... -> (M ... e ...))

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

;; Zip a list of names with a list of list of statements.  This is necessary
;; because Redex can only generate a flat list of fresh variables, but we need
;; to combine it with multiple object bodies at once.
(define-metafunction GI
  zip-stmts : y ... (S ...) ... -> (([S y] ...) ...)
  ;; Terminate when there are no more elements to process.
  [(zip-stmts) ()]
  ;; Move to the next list when one is exhausted.
  [(zip-stmts y ... () (S ...) ...) (() ([S_p y_p] ...) ...)
   (where (([S_p y_p] ...) ...) (zip-stmts y ... (S ...) ...))]
  ;; Pair the next name with the next statement, and recurse.
  [(zip-stmts y y_r ... (S S_l ...) (S_r ...) ...)
   (([S y] [S_p y_p] ...) ([S_pr y_pr] ...) ...)
   (where (([S_p y_p] ...) ([S_pr y_pr] ...) ...)
          (zip-stmts y_r ... (S_l ...) (S_r ...) ...))])

;; Shallow flatten a list of lists.
(define-metafunction GI
  concat : (any ...) ... -> (any ...)
  [(concat) ()]
  [(concat (any ...) any_r ...)
   ,(append (term (any ...)) (term (concat any_r ...)))])

;; Join methods from multiple inherited sources, resolving conflicts.
(define-metafunction GI
  join : M ... -> (M ...)
  ;; No methods given, no method received.
  [(join) ()]
  ;; Drop an abstract method if there is another method with the same name.
  [(join (method m _ abstract) M_l ... (name M (method m _ ...)) M_r ...)
   (join M_l ... M M_r ...)]
  ;; If the method is not abstract, but there is an abstract method with the
  ;; same name, shuffle the concrete method to the back.  The abstract method
  ;; will be removed before it is processed again.
  [(join (name M (method m _ ...))
         M_l ... (name M_c (method m _ abstract)) M_r ...)
   (join M_l ... M_c M_r ... M)]
  ;; If there are at least two non-abstract methods, create an abstract method
  ;; and filter out all methods with that name.
  [(join (method m _ ...) M_l ... (method m _ ...) M_r ...)
   ,(cons (term (method m () abstract)) (term (join M_p ...)))
   (where (M_p ...) (override M_l ... M_r ... m))]
  ;; Otherwise this method's name is unique, continue the join.
  [(join M M_r ...) ,(cons (term M) (term (join M_r ...)))])

;; Process alias clauses on methods M.
(define-metafunction GI
  aliases : (m as m) ... M ... -> (M ...)
  ;; No more aliases to process.
  [(aliases M ...) (M ...)]
  ;; Process the next alias, and recurse on the rest.
  [(aliases (m as m_p) (m_r as m_rp) ... M ...)
   ;; The aliases are processed in turn, so here the result of processing the
   ;; current alias is fed back into aliases.
   (aliases (m_r as m_rp) ... M_p ...)
   (where (M_p ...) (apply-alias M ... (m as m_p)))])

;; Process a single alias clause on methods M.
(define-metafunction GI
  apply-alias : M ... (m as m) -> (M ...)
  ;; No more methods to process.
  [(apply-alias _) ()]
  ;; If the method matches the alias, make a copy with the aliasing name.
  [(apply-alias (method m (x ...) e) M ... (m as m_p))
   ((method m (x ...) e) (method m_p (x ...) e) M_p ...)
   (where (M_p ...) (apply-alias M ... (m as m_p)))]
  ;; Otherwise leave the method as-is.
  [(apply-alias M M_r ... (m as m_p)) (M M_p ...)
   (where (M_p ...) (apply-alias M_r ... (m as m_p)))])

;; Process excludes clauses on methods M.
(define-metafunction GI
  excludes : m ... M ... -> (M ...)
  ;; No more excludes to process.
  [(excludes M ...) (M ...)]
  ;; Process the next exclude, and recurse on the rest.
  [(excludes m m_r ... M ...)
   ;; As in aliases, the result of the single exclude is fed back into the
   ;; recursive call.
   (excludes m_r ... M_p ...)
   (where (M_p ...) (apply-exclude M ... m))])

;; Process a single exclude clause on methods M.
(define-metafunction GI
  apply-exclude : M ... m -> (M ...)
  ;; No more methods to process.
  [(apply-exclude _) ()]
  ;; If the method matches the alias, make it abstract.
  [(apply-exclude (method m _ ...) M ... m) ((method m () abstract) M_p ...)
   (where (M_p ...) (apply-exclude M ... m))]
  ;; Otherwise leave the method as-is.
  [(apply-exclude M M_r ... m) (M M_p ...)
   (where (M_p ...) (apply-exclude M_r ... m))])

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
   (--> [σ (in-hole EF ((ref ℓ_u as (ref ℓ_d)) m v ..._a))]
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
   (--> [σ (in-hole EF (object M ... S ...))]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(store σ (object (subst-method [(self 0) / m ...] M) ... M_f ...))
         (in-hole EF (subst [ℓ / (self 0)]
                            [(self 0) / m ...] (seq e ... (ref ℓ))))]
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
        (where (M_f ... e ...) (body [S y] ...))
        object)))

;; Partial small-step dynamic semantics of Graceless inheritance, extended with
;; simple object inheritance.  Must be extended with rules for object literals.
(define -->GPI
  (extend-reduction-relation
   -->GP
   GO
   #:domain p
   ;; Inherits concatenates the methods in the super object into the object
   ;; constructor and returns the resulting concatenation.  The actual object
   ;; reference will be built in the next step.
   (--> [σ (in-hole E (object (inherits (ref ℓ)
                                        alias ... (m_a as m_ap) ...
                                        exclude ... m_e ...) ...
                              s_d ... M ... S ...))]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and substituted fields.
        [σ (in-hole E (object M_up ...
                              (subst-method s ... M) ...
                              (subst-stmt s ... S) ...))]
        ;; Only execute this rule if there are inherits clauses to process.
        (side-condition (pair? (term ((m_e ...) ...))))
        ;; Collect the names of the definitions in the inheriting object.
        (where (m ...) (names M ... S ...))
        ;; Lookup the super objects.
        (where ((object F ... M_p ...) ...) ((lookup σ ℓ) ...))
        ;; Run the aliases on the methods from each inherited object.
        (where ((M_a ...) ...) ((aliases (m_a as m_ap) ... M_p ...) ...))
        ;; Run the excludes on the result of the aliases.
        (where ((M_e ...) ...) ((excludes m_e ... M_a ...) ...))
        ;; Concatenate the result of all the excludes.
        (where (M_c ...) (concat (M_e ...) ...))
        ;; Resolve conflicts between inherited methods.
        (where (M_u ...) (join M_c ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object.
        (where (M_up ...) (override M_u ... m ...))
        ;; Remove the shadowed substitutions before applying them to the body.
        (where (s ...) (all-object-shadows s_d ... (M_up ...)))
        inherits)))

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
   (--> [σ (in-hole E (object Io ... (inherits (v m v_a ...) any ...) I ...
                              s ... M ... S ...))]
        [σ_p (in-hole E (object Io ... (inherits e any ...) I ...
                                s ... M ... S ...))]
        ;; We can't pattern match here, because the result could be either a
        ;; single object or an expression sequence.
        (where ([σ_p e])
               ,(apply-reduction-relation -->GP (term [σ (v m v_a ...)])))
        ;; Ensure the resulting expression is fresh.
        (side-condition (term (is-fresh e)))
        inherits/transform-fresh)))
