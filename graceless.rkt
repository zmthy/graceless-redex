#lang racket

(require redex)

(provide (except-out (all-defined-out)
                     eval
                     run))

;; The core syntax of Graceless.
(define-language Graceless
  ;; Method definition.
  ;;
  ;; This syntax differs somewhat from the text, which defines the body of a
  ;; method as a nested sequence and then treats the body as a single
  ;; pre-sequenced expression in all of the following rules.  We don't make that
  ;; assumption with this syntax definition, but it makes method bodies much
  ;; simpler to write.  We have to be sure to consider the presence of a body
  ;; sequence when matching on methods, and manually sequence the body with the
  ;; return expression when calling the method.
  (M (method m (x ...) e ... e))
  ;; Method name.
  (m x
     (x :=))
  ;; Statement.
  (S (def x = e)
     (var x)
     (var x := e)
     e)
  ;; Expression.
  (e o
     (r m e ...)
     (m e ...)
     self
     v)
  ;; Receiver.  No different from an expression in the base model.
  (r e)
  ;; Object expression.
  (o (object M ... S ...))
  ;; Value.
  (v done)
  ;; Variable name.
  (x variable-not-otherwise-mentioned)
  (y variable-not-otherwise-mentioned))

;; The runtime syntax of Graceless.
(define-extended-language G Graceless
  (e ....
     ;; The text defines these as pairs, but it's nicer to use a list here
     ;; instead, so long as there's at least two expressions in there.
     (e e ... e)
     (e y ->)
     (e y <- e)
     ;; This self reference has a De Bruijn index, which allows an inner object
     ;; to refer to an outer one.  These indices are implicit in the text.  The
     ;; source-level self is sugar for (self 0).
     (self n)
     uninitialised)
  ;; Self index.
  (n natural)
  (v ....
     (ref ℓ))
  ;; Memory location.
  (ℓ natural)
  ;; Object store.
  (σ (O ...))
  ;; Runtime object.
  (O (object F ... M ...))
  ;; Field mapping.
  (F [x v])
  ;; Substitution.
  (s [v x]
     ;; Substitution for some self.
     [ℓ (self n)]
     ;; Qualifying substitution to some self.
     [(self n) m ...])
  ;; Program.
  (p [σ e])
  ;; Evaluation context.
  (E (E m e ...)
     (v m v ... E e ...)
     (m v ... E e ...)
     (E e ...)
     (v x <- E)
     hole))

;; Remove any names from the substitution s which are shadowed by the names m.
;; If the substitution still has names remaining, it is returned as the sole
;; element of the list, otherwise the list is empty.
(define-metafunction G
  remove-shadows : s m ... -> (s ...)
  ;; If the name x appears in m, remove it.
  [(remove-shadows [_ x] _ ... x _ ...) ()]
  ;; If any name in the substitution appears in m, recurse without it.
  [(remove-shadows [any ... m m_s ...] m_l ... m m_r ...)
   (remove-shadows [any ... m_s ...] m_l ... m m_r ...)]
  ;; If all of the names have been removed from a substitution, remove it.
  [(remove-shadows [any] _ ...) ()]
  ;; Otherwise, retain the remaining substitution.
  [(remove-shadows s _ ...) (s)])

;; Increment if the expression e is a self reference, otherwise just return the
;; expression.
(define-metafunction G
  inc-self : e -> e
  [(inc-self (self n)) (self ,(add1 (term n)))]
  [(inc-self e) e])

;; Remove any names from the substitution s which are shadowed by a definition
;; in the object o.  If the substitution still has names remaining, it is
;; returned as the sole element of the list, otherwise the list is empty.  Any
;; substitution for self is incremented, as the object it refers to will be
;; further away inside the inner object.
(define-metafunction G
  object-shadows : s o -> (s ...)
  ;; Substitutions of self are incremented.
  [(object-shadows [ℓ any] _) ([ℓ (inc-self any)])]
  ;; Otherwise collect the method names of the object, remove-shadows, and
  ;; increment if the substitution is to self.
  [(object-shadows [e m_s ...] (object M ... S ...))
   (remove-shadows [(inc-self e) m_s ...] m_o ...)
   (where (m_o ...) (names M ... S ...))])

;; Determine whether the given thing appears in the substitutions s.
(define-metafunction G
  not-in-subst : any s ... -> boolean
  ;; This matching syntax captures any name in any kind of substitution.
  [(not-in-subst any _ ... [_ _ ... any _ ...] _ ...) #f]
  ;; In any other case, it is not in the list.
  [(not-in-subst _ _ ...) #t])

;; Perform substitutions through an expression e.
(define-metafunction G
  subst : s ... e -> e
  ;; Continue the substitution into an object body, removing substitutions
  ;; shadowed by the object.
  [(subst s ... (name o (object M ... S ...)))
   (object (subst-method s_p ... M) ... (subst-stmt s_p ... S) ...)
   (where (s_p ...) ,(append-map (λ (s) (term (object-shadows ,s o)))
                                 (term (s ...))))]
  ;; Continue the substitution into a request.
  [(subst s ... (e m e_a ...))
   ((subst s ... e) m (subst s ... e_a) ...)]
  ;; Substitute out an unqualified request with no arguments for a value v as
  ;; long as there is no later substitution in the list.
  [(subst _ ... [v x] s ... (x)) v
   (side-condition (term (not-in-subst x s ...)))]
  ;; Substitute out an unqualified request for one qualified in a reference to
  ;; ℓ, so long as there is no later substitution in the list.  Continue the
  ;; substitution into the arguments afterwards.
  [(subst s_l ... (name s [(self n) _ ... m _ ...]) s_r ... (m e ...))
   (subst s_l ... s s_r ... ((self n) m e ...))
   (side-condition (term (not-in-subst m s_r ...)))]
  ;; Just continue the substitution into a request when no substitution applies.
  [(subst s (m e ...)) (m (subst s e) ...)]
  ;; Continue the substitution into a sequence.
  [(subst s ... (e ...)) ((subst s ... e) ...)]
  ;; Continue the substitution into a field lookup.
  [(subst s ... (e y ->)) ((subst s ... e) y ->)]
  ;; Continue the substitution into an assignment.
  [(subst s ... (e y <- e_a))
   ((subst s ... e) y <- (subst s ... e_a))]
  ;; Substitute out self for the given reference, so long as there is no later
  ;; substitution in the list.
  [(subst _ ... [ℓ (self n)] s ... (self n)) (ref ℓ)
   (side-condition (term (not-in-subst (self n) s ...)))]
  ;; As above, for the direct self sugar.
  [(subst _ ... [ℓ (self 0)] s ... self) (ref ℓ)
   (side-condition (term (not-in-subst (self 0) s ...)))]
  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... e) e])

;; Continue subst through methods into method bodies, removing names which
;; appear in the parameter list.
(define-metafunction G
  subst-method : s ... M -> M
  [(subst-method s ... (method m (x ...) e ...))
   (method m (x ...) (subst s_p ... e) ...)
   (where (s_p ...) ,(append-map (λ (s) (term (remove-shadows ,s x ...)))
                                 (term (s ...))))])

;; Continue substitution into statements.  This ignores field names when
;; considering shadowing, as that will already have been taken care of by the
;; rule for objects in the subst function.
(define-metafunction G
  subst-stmt : s ... S -> S
  [(subst-stmt s ... (def x = e)) (def x = (subst s ... e))]
  [(subst-stmt _ ... (var x)) (var x)]
  [(subst-stmt s ... (var x := e)) (var x := (subst s ... e))]
  [(subst-stmt s ... e) (subst s ... e)])

;; Store a new runtime object O in the store σ.  The resulting location is the
;; same as calculated by fresh-location on the same store, before the object is
;; added.
(define-metafunction G
  store : σ O -> σ
  [(store σ O) ,(append (term σ) (term (O)))])

;; Fetch a fresh location for the store.
(define-metafunction G
  fresh-location : σ -> ℓ
  [(fresh-location σ) ,(length (term σ))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction G
  lookup : σ ℓ -> O
  [(lookup σ ℓ) ,(list-ref (term σ) (term ℓ))])

;; Retrieve the value of the field x in the object at the location ℓ in the
;; store σ.
(define-metafunction G
  get-field : σ ℓ x -> v or uninitialised
  [(get-field σ ℓ x) (get-field-in (lookup σ ℓ) x)])

;; Retrieve the value of the field x in the object O.
(define-metafunction G
  get-field-in : O x -> v or uninitialised
  [(get-field-in (object _ ... [x v] _ ...) x) v]
  [(get-field-in _ _) uninitialised])

;; Execute an assignment in the store σ by setting the field x in the object at
;; location ℓ to the value v.
(define-metafunction G
  set-field : σ ℓ x v -> σ
  [(set-field σ ℓ x v) ,(list-update (term σ)
                                     (term ℓ)
                                     (λ (O) (term (set-field-in ,O x v))))])

;; Set the field x in the object O to have the value v.
(define-metafunction G
  set-field-in : O x v -> O
  [(set-field-in (object F_l ... [x _] F_r ... M ...) x v)
   (object F_l ... (x v) F_r ... M ...)]
  [(set-field-in (object F ... M ...) x v) (object F ... [x v] M ...)])

;; Collect all of the method names of the methods M and generated accessors of
;; fields in the statement list S.
(define-metafunction G
  names : M ... S ... -> (m ...)
  [(names M ... S ...)
   ,(append (term (method-names M ...)) (term (stmt-method-names S ...)))])

;; Collect all of the method names in the object o, including those generated by
;; getter and setter methods of fields.
(define-metafunction G
  method-names : M ... -> (m ...)
  [(method-names (method m _ ...) ...) (m ...)])

;; Collect the corresponding method names of generated accessor methods in the
;; statements S.
(define-metafunction G
  stmt-method-names : S ... -> (m ...)
  [(stmt-method-names S ...)
   ,(append-map (λ (S) (term (stmt-to-method-names ,S))) (term (S ...)))])

;; Convert the statement S into the names of generated accessor methods if it is
;; a field, otherwise an empty list.
(define-metafunction G
  stmt-to-method-names : S -> (m ...)
  [(stmt-to-method-names (def x = _)) (x)]
  [(stmt-to-method-names (var x _ ...)) (x (x :=))]
  [(stmt-to-method-names e) ()])

;; Convert the statements S into accessor methods M and an object body e.
(define-metafunction G
  body : [S y] ... -> (M ... e ...)
  [(body [(def x = e) y] [S y_r] ...)
   ,(append (term (accessors def x y))
            (term (M ... (self y <- e) e_r ...)))
   (where (M ... e_r ...) (body [S y_r] ...))]
  [(body [(var x) y] [S y_r] ...)
   ,(append (term (accessors var x y))
            (term (M ... e_r ...)))
   (where (M ... e_r ...) (body [S y_r] ...))]
  [(body [(var x := e) y] [S y_r] ...)
   ,(append (term (accessors var x y))
            (term (M ... (self y <- e) e_r ...)))
   (where (M ... e_r ...) (body [S y_r] ...))]
  [(body [e _] [S y_r] ...) (M ... e e_r ...)
   (where (M ... e_r ...) (body [S y_r] ...))]
  [(body) ()])

;; Construct the accessor methods for the given field type with the public name
;; x and the private name y.
(define-metafunction G
  accessors : any x y -> (M ...)
  [(accessors def x y) ((method x () (self y ->)))]
  [(accessors var x y) ((method x () (self y ->))
                        (method (x :=) (x) (self y <- (x))))])

;; Sequence a series of expressions into a single expression.
(define-metafunction G
  seq : e ... -> e
  [(seq e) e]
  [(seq e ...) (e ...)])

;; Ensure that the given names are unique.
(define-metafunction G
  unique : m ... -> boolean
  [(unique _ ... m _ ... m _ ...) #f]
  [(unique _ ...) #t])

;; Ensure the given expression is not uninitialised.
(define-metafunction G
  initialised : e -> boolean
  [(initialised uninitialised) #f]
  [(initialised _) #t])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   G
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
   (--> [σ (in-hole E ((ref ℓ) m v ..._a))]
        ;; Substitute the variable names for the arguments and the receiver for
        ;; self.  This rule is slightly different from the text, which assumes
        ;; that the body is interpreted as a single sequenced expression.  Here
        ;; we manually sequence the body.
        [σ (in-hole E (subst [ℓ (self 0)] [v x] ... (seq e ...)))]
        ;; Fetch the one method with the name given in the request.
        (where (object _ ... (method m (x ..._a) e ...) _ ...) (lookup σ ℓ))
        request)
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [σ (in-hole E (object M ... S ...))]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(store σ (object (subst-method [(self 0) m ...] M) ... M_f ...))
         (in-hole E (subst [ℓ (self 0)] [(self 0) m ...] (seq e ... (ref ℓ))))]
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

;; Wrap a term t into an initial program with an empty store.
(define (program t) (term [() ,t]))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Evaluate an expression starting with an empty store.
(define-metafunction G
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->G until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction G
  run : p -> [σ e]
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->G (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error.
(define (eval-->G t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->G,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->G t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->G.
(define (traces-->G t) (traces -->G (program t)))
