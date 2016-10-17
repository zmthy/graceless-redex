#lang racket

(require redex)

(provide (except-out (all-defined-out)
                     eval
                     run))

;; The core syntax of Graceless.
(define-language Graceless
  ;; Program
  (p [σ t])
  ;; Variables
  (x (self n) y z)
  ;; Store references
  (y n)
  ;; Abstract variables
  (z variable-not-otherwise-mentioned)
  ;; Type
  (T ⊥
     Done
     (type D ...)
     (∨ T T))
  ;; Aliases for type
  (S T)
  (U T)
  ;; Signature
  (D (m ([z : S] ...) → U))
  ;; Declaration
  (d (method (m ([z : S] ...) → U) o))
  ;; Term
  (t (object d ... t)
     (r m t ...)
     (m t ...)
     (self n)
     ((self n) z ← t)
     (y z ← t)
     (t t t ...)
     v)
  ;; Receiver, no different from a term in the base model.
  (r t)
  ;; Value
  (v y
     done)
  ;; Evaluation outcome
  (o t
     uninitialised)
  ;; Method name
  (m z
     (z ≔))
  ;; Substitution
  (s [v / z]
     [v / (self n)]
     [(self n) / a])
  ;; Method identifier
  (a (m n))
  ;; Naturals
  (n natural)
  ;; Run-time object
  (O (d ...))
  ;; Object store
  (σ (O ...))
  ;; Scope type
  (Γ (G ...))
  (G D
     [self : T])
  ;; Store type
  (Σ ((D ...) ...))
  ;; Evaluation context
  (E hole
     (E m t ...)
     (v m v ... E t ...)
     (m v ... E t ...)
     (E t ...)
     (x z ← E)))

;; The ⊤ symbol is equivalent to the structural type with no signatures.
(define-term ⊤ (type))

;; Intersection combines two types into their meet on the subtyping lattice.
(define-metafunction Graceless
  ∧ : T T -> T
  ;; A type meets with itself.
  [(∧ T T) T]
  ;; Top meets any other type.
  [(∧ (type) T) T]
  [(∧ T (type)) T]
  ;; Bottom meets all types.
  [(∧ ⊥ T) ⊥]
  [(∧ T ⊥) ⊥]
  ;; Intersection distributes over union.
  [(∧ (∨ T_1 T_2) T_3) (∨ (∧ T_1 T_3) (∧ T_2 T_3))]
  [(∧ T_1 (∨ T_2 T_3)) (∨ (∧ T_1 T_2) (∧ T_1 T_3))]
  ;; Done fails to meet any type it has not already met.
  [(∧ Done T) ⊥]
  [(∧ T Done) ⊥]
  ;; Structural types join their signatures together.
  [(∧ (type D_1 ...) (type D_2 ...)) (type D ...)
   (where (D ...) (∧-sig (D_1 ...) (D_2 ...)))])

;; Intersection between signatures unions parameters and intersects return
;; types.  This proceeds by attempting to find a signature in the second list
;; with the same name and arity as the signature at the head of the first list.
(define-metafunction Graceless
  ∧-sig : (D ...) (D ...) -> (D ...)
  ;; If either list is empty, return the other one.
  [(∧-sig () (D ...)) (D ...)]
  [(∧-sig (D ...) ()) (D ...)]
  ;; Intersect signatures with a matching identity.  There's guaranteed to be at
  ;; most one match by the well-formedness properties of structural types.
  [(∧-sig ((m ([x_1 : S_1] ..._x) → U_1) D_1 ...)
          (D_2 ... (m ([x_2 : S_2] ..._x) → U_2) D_3 ...))
   ((m ([x_1 : (∨ S_1 S_2)] ...) → (∧ U_1 U_2)) D ...)
   (where (D ...) (∧-sig (D_1 ...) (D_2 ... D_3 ...)))]
  ;; No match means keep the signature and proceed on the rest.
  [(∧-sig (D_1 D_2 ...) (D_3 ...)) (D_1 D ...)
   (where (D ...) (∧-sig (D_2 ...) (D_3 ...)))])

;; Remove a substitution if it is shadowed by any of the identifiers a.  If the
;; substitution is not removed, it is returned as the sole element of the list,
;; otherwise the list is empty.
(define-metafunction Graceless
  remove-shadows : s a ... -> (s ...)
  ;; If the variable z is shadowed by an identifier, remove it.
  [(remove-shadows [_ / z] _ ... (z 0) _ ...) ()]
  ;; If the substitution is shadowed by an method, remove it.
  [(remove-shadows [_ / a] _ ... a _ ...) ()]
  ;; Otherwise, retain the substitution.
  [(remove-shadows s a ...) (s)])

;; Increment the self reference, if the given syntax is one, otherwise return it
;; unchanged.
(define-metafunction Graceless
  inc-self : any -> any
  [(inc-self (self n)) (self ,(add1 (term n)))]
  [(inc-self any) any])

;; As with remove-shadows, but increment any self reference in the substitution.
(define-metafunction Graceless
  object-shadows : s a ... -> (s ...)
  [(object-shadows [t / any] a ...)
   (remove-shadows [(inc-self t) / (inc-self any)] a ...)])

;; Apply remove-object-shadows for the object o to each substitution s.
(define-metafunction Graceless
  all-object-shadows : s ... d ... -> (s ...)
  [(all-object-shadows s ... d ...)
   ,(append-map (λ (s) (term (object-shadows ,s a ...)))
                (term (s ...)))
   (where (a ...) ((identify (signature d)) ...))])

;; Determine whether the given thing is being substituted out by the
;; substitutions s.
(define-metafunction Graceless
  not-in-subst : any s ... -> boolean
  ;; This matching syntax captures any name in any standard substitution.
  [(not-in-subst any _ ... [_ ... / any] _ ...) #f]
  ;; In any other case, it is not in the list.
  [(not-in-subst _ _ ...) #t])

;; Perform substitutions through an expression e.
(define-metafunction Graceless
  subst : s ... o -> o
  ;; Continue the substitution into an object body, removing substitutions
  ;; shadowed by the object.
  [(subst s ... (object d ... t))
   (object (subst-decl s_o ... d) ... (subst s_o ... t))
   (where (s_o ...) (all-object-shadows s ... d ...))]
  ;; Continue the substitution into a request.
  [(subst s ... (r m t ...)) ((subst s ... r) m (subst s ... t) ...)]
  ;; Substitute out an unqualified request with no arguments for a value v as
  ;; long as there is no later substitution in the list.
  [(subst _ ... [v / x] s ... (x)) v
   (side-condition (term (not-in-subst x s ...)))]
  ;; Substitute out an unqualified request for one qualified in a reference to
  ;; y, so long as there is no later substitution in the list.  Continue the
  ;; substitution into the arguments afterwards.
  [(subst s_l ... (name s [(self n_s) / (m n)]) s_r ... (m t ...))
   (subst s_l ... s s_r ... ((self n_s) m (subst s_l ... s s_r ... t) ...))
   ;; Ensure the number of arguments matches the number of parameters.
   (side-condition (= (term n) (length (term (t ...)))))
   (side-condition (term (not-in-subst (m n) s_r ...)))]
  ;; Just continue the substitution into a request when no substitution applies.
  [(subst s ... (m t ...)) (m (subst s ... t) ...)]
  ;; Continue the substitution into an assignment.
  [(subst s ... (x z ← t)) ((subst s ... x) z ← (subst s ... t))]
  ;; Substitute out self for the given reference, so long as there is no later
  ;; substitution in the list.
  [(subst _ ... [v / (self n)] s ... (self n)) v
   (side-condition (term (not-in-subst (self n) s ...)))]
  ;; Continue the substitution into a sequence.
  [(subst s ... (t ...)) ((subst s ... t) ...)]
  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... o) o])

;; Continue subst through methods into method bodies, removing names which
;; appear in the parameter list.
(define-metafunction Graceless
  subst-decl : s ... d -> d
  [(subst-decl s ... (method (m ([x : S] ...) → U) o))
   (method (m ([x : S] ...) → U) (subst s_d ... o))
   (where (s_d ...) ,(append-map (λ (s) (term (remove-shadows ,s (x 0) ...)))
                                 (term (s ...))))])

;; Store a new runtime object O in the store σ.  The resulting location is the
;; same as calculated by fresh-location on the same store, before the object is
;; added.
(define-metafunction Graceless
  store : σ O -> σ
  [(store σ O) ,(append (term σ) (term (O)))])

;; Fetch a fresh location for the store.
(define-metafunction Graceless
  fresh-location : σ -> y
  [(fresh-location σ) ,(length (term σ))])

;; Search for the object at the location ℓ in the store σ.
(define-metafunction Graceless
  lookup : σ y -> O
  [(lookup σ y) ,(list-ref (term σ) (term y))])

;; Set the method x in σ(y) to have the body v.
(define-metafunction Graceless
  update : σ y x v -> σ
  [(update σ y x v) ,(list-update (term σ)
                                  (term y)
                                  (λ (O) (term (update-in ,O x v))))])

;; Set the method x in the run-time object O to have the body v.
(define-metafunction Graceless
  update-in : O x v -> O
  [(update-in (d_l ... (method (x () → U) o) d_r ...) x v)
   (d_l ... (method (x () → U) v) d_r ...)])

;; Fetch the signature of a declaration.
(define-metafunction Graceless
  signature : d -> D
  [(signature (method D o)) D])

;; Identify a method based on its signature.
(define-metafunction Graceless
  identify : D -> a
  [(identify (m ([x : S] ...) → U)) (m ,(length (term (x ...))))])

;; Sequence a series of expressions into a single expression.
(define-metafunction Graceless
  seq : t ... -> t
  [(seq t) t]
  [(seq t ...) (t ...)])

;; Ensure that the given names are unique.
(define-metafunction Graceless
  unique : a ... -> boolean
  [(unique _ ... a _ ... a _ ...) #f]
  [(unique _ ...) #t])

;; Ensure the given expression is not uninitialised.
(define-metafunction Graceless
  initialised : t -> boolean
  [(initialised uninitialised) #f]
  [(initialised _) #t])

;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   Graceless
   #:domain [σ o]
   #:arrow :-->
   ;; Crash the program if a request results in uninitialised.  Requests are the
   ;; only way an uninitialised can appear in a program execution.
   (:--> [σ (in-hole E (y m v ..._a))]
         [σ uninitialised]
         ;; Fetch the method which matches the request.
         (where (_ ... (method (m ([x : S] ..._a) → U) uninitialised) _ ...)
                (lookup σ y))
         Uninitialised)
   ;; Substitute for unqualified requests to the parameters, and return the body
   ;; of the method.
   (--> [σ (in-hole E (y m v ..._a))]
        ;; Substitute the variable names for the arguments and the receiver for
        ;; self.  This rule is slightly different from the text, which assumes
        ;; that the body is interpreted as a single sequenced expression.  Here
        ;; we manually sequence the body.
        [σ (in-hole E (subst [y / (self 0)] [v / x] ... t))]
        ;; Fetch the method which matches the request.
        (where (_ ... (method (m ([x : S] ..._a) → U) t) _ ...) (lookup σ y))
        Request)
   ;; Update the method and return done.
   (--> [σ (in-hole E (y x ← v))]
        [(update σ y x v) (in-hole E done)]
        Update)
   ;; Move to the next expression in a sequence when the first expression has
   ;; completed evaluating.
   (--> [σ (in-hole E (v t ...))]
        [σ (in-hole E (seq t ...))]
        Sequence)
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [σ (in-hole E (object d ... t))]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(store σ ((subst-decl [(self 0) / a] ... d) ...))
         (in-hole E (subst [y / (self 0)]
                           [(self 0) / a] ... (t y)))]
        ;; Fetch a fresh location.
        (where y (fresh-location σ))
        ;; The method names are used for substituting local requests, as well as
        ;; ensuring the resulting object has unique method names.
        (where (a ...) ((identify (signature d)) ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique a ...)))
        Object)
   with [(:--> (in-hole E fst) (in-hole E snd))
         (--> fst snd)]))

;; An auxiliary judgment to select a compatible signature from a list.
(define-judgment-form Graceless
  #:mode (select-sig I I O)
  #:contract (select-sig Γ a D)

  [(side-condition ,(equal? (term a) (term (identify D))))
   ------------------------------------------------------- Here
   (select-sig (D G ...) a D)]

  [(select-sig (G ...) a D_a)
   ;; This is not necessary for normal structural types, which will never
   ;; feature two signatures with the same identifier, but it can be necessary
   ;; for a type environment Γ where methods can shadow others.
   (side-condition ,(not (equal? (term a) (term (identify D)))))
   ------------------------------------------------------------- There
   (select-sig (D G ...) a D_a)])

;; An auxiliary judgment to select a self type from an environment.
(define-judgment-form Graceless
  #:mode (select-self I I O)
  #:contract (select-self Γ n T)

  [------------------------------------ Here
   (select-self ([self : T] G ...) 0 T)]

  [(side-condition ,(> (term n) 1))
   (select-self (G ...) ,(sub1 (term n)) T)
   ---------------------------------------- There
   (select-self ([self : _] G ...) n T)]

  [(select-self (G ...) n T)
   --------------------------- Decl
   (select-self (D G ...) n T)])

;; Subtyping.
(define-judgment-form Graceless
  #:mode (subtype I I)
  #:contract (subtype T T)

  [------------- Refl
   (subtype T T)]

  [------------- Top
   (subtype T ⊤)]

  [------------- Bot
   (subtype ⊥ T)]

  [(subtype T T_1)
   ----------------------- Or/Left
   (subtype T (∨ T_1 T_2))]

  [(subtype T T_2)
   ----------------------- Or/Right
   (subtype T (∨ T_1 T_2))]

  [(subtype T_1 T)
   (subtype T_2 T)
   ----------------------- Or
   (subtype (∨ T_1 T_2) T)]

  [(select-sig (D_1 ...) (identify D_2) D) ...
   (subsig D D_2) ...
   ----------------------------------------------- Signatures
   (subtype (type D_1 ...) (type D_2 ...))])

;; Signature compatibility.
(define-judgment-form Graceless
  #:mode (subsig I I)
  #:contract (subsig D D)

  [(subtype S_2 S_1) ...
   (subtype U_1 U_2)
   ---------------------------------------------------------------- Method
   (subsig (m ([x : S_1] ..._x) → U_1) (m ([z : S_2] ..._x) → U_2))])

;; Signature absence.
(define-judgment-form Graceless
  #:mode (sig-not-in I I)
  #:contract (sig-not-in T a)

  [------------------- Done
   (sig-not-in Done a)]

  [(side-condition ,(not (ormap (λ (D)
                                  (equal? (term a) (term (identify ,D))))
                                (term (D_t ...)))))
   ---------------------------------------------------------------------- Type
   (sig-not-in (type D_t ...) a)]

  [(sig-not-in T_1 a)
   (sig-not-in T_2 a)
   -------------------------- Or
   (sig-not-in (∨ T_1 T_2) a)])

;; Signature lookup.  Accepts the signature identity as an input, and outputs
;; the signature with that identity in the type (if it is present).
(define-judgment-form Graceless
  #:mode (sig-in I I O)
  #:contract (sig-in T a D)

  [(select-sig (D_t ...) a D)
   --------------------------- Type
   (sig-in (type D_t ...) a D)]

  [------------------------------------------------------------- Bot
   (sig-in ⊥ (m n) (m ,(make-list (term n) (term [x : ⊤])) → ⊥))]

  [(sig-in T_1 a (m ([x : S_1] ..._x) → U_1))
   (sig-in T_2 a (m ([z : S_2] ..._x) → U_2))
   ----------------------------------------------------------------- Or
   (sig-in (∨ T_1 T_2) a (m ([x : (∧ S_1 S_2)] ...) → (∨ U_1 U_2)))]

  [(sig-in T_1 a D)
   (sig-not-in T_2 a)
   ------------------------ Or/Left
   (sig-in (∨ T_1 T_2) a D)]

  [(sig-in T_2 a D)
   (sig-not-in T_1 a)
   ------------------------ Or/Right
   (sig-in (∨ T_1 T_2) a D)])

;; Term typing.
(define-judgment-form Graceless
  #:mode (typed I I I O)
  #:contract (typed Σ Γ o T)

  [--------------------------- Uninitialised
   (typed Σ Γ uninitialised ⊥)]

  [--------------------- Done
   (typed Σ Γ done Done)]

  [(side-condition ,(< (term y) (length (term Σ))))
   (where (D ...) ,(list-ref (term Σ) (term y)))
   ------------------------------------------- Reference
   (typed Σ Γ y (type D ...))]

  [(typed Σ Γ t T)
   (typed Σ Γ (seq t_s ...) T_s)
   ----------------------------- Sequence
   (typed Σ Γ (t t_s ...) T_s)]

  [(where (D ...) ((signature d) ...))
   (decl-typed Σ ([self : (type D ...)] D ... . Γ) d D) ...
   (typed Σ ([self : (type D ...)] D ... . Γ) t T)
   (side-condition ,(not (check-duplicates (term ((identify D) ...)))))
   -------------------------------------------------------------------- Object
   (typed Σ Γ (object d ... t) (type D ...))]

  [(typed Σ Γ t_1 T_1)
   (sig-in T_1 (m ,(length (term (t_2 ...))))
           (m ([x : S] ...) → U))
   (typed Σ Γ t_2 T_2) ...
   (subtype T_2 S) ...
   ------------------------------------------ Request/Qualified
   (typed Σ Γ (t_1 m t_2 ...) U)]

  [(select-sig Γ (m ,(length (term (t ...))))
               (m ([x : S] ...) → U))
   (typed Σ Γ t T) ...
   (subtype T S) ...
   ------------------------------------------ Request/Unqualified
   (typed Σ Γ (m t ...) U)]

  ;; A special case which is ignored in the paper rules because it is presumed
  ;; to be covered by Request/Unqualified.  Explicitly indexing the self
  ;; variable makes it more difficult to ensure that it is covered by existing
  ;; rules, so we just have a distinct rule for it.
  [(select-self Γ n T)
   ---------------------- Self
   (typed Σ Γ (self n) T)]

  [(typed Σ Γ x T_1)
   (typed Σ Γ t T_2)
   (sig-in T_1 (z 0) (z () → U))
   (subtype T_2 U)
   ----------------------------- Update
   (typed Σ Γ (x z ← t) Done)])

;; Declaration typing.
(define-judgment-form Graceless
  #:mode (decl-typed I I I O)
  #:contract (decl-typed Σ Γ d D)

  [(typed Σ ((x () → S) ... . Γ) o T)
   (subtype T U)
   -------------------------------------------- Method
   (decl-typed Σ Γ
               (method (m ([x : S] ...) → U) o)
               (m ([x : S] ...) → U))])

;; Store typing.
(define-judgment-form Graceless
  #:mode (store-typed I O)
  #:contract (store-typed σ Σ)

  [(where (D ...) ((signature d) ...))
   (decl-typed (D ...) (((self 0) : (type D))) d D) ...
   ---------------------------------------------------- Store
   (store-typed (d ...) (D ...))])

;; Wrap a term t into an initial program with an empty store.
(define (program t) (term [() ,t]))

;; Progress the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Evaluate an expression starting with an empty store.
(define-metafunction Graceless
  eval : t -> t
  [(eval t) ,(second (term (run [() t])))])

;; Apply the reduction relation -->G until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction Graceless
  run : p -> [σ o]
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ y]) [σ (object d ... done)]
   (where (d ...) (lookup σ y))]
  [(run p) (run p_′)
   (where (p_′) ,(step-->G (term p)))]
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
