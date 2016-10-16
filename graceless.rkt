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
     (t t ...)
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
  ;; Scope type
  (Γ (D ...))
  ;; Run-time object
  (O (d ...))
  ;; Object store
  (σ (O ...))
  ;; Evaluation context
  (E (E m t ...)
     (v m v ... E t ...)
     (m v ... E t ...)
     (E t ...)
     (x z ← E)
     hole))

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
   ;; Crash the program if a request results in uninitialised.  Requests are the
   ;; only way an uninitialised can appear in a program execution.
   (--> [σ (in-hole E (y m v ..._a))]
        [σ uninitialised]
        ;; Fetch the method which matches the request.
        (where (_ ... (method (m ([x : S] ..._a) → U) uninitialised) _ ...)
               (lookup σ y))
        uninitialised)
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
        request)
   ;; Set the field in the object and return the following expression.
   (--> [σ (in-hole E (y x ← v))]
        [(update σ y x v) (in-hole E done)]
        update)
   ;; Move to the next expression in a sequence when the first expression has
   ;; completed evaluating.
   (--> [σ (in-hole E (v t ...))]
        [σ (in-hole E (seq t ...))]
        sequence)
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
        object)))

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
