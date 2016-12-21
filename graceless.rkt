#lang racket

(require redex)

(provide (except-out (all-defined-out)
                     eval
                     run))

;; This is the core language which we extend to implement inheritance and
;; nominal typing later on.  Graceless defines the basic terms, types,
;; reduction, and typing judgments.  A program is a pair of an object store and
;; a term that will be executed in the context of that store.

;; The core syntax of Graceless.
(define-language Graceless
  ;; Program
  (p [σ t])
  ;; Variable
  (x y
     z)
  ;; Store reference
  (y natural)
  ;; Abstract variable
  (z variable-not-otherwise-mentioned
     (self n))
  ;; Direct object reference
  (w (self n)
     y)
  ;; Type
  (T (⋃ S ...))
  ;; Structural type
  (S (type D ...))
  ;; Declaration
  (D (m ([z : ∞T] ...) → ∞T))
  ;; Delayed type (a type, or a promise of a type)
  (∞T any)
  ;; Definition
  (d (method (m ([z : ∞T] ...) → ∞T) t))
  ;; Term
  (t (object d ... t)
     (r m t ...)
     (m t ...)
     (w ← d)
     (↥ t)
     (t ⤒ b)
     (t ∋ a b b)
     [t t]
     w)
  ;; Variable reference
  (tx x (x))
  ;; Block
  (b {z → t})
  ;; Value
  (v y)
  ;; Receiver
  (r t)
  ;; Method name
  (m variable-not-otherwise-mentioned
     (variable-not-otherwise-mentioned ≔))
  ;; Naturals
  (n natural)
  ;; Substitution
  (s [x / z]
     [w / a])
  ;; Method identifier
  (a [m n])
  ;; Run-time object
  (O (d ...))
  ;; Object store
  (σ (O ...))
  ;; Typing environment
  (Γ (γ ...))
  ;; Environment binding
  (γ [y : T]
     [z : T]
     [self : T])
  ;; Rescue-free evaluation sub-context
  (G (F m t ...)
     (v m v_i ... F t ...)
     (m v_i ... F t ...)
     (↥ F)
     (F ∋ a b_1 b_2)
     [F t])
  ;; Rescue-free evaluation context
  (F hole
     G)
  ;; General evaluation context
  (E F
     (in-hole F (E ⤒ b))))

;; Unwraps a variable reference to its underlying variable, if the syntax is a
;; request.  Otherwise is the identity on variables.
(define-metafunction Graceless
  unwrap : tx -> x
  [(unwrap (x)) x]
  [(unwrap x)   x])


;; The top and bottom type symbols are used to simplify the discussion of the
;; subtyping lattice.  In general we treat empty and single-element unions
;; without referring to the wrapping ∪ symbol, but here we need to be more careful
;; with our metavariables.

;; The top type.
(define-term ⊤ (⋃ (type)))

;; The bottom type.
(define-term ⊥ (⋃))


;; In order to support infinite depth in the type syntax, the type annotations
;; on a signature may contain type promises.  These aren't types on their own,
;; so it would help to have a function to transform a delayed type into a real
;; type.

;; Forces a type if it is delayed.
(define-metafunction Graceless
  ω : ∞T -> T
  ;; If the type is not delayed, just return it.
  [(ω T)  T]
  ;; Force the promise otherwise.
  [(ω ∞T) ,(force (term ∞T))
   ;; Since the ∞T pattern is defined as any, we get a better error message in
   ;; the case that a non-promise is passed if we include a check that the input
   ;; was actually a promise.
   (side-condition (promise? (term ∞T)))])


;; Next we need to define substitution over terms.  Substitution in this
;; language is more complicated than normal, because method names appear in
;; local scope as well, so we need two different substitution forms.  Method
;; calls without arguments are also indistinguishable from regular variable
;; references.

;; We begin by dealing with shadowing.  When a substitution proceeds into a
;; method definition or an object constructor, if a parameter definition or
;; method identifier overlaps with the substitution then the definition shadows
;; it and it no longer applies to the body.

;; Removes a substitution if it is shadowed by any of the identifiers a.  If the
;; substitution is not removed, it is returned as the sole element of the list,
;; otherwise the list is empty.
(define-metafunction Graceless
  remove-shadows : s a ... -> (s ...)
  ;; If the variable z is shadowed by an identifier, remove it.
  [(remove-shadows [_ / z] _ ... (z 0) _ ...) ()]
  ;; If the substitution is shadowed by a method, remove it.
  [(remove-shadows [_ / a] _ ... a _ ...) ()]
  ;; Otherwise, retain the substitution.
  [(remove-shadows s a ...) (s)])

;; Increments the self reference, if the given syntax is one, otherwise return
;; it unchanged.
(define-metafunction Graceless
  inc-self : any -> any
  [(inc-self (self n)) (self ,(add1 (term n)))]
  [(inc-self any) any])

;; As with remove-shadows, but increments any self reference in the
;; substitution.
(define-metafunction Graceless
  object-shadows : s a ... -> (s ...)
  [(object-shadows [any_1 / any_2] a ...)
   (remove-shadows [(inc-self any_1) / (inc-self any_2)] a ...)])

;; Applies object-shadows over the substitutions entering an object, and that
;; object's definitions.
(define-metafunction Graceless
  all-object-shadows : s ... d ... -> (s ...)
  [(all-object-shadows s ... d ...)
   ,(apply append (term ((object-shadows s a ...) ...)))
   (where (a ...) ((identify (declaration d)) ...))])

;; Resets references to a surrounding object to be the receiver in a method when
;; that method is being updated into that object.
(define-metafunction Graceless
  reset-receiver : n s -> s
  ;; Replace a value substitution for self with a reset.
  [(reset-receiver n [v / (self n)]) [(self 0) / (self n)]]
  ;; Reset qualifying substitutions to 0.
  [(reset-receiver n [(self n) / a]) [(self 0) / a]]
  ;; Increment self references in any other substitution.  This shouldn't be
  ;; necessary normally because all of the substitutions will be for (self n)
  ;; anyway, but this accounts for the possibility in other applications.
  [(reset-receiver n [any_1 / any_2]) [(inc-self any_1) / (inc-self any_2)]])

;; Changes any self reference identified by the input to 0, and shuffles any
;; intervening self references up.
(define-metafunction Graceless
  reset-self : n s ... -> (s ...)
  [(reset-self n s ...) (s_o ... s_s ...)
   ;; Increment every self reference before performing the other substitutions.
   (where (s_s ...) ,(build-list (add1 (term n))
                                 (λ (i) (term [(self ,i) / (self ,i)]))))
   ;; The self identifier is incremented here for the same reason.
   (where (s_o ...) ,(map (λ (s) (term (reset-receiver n ,s)))
                          (term (s ...))))])


;; We can now proceed to the actual definition of term substitution.  This
;; proceeds through the mutual declaration of substitutions on terms,
;; declarations, and blocks.

;; Performs substitution through an expression e.
(define-metafunction Graceless
  subst : s ... t -> t

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

  ;; Substitution into a method update is the most complicated part.  Self
  ;; references use De Bruijn indices to distinguish each distinct binding, but
  ;; the assumption is that (self 0) is the receiver of a request when directly
  ;; inside of a method: hence the substitution [y / (self 0)] where y is the
  ;; receiver.  The trouble is that, because a method update can appear at any
  ;; depth inside of an object constructor, the actual reference to the receiver
  ;; could be any self index, not just (self 0).  In order to ensure we still
  ;; have unique identifiers, substitution into a updating method body takes
  ;; into account which object is the receiver of the update, and does not
  ;; continue such a substitution into the method definition.  Once the receiver
  ;; is a store reference, every incoming substitution on a self reference also
  ;; decrements the reference one larger than it, which will be the self
  ;; reference that was skipped over.  Once all of the surrounding objects are
  ;; substituted, the result will be the reference to the receiver of the update
  ;; is (self 0).

  ;; When approaching a substitution into a method update, there are three
  ;; possibilities, each enumerated below.

  ;; The receiver of the update is still a self reference, and the incoming
  ;; substitution is for the receiver, replacing it with a reference.  The
  ;; qualifying substitutions proceed into the definition, but the value
  ;; substitution does not.
  [(subst s_i ... [v / w] s_j ... (w ← d)) (v ← (subst-decl s_i ... s_j ... d))]

  ;; The receiver of the update is a store reference, and there is a
  ;; substitution for a self reference.  The self reference one larger will also
  ;; be decremented.
  [(subst s ... (y ← d))
   (y ← (subst-decl [(self n) / (self ,(add1 (term n)))] s ... d))
   (where (_ ... [v / (self n)] _ ...) (s ...))]

  ;; Finally, there is no incoming substitution for the receiver to replace it
  ;; with a reference.  In this case things are substituted as usual.
  [(subst s ... (w ← d)) (w ← (subst-decl s ... d))]

  ;; Continue the substitution into a raise.
  [(subst s ... (↥ t)) (↥ (subst s ... t))]

  ;; Continue the substitution into a catch, and its block.
  [(subst s ... (t ⤒ b)) ((subst s ... t) ⤒ (subst-block s ... b))]

  ;; Continue the substitution into a match, and its blocks.
  [(subst s ... (t ∋ a b_1 b_2))
   ((subst s ... t) ∋ a (subst-block s ... b_1) (subst-block s ... b_2))]

  ;; Substitute out self for the given reference, so long as there is no later
  ;; substitution in the list.
  [(subst _ ... [x / (self n)] s ... (self n)) x
   (side-condition (term (not-in-subst (self n) s ...)))]

  ;; Continue the substitution into a sequence.
  [(subst s ... [t ...]) [(subst s ... t) ...]]

  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... t) t])

;; Continues subst through methods into method bodies, removing names which
;; are shadowed by an appearance in the parameter list.
(define-metafunction Graceless
  subst-decl : s ... d -> d
  [(subst-decl s ... (method (m ([z : T_i] ...) → T) t))
   (method (m ([z : T_i] ...) → T) (subst s_d ... t))
   (where (s_d ...) ,(apply append (term ((remove-shadows s [z 0] ...) ...))))])

;; Continues subst through blocks into block bodies, removing names which are
;; shadowed by the block parameter.
(define-metafunction Graceless
  subst-block : s ... b -> b
  [(subst-block s ... {z → t}) {z → (subst s_d ... t)}
   (where ((s_d ...)) ((remove-shadows s [z 0]) ...))])

;; Determines whether the given thing is being substituted out by the
;; substitutions s.
(define-metafunction Graceless
  not-in-subst : any s ... -> boolean
  ;; This matching syntax captures any name in any standard substitution.
  [(not-in-subst any _ ... [_ ... / any] _ ...) #f]
  ;; In any other case, it is not in the list.
  [(not-in-subst _ _ ...) #t])


;; The type well-formedness judgment encodes the explicit requirement that
;; declaration identifiers in any structural type must be unique.

;; The judgment is overloaded on the three components of the hierarchy.
(define-judgment-form Graceless
  #:mode (well-formed I I)
  ;; Redex doesn't support coinduction, so we need an extra argument to act as
  ;; an assumption set.
  #:contract (well-formed (∞T ...) any)

  ;; When a promise is encountered, prove that the forced type is well-formed
  ;; under the assumption that the promise is.
  [(side-condition ,(promise? (term ∞T)))
   (side-condition ,(not (member (term ∞T) (term (∞T_i ...)))))
   (well-formed (∞T ∞T_i ...) ,(force (term ∞T)))
   ------------------------------------------------------------ Asm
   (well-formed (∞T_i ...) ∞T)]

  ;; A promise is well-formed under the assumption that it is.
  [--------------------------------- Asd
   (well-formed (_ ... ∞T _ ...) ∞T)]

  ;; A union is well-formed if its structural types are well-formed.
  [(well-formed any S) ...
   --------------------------- Uni
   (well-formed any (⋃ S ...))]

  ;; A structural type is well-formed if its declaration identifiers are unique,
  ;; and its declarations are well-formed.
  [(side-condition (unique (identify D) ...))
   (well-formed any D) ...
   ------------------------------ Str
   (well-formed any (type D ...))]

  ;; A declaration is well-formed if its annotations are well-formed.
  [(well-formed any ∞T_i) ...
   (well-formed any ∞T)
   --------------------------------------------- Sig
   (well-formed any (m ([x_i : ∞T_i] ...) → ∞T))])


;; Binary operators for union and intersection appear on Grace types.  Here we
;; have implemented unions as a list of structural types, and intersection as
;; the combination of declarations in a structural type.  It would still be
;; helpful to define the binary operators here as well.  Union is easy to
;; implement, because we just perform a set union between the list of structural
;; types.  Intersection needs to be more careful, combining declarations with
;; the same identifier to preserve the well-formedness of the resulting
;; structural type (which requires that method identifiers are unique in a
;; structural type).

;; Combines two types into a union by merging the variants and removing any
;; duplicates.
(define-metafunction Graceless
  ∪ : T T -> T
  [(∪ (⋃ S_i ...) (⋃ S_j ...)) (⋃ S_k ...)
   (where (S_k ...) ,(remove-duplicates (term (S_i ... S_j ...))))])

;; Union between potentially delayed types.  If neither type is delayed, this is
;; equivalent to union, but otherwise the result is itself delayed.
(define-metafunction Graceless
  ∞∪ : ∞T ∞T -> ∞T
  [(∞∪ T_1 T_2) (∪ T_1 T_2)]
  [(∞∪ ∞T_1 ∞T_2) ,(delay (term (⋃ (ω ∞T_1) (ω ∞T_1))))])

;; Intersection combines two types into their meet on the subtyping lattice.
(define-metafunction Graceless
  ∩ : T T -> T
  [(∩ (⋃ S_i ...) (⋃)) (⋃)]
  [(∩ (⋃ S_i ...) (⋃ S S_j ...)) (⋃ S_k ... S_l ...)
   (where (S_k ...) ((∩-struct S_i S) ...))
   (where (⋃ S_l ...) (∩ (⋃ S_i ...) (⋃ S_j ...)))])

;; Intersection between structural types.
(define-metafunction Graceless
  ∩-struct : S S -> S
  [(∩-struct (type D_i ...) (type D_j ...)) (type D_k ...)
   (where (D_k ...) (∩-seq (D_i ...) (D_j ...)))])

;; Intersection for sequences of declarations.
(define-metafunction Graceless
  ∩-seq : (D ...) (D ...) -> (D ...)
  [(∩-seq (D_1 D_i ...) (D_j ... D_2 D_k ...)) ((∩-decl D_1 D_2) D_l ...)
   (side-condition (equal? (term (identify D_1)) (term (identify D_2))))
   (where (D_l ...) (∩-seq (D_i ...) (D_j ... D_k ...)))]
  [(∩-seq (D_1 D_i ...) (D_j ...))             (D_1 D_k ...)
   (where (D_k ...) (∩-seq (D_i ...) (D_j ...)))]
  [(∩-seq () (D_j ...))                        (D_j ...)])

;; Intersection between declarations.
(define-metafunction Graceless
  ∩-decl : D D -> D
  [(∩-decl (m ([x_1 : ∞T_i1] ..._i) → ∞T_1) (m ([x_2 : ∞T_i2] ..._i) → ∞T_2))
   (m ([x_1 : (∞∪ ∞T_i1 ∞T_i2)] ...) → (∞∩ ∞T_1 ∞T_2))])

;; Intersection between potentially delayed types.  If neither type is delayed,
;; this is equivalent to intersection, but otherwise the result is itself
;; delayed.
(define-metafunction Graceless
  ∞∩ : ∞T ∞T -> ∞T
  [(∞∩ T_1 T_2) (∩ T_1 T_2)]
  [(∞∩ ∞T_1 ∞T_2) ,(delay (term (∩ (ω ∞T_1) (ω ∞T_1))))])

;; Unions an arbitrary number of types together.
(define-metafunction Graceless
  union : T ... -> T
  [(union) ⊥]
  [(union T T_i ...) (∪ T (union T_i ...))])

;; Intersects an arbitrary number of types together.
(define-metafunction Graceless
  intersect : T ... -> T
  [(intersect) ⊤]
  [(intersect T T_i ...) (∩ T (intersect T_i ...))])


;; Subtracting an identifier from a type removes all structural types from the
;; union that contain a declaration with that identifier.  This is useful for
;; typing the else-branch of a match construct, since we know that there is no
;; such definition with the matched identifier in that branch.

;; Subtracts an identifier from a union.
(define-metafunction Graceless
  - : T a -> T
  [(- (⋃ S_i ...) a) (⋃ S_j ...)
   (where (S_j ...) ,(filter (compose not empty?)
                             (term ((-struct S_i a) ...))))])

;; Subtracts an identifier from a structural type.  The resulting list is either
;; a singleton containing the input, or empty.
(define-metafunction Graceless
  -struct : S a -> (S ...)
  [(-struct (type D_i ... D D_j ...) a) ()
   (where a (identify D))]
  [(-struct (type D ...) a) ((type D ...))])


;; Types are related by subtyping, a coinductive relation that may descend
;; infinitely over an infinite type.

;; As with well-formedness, the subtyping relation is overloaded on all parts of
;; the typing hierarchy.
(define-judgment-form Graceless
  #:mode (<: I I I)
  ;; As with the well-formedness judgment, lack of support for coinduction means
  ;; we need an extra argument to behave as the assumption set.  Here the
  ;; assumption set is a pair of types in the subtyping relation.
  #:contract (<: ([∞T ∞T] ...) any any)

  ;; If either type is a promise, prove that the forced form of both types are
  ;; subtypes under the assumption that the two original types are subtypes.
  [(side-condition ,(or (promise? (term ∞T_1))
                        (promise? (term ∞T_2))))
   (side-condition ,(not (member (term [∞T_1 ∞T_2]) (term (any ...)))))
   (<: ([∞T_1 ∞T_2] any ...) (ω ∞T_1) (ω ∞T_2))
   -------------------------------------------------------------------- Ass
   (<: (any ...) ∞T_1 ∞T_2)]

  ;; Two promises are subtypes under the assumption that they are.
  [---------------------------------------- Asd
   (<: (_ ... [∞T_1 ∞T_2] _ ...) ∞T_1 ∞T_2)]

  ;; Without a forall mechanism, we need to split the union rule into a forall
  ;; and an exists rule.  This matches every structural type in the sub-type
  ;; against all of the structural types in the super-type.
  [(<: any S_i (S_j ...)) ...
   -------------------------------- U/∀
   (<: any (⋃ S_i ...) (⋃ S_j ...))]

  ;; Then this rule requires a single structural type in the list of the
  ;; super-types to be a super-type of the structural sub-type.
  [(<: any S_i S_j)
   ------------------------------ U/∃
   (<: any S_i (_ ... S_j _ ...))]

  ;; As with the union forms, we need to split this rule into forall and
  ;; exists.  The matching direction is reversed for structural types, so a list
  ;; of declarations is matched against a single declaration.
  [(<: any (D_i ...) D_j) ...
   -------------------------------------- S/∀
   (<: any (type D_i ...) (type D_j ...))]

  ;; Again, a single declaration selected from the list must match against the
  ;; other declaration.
  [(<: any D_i D_j)
   ------------------------------ S/∃
   (<: any (_ ... D_i _ ...) D_j)]

  ;; Declarations with the same identifier are compatible under contravariant
  ;; parameter subtyping and covariant return subtyping.
  [(<: any ∞T_i2 ∞T_i1) ...
   (<: any ∞T_1 ∞T_2)
   ------------------------------------- Sig
   (<: any
       (m ([x_1 : ∞T_i1] ..._i) → ∞T_1)
       (m ([x_2 : ∞T_i2] ..._i) → ∞T_2))])


;; We also need a number of auxiliary functions for examining and manipulating
;; stores.

;; Stores a new runtime object O in the store σ.  The resulting location is the
;; same as calculated by fresh-location on the same store, before the object is
;; added.
(define-metafunction Graceless
  store : σ O -> σ
  [(store σ O) ,(append (term σ) (term (O)))])

;; Fetches a fresh location for the store.
(define-metafunction Graceless
  fresh-location : σ -> y
  [(fresh-location σ) ,(length (term σ))])

;; Searches for the object at the location ℓ in the store σ.
(define-metafunction Graceless
  lookup : σ y -> O
  [(lookup σ y) ,(list-ref (term σ) (term y))])

;; Replaces the method with the same declaration as d in σ(y) with d itself.
(define-metafunction Graceless
  update : σ y d -> σ
  [(update σ y d) ,(list-update (term σ)
                                (term y)
                                (λ (O) (term (update-in ,O d))))])

;; Replaces the method with the same declaration as d in the run-time object O
;; with d itself.
(define-metafunction Graceless
  update-in : O d -> O
  [(update-in (d_l ... (method D t_1) d_r ...) (method D t_2))
   (d_l ... (method D t_2) d_r ...)])


;; We also need a few auxiliary functions for definitions and declarations.

;; Fetches the declaration of a definition.
(define-metafunction Graceless
  declaration : d -> D
  [(declaration (method D t)) D])

;; Identifies a method based on its signature.
(define-metafunction Graceless
  identify : any -> a
  [(identify d) (identify (declaration d))]
  [(identify (m ([x : _] ...) → _)) [m ,(length (term (x ...)))]])


;; The following judgments often require that a sequence contains unique
;; elements, so we define that as an auxiliary function as well.

;; Ensures that the given names are unique.
(define-metafunction Graceless
  unique : a ... -> boolean
  [(unique _ ... a _ ... a _ ...) #f]
  [(unique _ ...) #t])


;; Small-step dynamic semantics of Graceless, operating on an expression e
;; paired with a store σ.
(define -->G
  (reduction-relation
   Graceless
   #:domain p

   ;; Move to the next expression in a sequence when the first expression has
   ;; completed evaluating.
   (--> [σ (in-hole E [v t])]
        [σ (in-hole E t)]
        Seq)

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
        (where (a ...) ((identify d) ...))
        ;; An object's method names must be unique.
        (side-condition (term (unique a ...)))
        Obj)

   ;; Eliminate a rescue if the body does not result in a raise.
   (--> [σ (in-hole E (v ⤒ b))]
        ;; A safe rescue reduces to its body.
        [σ (in-hole E v)]
        Sfe)

   ;; Apply an update if the declaration matches exactly the one in the object.
   (--> [σ (in-hole E (y ← d))]
        ;; The premise on the rule in the paper is implicit in the update
        ;; operation here.
        [(update σ y d) (in-hole E y)]
        Upd)

   ;; Substitute the parameters in the body of requested method.
   (--> [σ (in-hole E (y m v ..._i))]
        ;; Substitute the variable names for the arguments and the receiver for
        ;; self.
        [σ (in-hole E (subst [y / (self 0)] [v / x] ... t))]
        ;; Fetch the method which matches the request.
        (where (_ ... (method (m ([x : _] ..._i) → _) t) _ ...) (lookup σ y))
        Req)

   ;; Rescue a raise if this is the closest rescue surrounding the raise.
   (--> [σ (in-hole E ((in-hole F (↥ v)) ⤒ {z → t}))]
        ;; The raised value is bound to the parameter in the block.
        [σ (in-hole E (subst [v / z] t))]
        Rsc)

   ;; Take the left branch of a match if the identifier appears in the object.
   (--> [σ (in-hole E (y ∋ a {z → t} b))]
        ;; The matched object is bound to the parameter in the body.
        [σ (in-hole E (subst [y / z] t))]
        ;; Search for the identifier and confirm that it is there.
        (side-condition (member (term a)
                                (map (λ (d) (term (identify ,d)))
                                     (term (lookup σ y)))))
        Fst)

   ;; Take the right branch of a match if the identifier does not appear in the
   ;; object.
   (--> [σ (in-hole E (y ∋ a b {z → t}))]
        ;; The matched object is bound to the parameter in the body.
        [σ (in-hole E (subst [y / z] t))]
        ;; Search for the identifier and confirm that it is not there.
        (side-condition (not (member (term a)
                                     (map (λ (d) (term (identify ,d)))
                                          (term (lookup σ y))))))
        Snd)

   ;; The base arrow fails an entire program if it encounters an unrescued
   ;; raise.
   (--> [σ (in-hole G (↥ v))]
        [σ (↥ v)]
        Raise)))


;; We also define a judgment for selecting a declaration from the typing
;; environment, and a judgment for direct variable lookup in the environment.

;; Finds the nearest declaration identified by 'a' in a typing environment.
(define-judgment-form Graceless
  #:mode (lookup-sig I I O)
  #:contract (lookup-sig Γ a D)

  [(side-condition ,(equal? (term a) (term (identify D))))
   ---------------------------------------------------------- Hre
   (lookup-sig (_ ... [self : (⋃ (type _ ... D _ ...))]) a D)]

  [(not-in γ a)
   (lookup-sig (γ_t ...) a D)
   ---------------------------- Thr
   (lookup-sig (γ_t ... γ) a D)])

;; Variable lookup in a typing environment.  This is necessary because self
;; references are stored without an index, and we need to recover the index by
;; manually stepping through the environment.
(define-judgment-form Graceless
  #:mode (lookup-var I I O)
  #:contract (lookup-var Γ x T)

  [(side-condition ,(not (ormap (λ (γ) (equal? (term x) (first γ)))
                                (term (γ ...)))))
   --------------------------------------------------------------- Hre
   (lookup-var (_ ... [x : T] γ ...) x T)]

  [(side-condition ,(= (term n)
                       (count (λ (γ) (equal? (term self) (first γ)))
                              (term (γ ...)))))
   ---------------------------------------------------------------- Thr
   (lookup-var (_ ... [self : T] γ ...) (self n) T)])

;; A relation that checks if a definition identified by 'a' appears in a self
;; type in the given binding.
(define-relation Graceless
  not-in ⊆ γ × a

  [(not-in [self : (⋃ (type D ...))] a)
   (side-condition (not (member (term a) (term ((identify D) ...)))))]

  ;; 'self' is a keyword, so is not matched by x.
  [(not-in [x : T] a)])


;; Some auxiliary functions.

;; Fetches the most accurate type annotations on a signature in the given type.
;; Returns a singleton list if successful, or an empty list if there is no such
;; declaration in the type.
(define-metafunction Graceless
  sig-types : T a -> ([(T ...) T] ...)
  [(sig-types (⋃ (type D ...) ...) a)
   (union-sigs ((fetch-sig-types D ... a) ...))])

;; Fetches the type annotations on a signature from a list of signatures.
(define-metafunction Graceless
  fetch-sig-types : D ... a -> ([(T ...) T] ...)
  [(fetch-sig-types _ ... (m ([_ : T_i] ...) → T) _ ... [m n]) ([(T_i ...) T])
   (side-condition (= (term n) (length (term (T_i ...)))))]
  [(fetch-sig-types _ ... a) ()])

;; Unions the type annotations on signatures into a single signature.
(define-metafunction Graceless
  union-sigs : (([(T ...) T] ...) ...) -> ([(T ...) T] ...)
  [(union-sigs (() any ...)) (union-sigs (any ...))]
  [(union-sigs (([(T_i ...) T_1]) any ...)) [((∩ T_i T_j) ...) (∪ T_1 T_2)]
   (where ([(T_j ...) T_2]) (union-sigs (any ...)))]
  [(union-sigs (any () ...)) any]
  [(union-sigs _) ()])

;; The ground declaration of an identifier.
(define-metafunction Graceless
  ground : a -> T
  [(ground [m n]) (m ,(make-list (term n) (term [x : ⊥])) → ⊤)])


;; Now we can define term typing.  Unlike the text, we define two separate,
;; mutually recursive judgments to deal with subsumption: one is a
;; syntax-directed type assignment judgment where the type is an output, and the
;; other is a type *checker*, extending the assignment with subsumption and
;; accepting the type as an input.  The result is a slightly different form of
;; typing judgment than in the text, since subsumption must be applied exactly
;; once, but reflexivity and transitivity of subtyping means that it is simple
;; to recover slightly different derivations for the same proofs.

;; Type checking with subsumption.
(define-judgment-form Graceless
  #:mode (has-type I I I)
  #:contract (has-type Γ t T)

  [(assign-type Γ t T_1)
   (<: () T_1 T_2)
   (well-formed () T_2)
   --------------------- Sub
   (has-type Γ t T_2)])

;; The syntax-directed type assignment.
(define-judgment-form Graceless
  #:mode (assign-type I I O)
  #:contract (assign-type Γ t T)

  ;; Variable typing using the lookup-var judgment defined above.
  [(lookup-var Γ (unwrap tx) T)
   ---------------------------- Var
   (assign-type Γ tx T)]

  ;; A raise never returns, so it has type ⊥, so long as the value being
  ;; raised is also well-typed.
  [(assign-type Γ t T)
   ----------------------- Rse
   (assign-type Γ (↥ t) ⊥)]

  [(assign-type Γ t_1 T_1)
   (assign-type Γ t_2 T_2)
   ----------------------------- Seq
   (assign-type Γ [t_1 t_2] T_2)]

  [(where (D ...) ((declaration d) ...))
   (where Γ (γ ... [self : (⋃ (type D ...))]))
   (assign-decl Γ d D) ...
   (assign-type Γ t T)
   (side-condition (unique (identify D) ...))
   ------------------------------------------------------- Obj
   (assign-type (γ ...) (object d ... t) (⋃ (type D ...)))]

  [(lookup-sig Γ [m ,(length (term (t_i ...)))] (m ([x : T_i] ...) → T))
   (has-type Γ t_i T_i) ...
   --------------------------------------------------------------------- R/U
   (assign-type Γ (m t_i ...) T)]

  [(assign-type Γ t T_1)
   (where ([(T_i ..._i) T_2])
          (sig-types T_1 [m ,(length (term (t_i ...)))]))
   (has-type Γ t_i T_i) ...
   ------------------------------------------------------ R/Q
   (assign-type Γ (t m t_i ..._i) T_2)]

  [(assign-type (γ ...) t_1 T_1)
   (assign-type (γ ... [z : ⊤]) t_2 T_2)
   --------------------------------------------------- Rsc
   (assign-type (γ ...) (t_1 ⤒ {z → t_2}) (∪ T_1 T_2))]

  [(lookup-var Γ w T)
   (assign-decl Γ d D)
   (where (⋃ (type _ ... D _ ...)) T)
   ---------------------------------- Upd
   (assign-type Γ (w ← d) T)]

  [(assign-type (γ ...) t_1 T_1)
   (assign-type (γ ... [z_1 : (∩ T_1 (ground a))]) t_2 T_2)
   (assign-type (γ ... [z_2 : (- T_1 a)]) t_3 T_3)
   ------------------------------------------------------------------- Mch
   (assign-type (γ ...) (t_1 ∋ a {z_1 → t_2} {z_2 → t_3}) (∪ T_2 T_3))])

;; Checks that a definition satisfies a declaration.
(define-judgment-form Graceless
  #:mode (assign-decl I I O)
  #:contract (assign-decl Γ d D)

  [(where Γ (γ ... [x : T_i] ...))
   (well-formed () T_i) ...
   (well-formed () T)
   (has-type Γ t T)
   -------------------------------------------- Sig
   (assign-decl (γ ...)
             (method (m ([x : T_i] ...) → T) t)
             (m ([x : T_i] ...) → T))])

;; Checks that an object contains the given declarations.  This is split out
;; purely for the purpose of simplifying the store typing to a point that Redex
;; can understand the ellipsis patterns.
(define-judgment-form Graceless
  #:mode (assign-decls I I I)
  #:contract (assign-decls Γ (d ...) (D ...))

  [(assign-decl (γ ... [self : (⋃ (type D ...))]) d D) ...
   (side-condition (unique (identify D) ...))
   ------------------------------------------------------- Dcl
   (assign-decls (γ ...) (d ...) (D ...))])

;; Assigns a store an initial typing environment.
(define-judgment-form Graceless
  #:mode (assign-env I O)
  #:contract (assign-env σ Γ)

  [(where (y ...) ,(range (length (term ((d ...) ...)))))
   (where ((D ...) ...) (((declaration d) ...) ...))
   (where Γ ([y : (⋃ (type D ...))] ...))
   (assign-decls Γ (d ...) (D ...)) ...
   ------------------------------------------------------ Sto
   (assign-env ((d ...) ...) Γ)])


;; Wraps a term t into an initial program with an empty store.
(define (program t) (term [() ,t]))

;; Progresses the program p by one step with the reduction relation -->G.
(define (step-->G p) (apply-reduction-relation -->G p))

;; Evaluates an expression starting with an empty store.
(define-metafunction Graceless
  eval : t -> t
  [(eval t) ,(second (term (run [() t])))])

;; Applies the reduction relation -->G until the result is a value or the
;; program gets stuck or has an error.
(define-metafunction Graceless
  run : p -> [σ t]
  [(run [σ y]) [σ (object d ... y)]
   (where (d ...) (lookup σ y))]
  [(run [σ (↥ v)]) [σ (↥ v)]]
  [(run p) (run p_n)
   (where (p_n) ,(step-->G (term p)))]
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
