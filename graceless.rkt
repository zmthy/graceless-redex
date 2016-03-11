#lang racket

(require redex)

(provide (except-out (all-defined-out)
                     eval
                     run))

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
  (s [v x]
     [ℓ self]
     [ℓ m ...])
  (σ ([M ...] ...))
  (p [e σ]))

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
  [(remove-shadows [ℓ] _ ...) ()]
  ;; Otherwise, retain the remaining substitution.
  [(remove-shadows s _ ...) (s)])

;; Remove any names from the substitution s which are shadowed by a definition
;; in the object o.  If the substitution still has names remaining, it is
;; returned as the sole element of the list, otherwise the list is empty.  Any
;; substitution for self is guaranteed to be removed, as the new object context
;; implicitly shadows it.
(define-metafunction G
  remove-object-shadows : s o -> (s ...)
  ;; Self is always removed.
  [(remove-object-shadows [_ self] _) ()]
  ;; Otherwise collect the method names of the object, and remove-shadows.
  [(remove-object-shadows s o) (remove-shadows s m ...)
   (where (m ...) (object-names o))])

;; Determine whether the given thing appears in the substitutions s.
(define-metafunction G
  not-in-subst : any s ... -> boolean
  ;; This matching syntax captures any match in any kind of substitution.
  [(not-in-subst any _ ... [_ ... any _ ...] _ ...) #f]
  ;; In any other case, it is not in the list.
  [(not-in-subst _ _ ...) #t])

;; Perform substitutions through an expression e.
(define-metafunction G
  subst : s ... e -> e
  ;; Continue the substitution into an object body, removing substitutions
  ;; shadowed by the object.
  [(subst s ... (name o (object M ... F ...)))
   (object (subst-method s_p ... M) ... (subst-field s_p ... F) ...)
   (where (s_p ...) ,(append-map (λ (s) (term (remove-object-shadows ,s o)))
                                 (term (s ...))))]
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
  ;; All other syntax is a terminal, so just return that.
  [(subst _ ... e) e])

;; Continue subst through methods into method bodies, removing names which
;; appear in the parameter list.
(define-metafunction G
  subst-method : s ... M -> M
  [(subst-method s ... (method m (x ...) e))
   (method m (x ...) (subst s_p ... e))
   (where (s_p ...) ,(append-map (λ (s) (term (remove-shadows ,s x ...)))
                                 (term (s ...))))])

;; Continue substitution through fields into their assignments.  This ignores
;; their names, as that will already have been taken care of by the rule for
;; object in the subst function.
(define-metafunction G
  subst-field : s ... F -> F
  [(subst-field s ... (def x = e)) (def x = (subst s ... e))]
  [(subst-field _ ... (var x)) (var x)]
  [(subst-field s ... (var x := e)) (var x := (subst s ... e))])

;; Store a new object with the methods M.  The resulting location is the same as
;; calculated by fresh-location on the same store, before the object is added.
(define-metafunction G
  store : σ [M ...] -> σ
  [(store σ [M ...]) ,(append (term σ) (term ([M ...])))])

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
   [M_l ... (method x () v) M_r ...]]
  [(update-method [M ...] _ _) [M ...]])

;; Collect all of the method names in the object o, including those generated by
;; getter and setter methods of fields.
(define-metafunction G
  object-names : o -> (m ...)
  [(object-names (object (method m _ _) ... F ...))
   ,(append (term (m ...)) (term (field-names F ...)))])

;; Convert the field F into getter and (maybe) setter methods.
(define-metafunction G
  field-to-methods : F -> (M ...)
  [(field-to-methods (def x = _)) ((method x () uninitialised))]
  [(field-to-methods (var x _ ...))
   ((method x () uninitialised)
    (method (x :=) (x) (assign self x (request x) done)))])

;; Collect the corresponding getter and (maybe) setter methods of the fields F.
(define-metafunction G
  field-methods : F ... -> (M ...)
  [(field-methods F ...)
   ,(append-map (λ (F) (term (field-to-methods ,F))) (term (F ...)))])

;; Convert the field F into getter and (maybe) setter method names.
(define-metafunction G
  field-to-names : F -> (m ...)
  [(field-to-names (def x = _)) (x)]
  [(field-to-names (var x _ ...)) (x (x :=))])

;; Collect the corresponding getter and (maybe) setter method names of the
;; fields F.
(define-metafunction G
  field-names : F ... -> (m ...)
  [(field-names F ...)
   ,(append-map (λ (F) (term (field-to-names ,F))) (term (F ...)))])

;; Convert a field F to an assignment in the object at location ℓ, which then
;; executes the expression e.
(define-metafunction G
  field-to-assign : ℓ F e -> e
  [(field-to-assign ℓ (def x = e_a) e) (assign (ref ℓ) x e_a e)]
  [(field-to-assign ℓ (var x) e) e]
  [(field-to-assign ℓ (var x := e_a) e) (assign (ref ℓ) x e_a e)])

;; Convert a list of fields F to a sequence of assignments in the object at
;; location ℓ, finally executing the final expression e.
(define-metafunction G
  field-assigns : ℓ F ... e -> e
  [(field-assigns ℓ F ... e)
   ,(foldr (λ (F e) (term (field-to-assign ℓ ,F ,e))) (term e) (term (F ...)))])

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
   ;; Allocate the object o, converting fields into assignments with local
   ;; requests substituted to the new object, and ultimately return the
   ;; resulting reference.
   (--> [(in-hole E (name o (object M ... F ...))) σ]
        ;; This substitution is into the body of the object.  The use of self
        ;; and local requests in the method bodies will be handled when they are
        ;; requested.
        [(in-hole E (subst [ℓ self] [ℓ m ...] (field-assigns ℓ F ... (ref ℓ))))
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
        object)
   ;; Substitute for unqualified requests to the parameters, and return the body
   ;; of the method.
   (--> [(in-hole E (request (ref ℓ) m v ..._a)) σ]
        ;; It's important that the local references come first in the
        ;; substitution, as the parameters shadow local methods in the body.
        [(in-hole E (subst [v x] ... [ℓ self] [ℓ m_o ...] e)) σ]
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
