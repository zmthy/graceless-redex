#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with uniform identity
;; method transformation multiple inheritance.
(define -->GU
  (extend-reduction-relation
   -->GPF
   GI
   #:domain p
   ;; Concatenate the body of the inherited objects into the inheriting object's
   ;; body, removing overrides.
   (--> [σ (in-hole E (object (inherits (object M ... S ...)
                                        alias ... (m_a as m_ap) ...
                                        exclude ... m_e ...) ...
                              s_d ... M_d ... S_d ...))]
        ;; The resulting object includes the super methods, the substituted
        ;; methods, and field accessors.
        [σ (in-hole E (object M_up ...
                              (subst-method s ... M_d) ...
                              e_p ...
                              (subst-stmt s ... S_d) ...))]
        ;; Only execute this rule if there are inherits clauses to process.
        (side-condition (pair? (term ((m_e ...) ...))))
        ;; Collect the names of the definitions in the inherited objects.
        (where ((m ...) ...) ((names M ... S ...) ...))
        ;; An object's method names must be unique.
        (side-condition (term (all-unique (m ...) ...)))
        ;; Qualify local requests to this object in the super-methods.
        (where ((M_p ...) ...) ((subst-methods [(self 0) / m ...] (M ...)) ...))
        ;; Flatten the statements, to generate an appropriate number of fresh
        ;; field names.
        (where (S_c ...) (concat (S ...) ...))
        ;; Build fresh field names for each of the statements (this builds
        ;; unnecessary fresh names for expressions as well).
        (fresh ((y ...) (S_c ...)))
        (where (([S_p y] ...) ...) (zip-stmts y ... (S ...) ...))
        ;; Collect the field accessor methods and the resulting object body.
        (where ((M_f ... e ...) ...) ((body [S_p y] ...) ...))
        ;; Qualify local requests to this object in the super-methods and
        ;; flatten down to a single list of expressions.
        (where (e_p ...) (concat (substs [(self 0) / m ...] (e ...)) ...))
        ;; Run the aliases on the methods from each inherited object.
        (where ((M_a ...) ...)
               ((aliases (m_a as m_ap) ... M_p ... M_f ...) ...))
        ;; Run the excludes on the result of the aliases.
        (where ((M_e ...) ...) ((excludes m_e ... M_a ...) ...))
        ;; Finally escape this double ellipses hell by concatenating the result
        ;; of all the excludes.
        (where (M_c ...) (concat (M_e ...) ...))
        ;; Resolve conflicts between inherited methods.
        (where (M_u ...) (join M_c ...))
        ;; Collect the names of the definitions in the inheriting object.
        (where (m_d ...) (names M_d ... S_d ...))
        ;; Remove from the inherited methods any method which is overridden by a
        ;; definition in the inheriting object.
        (where (M_up ...) (override M_u ... m_d ...))
        ;; Remove the shadowed substitutions before applying them to the body.
        (where (s ...) (all-object-shadows s_d ... (M_up ...)))
        inherits/multiple)))

;; Progress the program p by one step with the reduction relation -->GU.
(define (step-->GU p) (apply-reduction-relation -->GU p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GU until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GU (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error.
(define (eval-->GU t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GU,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GU t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GU.
(define (traces-->GU t) (traces -->GU (program t)))
