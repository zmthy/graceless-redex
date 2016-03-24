#lang racket

(require redex
         "common.rkt")

(provide (except-out (all-defined-out)
                     eval
                     run)
         (all-from-out "common.rkt"))

;; Small-step dynamic semantics of Graceless extended with concatenating
;; inheritance.
(define -->GC
  (extend-reduction-relation
   -->GPO
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
                              (self x_c <- v_c) ...
                              (subst-stmt s ... S) ...))]
        ;; Only execute this rule if there are inherits clauses to process.
        (side-condition (pair? (term ((m_e ...) ...))))
        ;; Collect the names of the definitions in the inheriting object.
        (where (m ...) (names M ... S ...))
        ;; Lookup the super objects.
        (where ((object [x v] ... M_p ...) ...) ((lookup σ ℓ) ...))
        ;; Concatenate the fields into a single list.
        (where ([x_c v_c] ...) (concat ([x v] ...) ...))
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
        inherits/concatenation)))

;; Progress the program p by one step with the reduction relation -->GC.
(define (step-->GC p) (apply-reduction-relation -->GC p))

;; Evaluate an expression starting with an empty store.
(define-metafunction GO
  eval : e -> e
  [(eval e) ,(second (term (run [() e])))])

;; Apply the reduction relation -->GC until the result is a value or the program
;; gets stuck or has an error.
(define-metafunction GO
  run : p -> p
  [(run [σ uninitialised]) [σ uninitialised]]
  [(run [σ (ref ℓ)]) [σ (object M ...)]
   (where [M ...] (lookup σ ℓ))]
  [(run p) (run p_p)
   (where (p_p) ,(step-->GC (term p)))]
  [(run p) p])

;; Run the term t as an initial program with the reduction relation -->GC,
;; returning the resulting object, stuck program, or error.
(define (eval-->GC t) (term (eval ,t)))

;; Run the term t as an initial program with the reduction relation -->GC,
;; returning the resulting object, stuck program, or error, and the store.
(define (run-->GC t) (term (run [() ,t])))

;; Run the traces function on the given term as an initial program with the
;; reduction relation -->GC.
(define (traces-->GC t) (traces -->GC (program t)))
