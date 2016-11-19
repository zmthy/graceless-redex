#lang racket

(require redex
         "graceless.rkt")

(define (typed? p)
  (let ([σ (first p)]
        [t (second p)])
    (match (judgment-holds (store-typed ,σ Σ) Σ)
      [(list Σ)
       (judgment-holds (typed ,Σ () ,t T))]
      [else #f])))

(define value? (redex-match Graceless v))
(define error? (redex-match Graceless uninitialised))

(define (reduces? p)
  (not (null? (apply-reduction-relation -->G (term ,p)))))

(define (progress? p)
  (if (typed? p)
      (or (value? (second p))
          (error? (second p))
          (reduces? p))
      #t))

(let ([c (make-coverage -->G)])
  (parameterize ([relation-coverage (list c)])
    (check-reduction-relation -->G (λ (p) (progress? p))))
  (covered-cases c))
