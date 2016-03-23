#lang racket

(require redex
         "../test.rkt"
         "uniform.rkt")

(provide (all-defined-out)
         (all-from-out "uniform.rkt"))

(define (test-->>GU t r)
  (test-->>G -->GU t r))
