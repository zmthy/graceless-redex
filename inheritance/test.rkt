#lang racket

(require redex
         "../test.rkt"
         "forwarding.rkt"
         "concatenation.rkt"
         "delegation.rkt"
         "merged.rkt"
         "uniform.rkt")

(provide (all-defined-out)
         (all-from-out "forwarding.rkt")
         (all-from-out "concatenation.rkt")
         (all-from-out "delegation.rkt")
         (all-from-out "merged.rkt")
         (all-from-out "uniform.rkt"))

(define (test-->>GF t r)
  (test-->>G -->GF t r))

(define (test-->>GC t r)
  (test-->>G -->GC t r))

(define (test-->>GD t r)
  (test-->>G -->GD t r))

(define (test-->>GO t r)
  (test-->>GF t r)
  (test-->>GC t r)
  (test-->>GD t r))

(define (test-->>GM t r)
  (test-->>G -->GM t r))

(define (test-->>GU t r)
  (test-->>G -->GU t r))

(define (test-->>GI t r)
  (test-->>GM t r)
  (test-->>GU t r))

(define (test-->>GA t r)
  (test-->>GO t r)
  (test-->>GI t r))
