#lang racket
(require redex)
(require "Lang.rkt")
(define (CoreHead? exp)
  (member (car exp)
          (list 'set!

                'letrec
                'if
                'first
                'rest
                'empty
                'begin
                'apply))
  )
(define (SurfHead? exp)
  (member (car exp)
          (list
           'And
           'Or
           'Let
           'Even
           'Odd
           'Apply
           'Lambda
           'Sg
           'Myor
           )))