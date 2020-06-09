#lang racket
(require redex "subst.rkt")

(reduction-steps-cutoff 10)

(define-language lang
  (e (e e)
     (abort e)
     (+ e e)
     x
     v)
  (c (v c)
     (c e)
     (+ c e)
     (+ v c)
     hole)
  (v call/cc
     number
     (lambda (x) e))
  
  (x (variable-except lambda call/cc abort)))

(define reductions
  (reduction-relation
   lang
   (--> (in-hole c (call/cc v))
        (in-hole c (v (lambda (x) (abort (in-hole c x)))))
        call/cc
        (fresh x))
   (--> (in-hole c (+ v_1 v_2))
        (in-hole c ,(+ (term v_1) (term v_2)))
        +)
   (--> (in-hole c (abort e)) 
        e
        abort)
   (--> (in-hole c ((lambda (x) e) v))
        (in-hole c (subst (x v e)))
        βv)))

;(traces reductions '((lambda (x) (x x)) (lambda (x) (x x))))
;(traces reductions '((call/cc call/cc) (call/cc call/cc)))
;(traces reductions '((lambda (x) ((call/cc call/cc) x)) (call/cc call/cc)))
(traces reductions '(+
    (call/cc 
        (lambda (c)
            (+ (c 2) 3))) 5))