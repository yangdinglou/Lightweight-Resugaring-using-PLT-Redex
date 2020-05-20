#lang racket
(require redex "subst.rkt")

(reduction-steps-cutoff 10)

(define-language CBV
  (e (e e)
     x
     v)
  (c (v c)
     (c e)
     ;(lambda (x) c)
     hole)
  (v number
     (lambda (x) e))
  
  (x variable-not-otherwise-mentioned))



(define-extended-language CBN CBV
  (e ::= ....
     (lambdaN (x) e)
     (shell e)
     )
  (c ::= ....
     (lambdaN (x) c)
     )
  )

(define reductions
  (reduction-relation
   CBN
   (--> (in-hole c ((lambda (x) e) v))
        (in-hole c (subst (x v e)))
        βv)
   (--> (in-hole c (shell x))
        (in-hole c x)
        shellx)
   (--> (in-hole c (shell (lambdaN (x) e)))
        (in-hole c (lambda (x) (shell e)))
        shell=cbn)
   (--> (in-hole c (shell v))
        (in-hole c v)
        shell=cbv)
   (--> (in-hole c (shell (e_1 e_2)))
        (in-hole c ((shell e_1) (lambda (x_new) (shell e_2))))
        (fresh x_new)
        ;(where (x_new) ,(variable-not-in (term (e_1 e_2)) (term newvar) ))
        shell=app)
   ))
(traces reductions '((lambda (x) ((lambda (y) x) ((lambda (t) t) 1))) 2))

(traces reductions '(shell ((lambdaN (x) ((lambdaN (y) x) ((lambdaN (t) t) 1))) 2)))
