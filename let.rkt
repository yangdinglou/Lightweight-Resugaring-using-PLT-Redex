#lang racket
   
;; basic definitions for the Redex Summer School 2015
   
(provide
 ;; Language 
 Lambda
   
 ;; ((Lambda x) ...) Lambda -> Lambda
 ;; (subs ((e_1 x_1) ...) e) substitures e_1 for x_1 ... in e
 ;; e_1, ... e are in Lambda or extensions of Lambda that 
 ;; do not introduce binding constructs beyond lambda 
 subst)
   
;; -----------------------------------------------------------------------------
(require redex)
   
(define-language Lambda
  (e ::=
     x 
     (lambda (x_!_ ...) e)
     (If e e e)
     (Zero? e)
     (+ e e)
     (- e e)
     (* e e)
     (/ e e)
     (> e e)
     (< e e)
     ;(e e ...)
     (e e)
     v
     )
  (v ::=
     (lambda (x_!_ ...) e)
     natural boolean)
  (x ::= variable-not-otherwise-mentioned))

;; -----------------------------------------------------------------------------
;; (subst ([e x] ...) e_*) substitutes e ... for x ... in e_* (hygienically)

(define-metafunction Lambda
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x ...) any_body))
   (lambda (x_new ...)
     (subst ((any_1 x_1) ...)
            (subst-raw ((x_new x) ...) any_body)))
   (where  (x_new ...)  ,(variables-not-in (term (any_body any_1 ...)) (term (x ...)))) ]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])
   
(define-metafunction Lambda
  subst-raw : ((x x) ...) any -> any
  [(subst-raw ((x_n1 x_o1) ... (x_new x) (x_n2 x_o2) ...) x) x_new]
  [(subst-raw ((x_n1 x_o1) ... ) x) x]
  [(subst-raw ((x_n1 x_o1) ... ) (lambda (x ...) any))
   (lambda (x ...) (subst-raw ((x_n1 x_o1) ... ) any))]
  [(subst-raw [(any_1 x_1) ... ] (any ...))
   ((subst-raw [(any_1 x_1) ... ] any) ...)]
  [(subst-raw [(any_1 x_1) ... ] any_*) any_*])

(define-extended-language Lambda-calculus Lambda
  (e ::= .... natural boolean Sugar)
  (Sugar ::=
         (Let (x_!_ ...) (e_!_ ...) e)
         (And e e)
         (Or e e)
         (Odd e)
         (Even e)
         )
 
  ; a context is an expression with one hole in lieu of a sub-expression 
  (C ::=
     hole
     (e ... C e ...)
     (v C)
     
     (lambda (x_!_ ...) C)
     (If C e e)
     (Zero? C)
     (+ C e)
     (- C e)
     (* C e)
     (/ C e)
     (> C e)
     (< C e)
     ;Sugar
     (Let (x_!_ ...) C e)
     (Let (x_!_ ...) e C)
     (And C e)
     (Or C e)
     (Or e C)
     (Odd C)
     (Even C)
     )
  )

(define -->β
  (reduction-relation
   Lambda-calculus
   (--> (in-hole C ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole C (subst ([e_1 x_1] ...) e))
        "1")
   #;(--> (in-hole C (Let (x_1 ..._n) (e_1 ..._n) e))
          (in-hole C ((lambda (x_1 ...) ((lambda () e))) e_1 ...))
          "2")
   (--> (in-hole C (Let (x_1 ..._n) (e_1 ..._n) e))
        (in-hole C ((lambda (x_1 ...) e) e_1 ...))
        "3")
   (--> (in-hole C (If #t e_1 e_2))
        (in-hole C e_1)
        "4")
   (--> (in-hole C (If #f e_1 e_2))
        (in-hole C e_2)
        "5")
   (--> (in-hole C (And e_1 e_2))
        (in-hole C (If e_1 e_2 #f))
        "6")
   #;(--> (in-hole C (And #f e))
          (in-hole C #f)
          "7")
   (--> (in-hole C (Or e_1 e_2))
        (in-hole C (If e_1 #t e_2))
        "7")
   #;(--> (in-hole C (Or #f e))
          (in-hole C e)
          "9")
   (--> (in-hole C (Zero? v))
        (in-hole C ,(= (term v) 0))
        "8")
   (--> (in-hole C (+ v_1 v_2))
        (in-hole C ,(+ (term v_1) (term v_2)))
        "9")
   (--> (in-hole C (- v_1 v_2))
        (in-hole C ,(- (term v_1) (term v_2)))
        "10")
   (--> (in-hole C (* v_1 v_2))
        (in-hole C ,(* (term v_1) (term v_2)))
        "11")
   (--> (in-hole C (/ v_1 v_2))
        (in-hole C ,(/ (term v_1) (term v_2)))
        "12")
   (--> (in-hole C (< v_1 v_2))
        (in-hole C ,(< (term v_1) (term v_2)))
        "13")
   (--> (in-hole C (> v_1 v_2))
        (in-hole C ,(> (term v_1) (term v_2)))
        "14")
   
   (--> (in-hole C (Odd v))
        (in-hole C (Even ,(- (term v) 1)))
        "15"
        (side-condition (> (term v) 1)))
   (--> (in-hole C (Odd 0))
        (in-hole C #t)
        "16")
   (--> (in-hole C (Odd 1))
        (in-hole C #f)
        "17")
   (--> (in-hole C (Even v))
        (in-hole C (Odd ,(- (term v) 1)))
        "18"
        (side-condition (> (term v) 1)))
   (--> (in-hole C (Even 0))
        (in-hole C #f)
        "19")
   (--> (in-hole C (Even 1))
        (in-hole C #t)
        "20")
   ))
(define (tagged-list? tag l)
  (and (pair? l)
       (eq? tag (car l))))
(define (expfilter exp) #t
  #;(cond ((tagged-list? 'If exp) #f)
        ((= (length exp) 0) #t)
        (else (and (expfilter (car exp)) (expfilter (car exp)))))
  )

#;(traces -->β
          (term (Let (x) (#f) (Or x (Let (x y z) (#t #f (Or #t #f))
                                   (And x (Or z (And x y)))
                                         ;x
                                   )))))
#;(traces -->β
        (term (Let (x) (2)
                   (Let (x y z) (1 2 (lambda (t) (+ t 1)))
                        (z x)
                        )))
        )
#;(traces -->β
        (term (Let (x) (2)
                   (Let (x y z) (1 2 (lambda (t) (+ t 1)))
                        (z x)
                        )))
        #:filter
        (lambda (exp name) (expfilter exp))
        )
#;(traces -->β
          (term (Even 3))
          #:filter
          (lambda (exp name) (expfilter exp))
          )