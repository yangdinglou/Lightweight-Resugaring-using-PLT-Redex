#lang racket
(require redex)
(provide Test Rule)
(define-language Test
  (Exp ::=
       (Exp Exp)
       x
       Coreexp
       Otherexp)
  (Otherexp :=
            Surfexp
            Commonexp)
  (Coreexp ::=
           (if Exp Exp Exp)
           (lambda (x_!_ ...) Exp)
           (apply Exp Exp_!_ ...)
           )
  (Surfexp ::=
           (And Exp Exp)
           (Or Exp Exp)
           (Let (x_!_ ...) (Exp_!_ ...) Exp)
           (Odd Exp)
           (Even Exp)
           (If Exp Exp Exp)
           (Lambda (x_!_ ...) Exp)
           (Apply Exp Exp_!_ ...)
           )
  (Commonexp ::=
             (+ Exp Exp)
             (- Exp Exp)
             (* Exp Exp)
             (/ Exp Exp)
             (> Exp Exp)
             (< Exp Exp)
             (eq? Exp Exp)
             natural
             boolean
             x
             )
  (v ::=
     natural boolean
     (lambda (x_!_ ...) Exp))
  (x ::= variable-not-otherwise-mentioned)
  (C ::=
     hole
     (Exp ... C Exp ...)
     (v C)
     (if C Exp Exp)
     ;(lambda (x_!_ ...) C)
     (+ C Exp)
     (- C Exp)
     (* C Exp)
     (/ C Exp)
     (> C Exp)
     (< C Exp)
     (Eq? C Exp)
     (+ Otherexp C)
     (- Otherexp C)
     (* Otherexp C)
     (/ Otherexp C)
     (> Otherexp C)
     (< Otherexp C)
     (Eq? Otherexp C)
     
     (And C Exp)
     (And Otherexp C)
     (Or C Exp)
     (Or Otherexp C)
     ;(Let (x_!_ ...) C Exp)
     (Let (x_!_ ...) (Exp_!_ ...) C)
     (Apply C Exp)
     (apply C Exp)
     ))
(define-metafunction Test
  subst : ((any x) ...) any ->
  any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x ...) any_body))
   (lambda (x_new ...)
     (subst ((any_1 x_1) ...)
            (subst-raw ((x_new x) ...) any_body)))
   (where  (x_new ...)  ,(variables-not-in (term (any_body any_1 ...)) (term (x ...)))) ]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])
(define-metafunction Test
  subst-raw : ((x x) ...) any -> any
  [(subst-raw ((x_n1 x_o1) ... (x_new x) (x_n2 x_o2) ...) x) x_new]
  [(subst-raw ((x_n1 x_o1) ... ) x) x]
  [(subst-raw ((x_n1 x_o1) ... ) (lambda (x ...) any))
   (lambda (x ...) (subst-raw ((x_n1 x_o1) ... ) any))]
  [(subst-raw [(any_1 x_1) ... ] (any ...))
   ((subst-raw [(any_1 x_1) ... ] any) ...)]
  [(subst-raw [(any_1 x_1) ... ] any_*) any_*])

(define Rule
  (reduction-relation
   Test
   (--> (in-hole C (apply (lambda (x_1 ..._n) Exp) Exp_1 ..._n))
        (in-hole C (subst ([Exp_1 x_1] ...) Exp))
        "lambda app")
   (--> (in-hole C (Apply Exp_1 ..._n))
        (in-hole C (apply Exp_1 ...))
        "App sugar")
   (--> (in-hole C (Lambda (x_1 ..._n) Exp))
        (in-hole C (lambda (x_1 ...) Exp))
        "Lambda sugar")
   (--> (in-hole C (if #t Exp_1 Exp_2))
        (in-hole C Exp_1)
        "if-true")
   (--> (in-hole C (if #f Exp_1 Exp_2))
        (in-hole C Exp_2)
        "if-false")

   (--> (in-hole C (+ v_1 v_2))
        (in-hole C ,(+ (term v_1) (term v_2)))
        "+")
   (--> (in-hole C (- v_1 v_2))
        (in-hole C ,(- (term v_1) (term v_2)))
        "-")
   (--> (in-hole C (* v_1 v_2))
        (in-hole C ,(* (term v_1) (term v_2)))
        "*")
   (--> (in-hole C (/ v_1 v_2))
        (in-hole C ,(/ (term v_1) (term v_2)))
        "/")
   (--> (in-hole C (< v_1 v_2))
        (in-hole C ,(< (term v_1) (term v_2)))
        "<")
   (--> (in-hole C (> v_1 v_2))
        (in-hole C ,(> (term v_1) (term v_2)))
        ">")
   (--> (in-hole C (Eq? v_1 v_2))
        (in-hole C ,(eq? (term v_1) (term v_2)))
        "Eq?")
   (--> (in-hole C (Let (x_1 ..._n) (Exp_1 ..._n) Exp))
        (in-hole C (apply (lambda (x_1 ...) Exp) Exp_1 ...))
        "Let-sugar")
   (--> (in-hole C (And Exp_1 Exp_2))
        (in-hole C (if Exp_1 Exp_2 #f))
        "and")
   (--> (in-hole C (Or Exp_1 Exp_2))
        (in-hole C (if Exp_1 #t Exp_2))
        "or")
   (--> (in-hole C (Odd v))
        (in-hole C (Even ,(- (term v) 1)))
        "Odd v"
        (side-condition (> (term v) 1)))
   (--> (in-hole C (Odd 0))
        (in-hole C #t)
        "Odd 0")
   (--> (in-hole C (Odd 1))
        (in-hole C #f)
        "Odd 1")
   (--> (in-hole C (Even v))
        (in-hole C (Odd ,(- (term v) 1)))
        "Even v"
        (side-condition (> (term v) 1)))
   (--> (in-hole C (Even 0))
        (in-hole C #f)
        "Even 0")
   (--> (in-hole C (Even 1))
        (in-hole C #t)
        "Even 1")
   ))