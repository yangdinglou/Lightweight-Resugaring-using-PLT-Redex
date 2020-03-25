#lang racket
(require redex)
(define (tagged-list? tag exp)
  (and (pair? exp)
       (eq? tag (car exp))))
(define (CoreHead? exp)
  (member (car exp)
          (list 'If
                'lambda
                'Apply))
  )
      
(define (SurfHead? exp)
  (member (car exp)
          (list
           'And
           'Or
           'Let
           'Even
           'Odd)))
(define (CommonHead? exp)
  (member (car exp)
          (list
           '+
           '-
           '*
           '/
           '>
           '<
           'eq?)))
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
           (If Exp Exp Exp)
           (lambda (x_!_ ...) Exp)
           (Apply Exp Exp_!_ ...)
           )
  (Surfexp ::=
           (And Exp Exp)
           (Or Exp Exp)
           (Let (x_!_ ...) (Exp_!_ ...) Exp)
           (Odd Exp)
           (Even Exp)
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
     (If C Exp Exp)
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
   (--> (in-hole C (Apply (lambda (x_1 ..._n) Exp) Exp_1 ..._n))
        (in-hole C (subst ([Exp_1 x_1] ...) Exp))
        "lambda")
   (--> (in-hole C (If #t Exp_1 Exp_2))
        (in-hole C Exp_1)
        "if-true")
   (--> (in-hole C (If #f Exp_1 Exp_2))
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
        (in-hole C (Apply (lambda (x_1 ...) Exp) Exp_1 ...))
        "Let-sugar")
   (--> (in-hole C (And Exp_1 Exp_2))
        (in-hole C (If Exp_1 Exp_2 #f))
        "and")
   (--> (in-hole C (Or Exp_1 Exp_2))
        (in-hole C (If Exp_1 #t Exp_2))
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


(define (approx-exp? exp1 exp2)
  
  (if (and (eq? (length exp1) (length exp2))
           (eq? (car exp1) (car exp2)))
      (if (eq? (foldl + 0
                      (map (lambda (lst1 lst2)
                             (if (eq? lst1 lst2) 0 1))
                           exp1 exp2))
               1)
          #t
          #f)
      #f))
(define (cbv-reduce exp explst)
  (let ((surf 0) (core 0) (ret empty))
    (begin
      (for ([i (length exp)])
        (let ((subexp (list-ref exp i)))
          (if (not (pair? subexp))
              void
              (cond
                ((> core 0) void)
                ((CoreHead? subexp)
                 (begin (set! core i)
                        (let ((newlst (filter (lambda (expinlst) (not (eq? (list-ref expinlst i) subexp)))
                                              explst)))
                          (if (eq? (length newlst) 1)
                              (set! ret (car newlst))
                              ;(begin (displayln newlst)
                              ;(displayln "error1 in cbv-reduce")
                              (set! ret (car (filter (lambda (expinlst) (eq? (list-ref expinlst i) (one-step-reduce subexp)))
                                                     newlst)))
                              ;)
                              ))
                        ))
                ((> surf 0) void)
                ((or (SurfHead? subexp) (CommonHead? subexp))
                 (begin (set! surf i)
                        #;(let ((newlst (filter (lambda (expinlst) (not (eq? (list-ref expinlst i) subexp)))
                                                explst)))
                            (if (eq? (length newlst) 1)
                                (set! ret (car newlst))
                                (set! ret (car (filter (lambda (expinlst) (eq? (list-ref expinlst i) (one-step-reduce subexp)))
                                                       newlst)))
                                )
                            #;(set! ret (car (filter (lambda (expinlst) (approx-exp? (list-ref expinlst i) subexp))
                                                     explst))))
                        (set! ret (list-set exp i (one-step-reduce subexp)))
                        ))
                (else (begin (display subexp) (error "error2 in cbv-reduce")))))))
      ret)))

(define (one-step-reduce exp)
  (if (pair? exp)
      (let ((explst (apply-reduction-relation Rule exp)))
        (cond
          ((eq? (length explst) 0)
           '())
          ((eq? (length explst) 1)
           (car explst))
          ((CoreHead? exp)
           (let ((tmp (filter (lambda (lst) (not (approx-exp? exp lst)))
                              explst)))
             (begin (display tmp)
                    (if (eq? (length tmp) 1)
                        (car tmp)
                        (error "e1")))))
          ((or (SurfHead? exp) (CommonHead? exp))
           (let ((tmp (filter (lambda (lst) (approx-exp? exp lst))
                              explst)))
             (if (empty? tmp)
                 (error "error") ;(displayln explst) (cbv-reduce exp explst)
                 ;(begin (displayln "begin2") (displayln tmp) (cbv-reduce exp tmp))
                 (cbv-reduce exp tmp)
                 )))
             
          ))
      empty))


#;(one-step-reduce (term (Or #f (Apply (lambda (xx y z) (And xx (Or z (And #f y)))) #t #f (Or #t #f)))))
#;(apply-reduction-relation Rule
                            (term (And (If #t (And #f #t) (And #t #t))
                                       (If #f (Or #t #f) (And #f #t)))
                                  ))


#;(traces Rule
          (term (And (If #t (And #f #t) (And #t #t))
                     (If #f (Or #t #f) (And #f #t)))
                ))
#;(traces Rule
          (term (Or
                 #f
                 (Let
                  (x y z)
                  (#t #f (Or #t #f))
                  (And #f (Or z (And #f y)))))))
#;(traces Rule
          (term (Let (x y z) (1 2 (lambda (t) (+ t 1)))
                        (Apply z x)
                        )))
(traces Rule
          (term 
           (Let (x) (2)
                (Let (x y z) (1 2 (lambda (t) (+ t 1)))
                     (Apply z x)
                     ))))