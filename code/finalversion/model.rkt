#lang racket
(require redex)
(provide lang
         reductions
         run)

(define-language lang
  (e ::=
     coreexp
     commonexp
     surfexp)
  (coreexp ::=
           (λN (x_!_ ...) e)
           (coreexp e ...)
           (let ((x_!_ e) ...) e)
           (if e e e)
           (first e)
           (rest e)
           (empty e)
           
           (begin e e ...))
  (surfexp ::=
           (surfexp e ...)
           (map e e)
           (filter e e)
           
           (and e e)
           (or e e)
           (Myor e e)
           (not e)
           (Let x e e)
           (Sg e e e)
           (Hygienicadd e e)

           (S comb) (K comb) (I comb)
           (SS comb) (KK comb) (II comb)
           ;(S e ...)
           ;(K e ...)
           ;(I e ...)
           (Odd e)
           (Even e))
  (commonexp ::=
             (commonexp e ...);lambda?
             (cons e e)
             (+ e e ...)
             (- e e ...)
             (* e e ...)
             (/ e e ...)
             (== e e)
             (> e e)
             (< e e)
             x
             v)
           
  (v ::=
     lambda
     number
     (void)
     xx yy
     boolean
     tmpval;for one-step-try
     (list e ...)
     )
  (lambda ::=
          (λ (x_!_ ...) e))

  (x variable-not-otherwise-mentioned)
  
  (p ((store (x_!_ v) ...)
      e))
  (P ((store (x v) ...) E))
  (E (v ... E e ...)
     ;(let ((x v) ... (x E) (x e) ...) e)
     (if E e e)
     (begin E e e ...)
     (first E)
     (rest E)
     (empty E)
     (cons E e)
     (cons v E)
     (list v ... E e ...)
     (+ v ... E e ...)
     (- v ... E e ...)
     (* v ... E e ...)
     (/ v ... E e ...)
     (== E e)
     (== v E)
     (> E e)
     (> v E)
     (< E e)
     (< v E)
     (map E e)
     (map e E)
     (Let x E e)
     (Let x e E)
     (and E e)
     (and e E)
     (or E e)
     (or e E)
     (Myor E e)
     (Myor e E)
     (not E)
     (Sg e e E)
     (Sg e E e)
     (Sg E e e)
     (Hygienicadd E e)
     (Hygienicadd e E)
     (Odd E)
     (Even E)

     ((S comb) e ... E e ...)
     ((K comb) e ... E e ...)
     ((I comb) e ... E e ...)
     ((SS comb) e ... E e ...)
     ((KK comb) e ... E e ...)
     ((II comb) e ... E e ...)
     
     hole)
  
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (λN (x ...) e #:refers-to (shadow x ...))
  (Let x e e_body #:refers-to (shadow x))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))

(define reductions
  (reduction-relation
   lang ;#:domain p
   #;(--> (in-hole P_1 (begin v e_1 e_2 ...))
        (in-hole P_1 (begin e_1 e_2 ...))
        "begin many")

   #;(--> (in-hole P_1 (begin e_1))
        (in-hole P_1 e_1)
        "begin one")

   (--> (in-hole P ((λ (x_0 x_1 ... x) e_0) v_0 v_1 ... v))
        (in-hole P (let ([x_0 v_0]) ((λ (x_1 ... x) e_0) v_1 ... v)))
        "βv")
   (--> (in-hole P ((λ (x_0 x_1 ... x) e_0) v_0))
        (in-hole P (let ([x_0 v_0]) (λ (x_1 ... x) e_0)))
        "βv1")
   (--> (in-hole P ((λ (x) e_0) v_0 v_1 ... v))
        (in-hole P (let ([x v_0]) (e_0 v_1 ... v)))
        "βvs")
   (--> (in-hole P ((λ (x) e_0) v_0))
        (in-hole P (let ([x v_0]) e_0))
        "βv0")

   (--> (in-hole P ((λN (x_0 x_1 ... x) e_tmp) e_0 e_1 ... e))
        (in-hole P (let ([x_0 e_0]) ((λN (x_1 ... x) e_tmp) e_1 ... e)))
        "βn")
   (--> (in-hole P ((λN (x_0 x_1 ... x) e) e_0))
        (in-hole P (let ([x_0 e_0]) (λN (x_1 ... x) e)))
        "βn1")
   (--> (in-hole P ((λN (x) e_tmp) e_0 e_1 ... e))
        (in-hole P (let ([x e_0]) (e_tmp e_1 ... e)))
        "βns")
   (--> (in-hole P ((λN (x) e_tmp) e_0))
        (in-hole P (let ([x e_0]) e_tmp))
        "βn0")

   (--> (in-hole P (= number_1 number_2 ...))
        (in-hole P ,(apply = (term (number_1 number_2 ...))))
        "=")
   (--> (in-hole P (- number_1 number_2 ...))
        (in-hole P ,(apply - (term (number_1 number_2 ...))))
        "-")
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P (* number ...))
        (in-hole P ,(apply * (term (number ...))))
        "*")
   (--> (in-hole P (> number_1 number_2))
        (in-hole P ,(> (term number_1) (term number_2)))
        ">")
   (--> (in-hole P (< number_1 number_2))
        (in-hole P ,(< (term number_1) (term number_2)))
        "<")
   (--> (in-hole P (== number_1 number_2))
        (in-hole P ,(equal? (term number_1) (term number_2)))
        "==")

   (--> (in-hole P (if #f e_then e_else))
        (in-hole P e_else)
        "iff")
   (--> (in-hole P (if v e_then e_else))
        (in-hole P e_then)
        (side-condition (not (equal? (term v) #f)))
        "ift")
   
   (--> (in-hole P (first (list v_1 v_2 ...)))
        (in-hole P v_1)
        "first")
   (--> (in-hole P (rest (list v_1 v_2 ...)))
        (in-hole P (list v_2 ...))
        "rest")
   (--> (in-hole P (cons v_1 (list v_2 ...)))
        (in-hole P (list v_1 v_2 ...))
        "cons")
   (--> (in-hole P (empty (list)))
        (in-hole P #t)
        "emptyt")
   (--> (in-hole P (empty (list v_1 ... v)))
        (in-hole P #f)
        "emptyf")
   

   (--> ((store (x_old v_old) ...)
         (in-hole E (let ([x_1 e_1] [x_2 e_2] ...) e)))
        ((store (x_old v_old) ...)
         (in-hole E (let ([x_2 e_2] ...) (substitute e x_1 e_1))))
        "let1")
   (--> (in-hole P (let () e))
        (in-hole P e)
        "let0")
   (--> (in-hole P (Let x e_1 e_2))
        (in-hole P ((λ (x) e_2) e_1))
        "MyLet")



   (--> (in-hole P (map e_1 e_2))
        (in-hole P (let ((x e_2))(if (empty x) (list) (cons (e_1 (first x)) (map e_1 (rest x))))))
        "map")
   (--> (in-hole P (filter e (list v_1 v_2 ...)))
        (in-hole P (if (e v_1) (cons v_1 (filter e (list v_2 ...))) (filter e (list v_2 ...))))
        "filters")
   (--> (in-hole P (filter e (list)))
        (in-hole P (list))
        "filter0")
   
   (--> (in-hole P (and e_1 e_2))
        (in-hole P (if e_1 e_2 #f))
        "and")
   (--> (in-hole P (or e_1 e_2))
        (in-hole P (if e_1 #t e_2))
        "or")
   (--> (in-hole P (Myor e_1 e_2))
        (in-hole P (let ((tmp e_1)) (if tmp tmp e_2)))
        "Myor")
   (--> (in-hole P (not e_1))
        (in-hole P (if e_1 #f #t))
        "not")
   (--> (in-hole P (Sg e_1 e_2 e_3))
        (in-hole P (and (or e_1 e_2) (not e_3)))
        "Sg")
   (--> (in-hole P (Hygienicadd e_1 e_2))
        (in-hole P (let ((x e_1)) (+ x e_2)))
        "Hygienic add")
   (--> (in-hole P (Odd v))
        (in-hole P (if (> v 0) (Even (- v 1)) #f))
        "Odd")
   (--> (in-hole P (Even v))
        (in-hole P (if (> v 0) (Odd (- v 1)) #t))
        "Even")



   
   (--> (in-hole P (I comb))
        (in-hole P (λ (x) x))
        "I")
   (--> (in-hole P (K comb))
        (in-hole P (λ (x_1 x_2) x_1))
        "K")
   (--> (in-hole P (S comb))
        (in-hole P (λ (x_1 x_2 x_3) (x_1 x_3 (x_2 x_3))))
        "S")
   (--> (in-hole P (II comb))
        (in-hole P (λN (x) x))
        "II")
   (--> (in-hole P (KK comb))
        (in-hole P (λN (x_1 x_2) x_1))
        "KK")
   (--> (in-hole P (SS comb))
        (in-hole P (λN (x_1 x_2 x_3) (x_1 x_3 (x_2 x_3))))
        "SS")
   #;(--> (in-hole P (I e ...))
        (in-hole P ((λ (x) x) e ...))
        "II")
   #;(--> (in-hole P (K e ...))
        (in-hole P ((λ (x_1 x_2) x_1) e ...))
        "KK")
   #;(--> (in-hole P (S e ...))
        (in-hole P ((λ (x_1 x_2 x_3) (x_1 x_3 (x_2 x_3))) e ...))
        "SS")


   ))

(define (run e) (traces reductions (term ((store) ,e))))

#;(run
    (term (filter (λ (x) (and (> x 3) (< x 8))) (list 1 2 3 4 5 6 7 8 9))))

#;(run
    (term (map (λ (x) (+ 1 x)) (list 1 2 3))))
#;(run
    (term ((λ (x) (((λ (x y) (+ x y)) xx) yy)) 1)))
#;(run
    (term
     (((λ (x y) x) xx) ((λ (x) x) yy))
     ))
#;(run
 (term ((λ (x_1 x_2 x_3)
          (x_1 x_3 (x_2 x_3)))
        (λ (x) x)
        ((λ (x_1 x_2) x_1) xx)
        yy)))
#;(run
    (term (Let x (+ 1 2) (Let x 4 (+ x 1)))))
;(run (term (S (K S I) K xx yy)))

;(run (term (S I (K xx) yy)))
#;(apply-reduction-relation/tag-with-names reductions
                                         (term ((store)
                                                (S I (K xx) yy)
                                                )))
#;(run (term (I yy ((K xx) yy))))
;(run (term (if (and (and #t #t) (or #t #f)) 1 2)))
#;(apply-reduction-relation reductions (term ((store)
 (S I (K xx) yy)
 )))

#;(run
    (term (Sg (and #t #f) (not #f) #f)))
#;(run
    (term (Myor (Myor #f #f) (and #t #t))))
#;(run (term ((λ (x) (Let x (+ 1 4) (+ x 1))) 3)))

#;(run
    (term (Odd 6)))

;(run (term I))

#;(run
    (term
     ((SS comb) (II comb) ((KK comb) xx) yy)
     ))
#;(run (term ((λN
   (x_1 x_2 x_3)
   (x_1 x_3 (x_2 x_3)))
  ((λN (x_1 x_2) x_1)
   ((λN
     (x_1 x_2 x_3)
     (x_1 x_3 (x_2 x_3)))
    (λN (x) x)))
  (λN (x_1 x_2) x_1)
  xx
  yy)))
#;(run
    (term
     ((S comb) (I comb) ((K comb) xx) yy)
     ))
#;(run
    (term
     (let ((x 2)) (Hygienicadd 1 x))
     ))