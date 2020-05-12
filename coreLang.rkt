#lang racket
(require redex)
(provide lang
         reductions
         run)

(define-language lang
  (e ::=
     coreexp
     commonexp
     surfexp
     x)
  (coreexp ::=
           (let ((x_!_ e) ...) e)
           (if e e e)
           (first e)
           (rest e)
           (empty e)
           
           (begin e e ...))
  (surfexp ::=
           (e e ...);lambda?
           (map e e)
           
           (and e e)
           (or e e)
           (not e)
           (Let x e e))
  (commonexp ::=
             (cons e e)
             (+ e e ...)
             (- e e ...)
             (* e e ...)
             (/ e e ...)
             (== e e)
             (> e e)
             (< e e)
             v)
           
  (v ::=
     lambda
     number
     (void)
     xx yy
     boolean
     tmpval;for one-step-try
     (list e ...)
     S K I)
  (lambda ::=
          (λ (x_!_ ...) e))

  (x variable-not-otherwise-mentioned)
  
  (p ((store (x_!_ v) ...)
      e))
  (P ((store (x v) ...) E))
  (E (v ... E e ...)
     (let ((x v) ... (x E) (x e) ...) e)
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
     (map v E)
     (Let x E e)
     (Let x e E)
     (and E e)
     (and e E)
     (or E e)
     (or e E)
     (not E)
     (S e ... E e ...)
     (K e ... E e ...)
     (I e ... E e ...)
     
     hole)
  
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (Let x e e_body #:refers-to (shadow x))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))

(define reductions
  (reduction-relation
   lang ;#:domain p
   (==> (in-hole P_1 (begin v e_1 e_2 ...))
        (in-hole P_1 (begin e_1 e_2 ...))
        "begin many")

   (==> (in-hole P_1 (begin e_1))
        (in-hole P_1 e_1)
        "begin one")

   (==> (in-hole P ((λ (x_0 x_1 ... x) e_0) v_0 v_1 ... v))
        (in-hole P (let ([x_0 v_0]) ((λ (x_1 ... x) e_0) v_1 ... v)))
        "βv")
   (==> (in-hole P ((λ (x_0 x_1 ... x) e_0) v_0))
        (in-hole P (let ([x_0 v_0]) (λ (x_1 ... x) e_0)))
        "βv1")
   (==> (in-hole P ((λ (x) e_0) v_0 v_1 ... v))
        (in-hole P (let ([x v_0]) (e_0 v_1 ... v)))
        "βvs")
   (==> (in-hole P ((λ (x) e_0) v_0))
        (in-hole P (let ([x v_0]) e_0))
        "βv0")

   (==> (in-hole P (= number_1 number_2 ...))
        (in-hole P ,(apply = (term (number_1 number_2 ...))))
        "=")
   (==> (in-hole P (- number_1 number_2 ...))
        (in-hole P ,(apply - (term (number_1 number_2 ...))))
        "-")
   (==> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (==> (in-hole P (* number ...))
        (in-hole P ,(apply * (term (number ...))))
        "*")
   (==> (in-hole P (> number_1 number_2))
        (in-hole P ,(> (term number_1) (term number_2)))
        ">")
   (==> (in-hole P (< number_1 number_2))
        (in-hole P ,(< (term number_1) (term number_2)))
        "<")
   (==> (in-hole P (== number_1 number_2))
        (in-hole P ,(equal? (term number_1) (term number_2)))
        "==")

   (==> (in-hole P (if #f e_then e_else))
        (in-hole P e_else)
        "iff")
   (==> (in-hole P (if v e_then e_else))
        (in-hole P e_then)
        (side-condition (not (equal? (term v) #f)))
        "ift")
   
   (==> (in-hole P (first (list v_1 v_2 ...)))
        (in-hole P v_1)
        "first")
   (==> (in-hole P (rest (list v_1 v_2 ...)))
        (in-hole P (list v_2 ...))
        "rest")
   (==> (in-hole P (cons v_1 (list v_2 ...)))
        (in-hole P (list v_1 v_2 ...))
        "cons")
   (==> (in-hole P (empty (list)))
        (in-hole P #t)
        "emptyt")
   (==> (in-hole P (empty (list v_1 ... v)))
        (in-hole P #f)
        "emptyf")
   

   (==> ((store (x_old v_old) ...)
         (in-hole E (let ([x_1 v_1] [x_2 v_2] ...) e)))
        ((store (x_old v_old) ...)
         (in-hole E (let ([x_2 v_2] ...) (substitute e x_1 v_1))))
        "let1")
   (==> (in-hole P (let () e))
        (in-hole P e)
        "let0")
   (==> (in-hole P (Let x e_1 e_2))
        (in-hole P ((λ (x) e_2) e_1))
        "MyLet")


   (==> (in-hole P (map e (list v_1 v_2 ...)))
        (in-hole P (cons (e v_1) (map e (list v_2 ...))))
        "maps")
   (==> (in-hole P (map e (list)))
        (in-hole P (list))
        "map0")
   
   (==> (in-hole P (and e_1 e_2))
        (in-hole P (if e_1 e_2 #f))
        "and")
   (==> (in-hole P (or e_1 e_2))
        (in-hole P (if e_1 #t e_2))
        "or")
   (==> (in-hole P (not e_1))
        (in-hole P (if e_1 #f #t))
        "not")
   (==> (in-hole P I)
        (in-hole P (λ (x) x))
        "I")
   (==> (in-hole P K)
        (in-hole P (λ (x_1 x_2) x_1))
        "K")
   (==> (in-hole P S)
        (in-hole P (λ (x_1 x_2 x_3) (x_1 x_3 (x_2 x_3))))
        "S")

   with
   [(--> a b) (==> a b)]))

(define (run e) (traces reductions (term ((store) ,e))))


#;(run
    (term (map (λ (x) (+ 1 x)) (list 1 2 3))))
#;(run
    (term ((λ (x) (((λ (x y) (+ x y)) xx) yy)) 1)))
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

;(run (term (I yy ((K xx) yy))))
;(run (term (if (and (and #t #t) (or #t #f)) 1 2)))
#;(apply-reduction-relation reductions (term ((store)
 (S I (K xx) yy)
 )))