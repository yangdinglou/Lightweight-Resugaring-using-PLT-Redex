#lang racket
(require redex)
(provide lang
         reductions
         run)
;; collect : term -> term
;; performs a garbage collection on the term `p'
(define (collect p)
  (match p
    [`((store (,vars ,vs) ...) ,e)

     (define (unused-var? var)
       (and (not (in? var e))
            (andmap (λ (rhs) (not (in? var rhs)))
                    vs)))

     (define unused
       (for/list ([var (in-list vars)]
                  #:when (unused-var? var))
         var))

     (cond
       [(null? unused) p]
       [else
        (collect
         (term ((store ,@(filter (λ (binding) (not (memq (car binding) unused)))
                                 (cdar p)))
                ,e)))])]))

(define (in? var body)
  (let loop ([body body])
    (match body
      [(cons a b) (or (loop a) (loop b))]
      [(? symbol?) (equal? body var)]
      [else #f])))

(define-language lang
  (e ::=
     coreexp
     commonexp
     surfexp
     x
     
     undefined)
  (coreexp ::=
           (set! x e)
           (let ((x_!_ e) ...) e)
           (letrec ((x_!_ e) ...) e)
           (if e e e)
           (first e)
           (rest e)
           (empty e)
           
           (begin e e ...)
           (lset! x e))
  (surfexp ::=
           (e e ...);lambda?
           (map e e)
           (and e e)
           (or e e)
           (not e))
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
  (v-or-undefined v undefined)
  
  (p ((store (x_!_ v-or-undefined) ...)
      e))
  (P ((store (x v-or-undefined) ...) E))
  (E (v ... E e ...)
     (set! x E)
     (lset! x E)
     (let ((x v-or-undefined) ... (x E) (x e) ...) e)
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
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))

(define reductions
  (reduction-relation
   lang #:domain p
   (==> (in-hole P_1 (begin v e_1 e_2 ...))
        (in-hole P_1 (begin e_1 e_2 ...))
        "begin many")

   (==> (in-hole P_1 (begin e_1))
        (in-hole P_1 e_1)
        "begin one")

   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v_i)
                (x_after v-or-undefined_after) ...)
         (in-hole E_1 x_i))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_i)
                (x_after v-or-undefined_after) ...)
         (in-hole E_1 v_i))
        "get")

   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v_old)
                (x_after v-or-undefined_after) ...)
         (in-hole E (set! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (in-hole E (void)))
        "set!")
   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v-or-undefined)
                (x_after v-or-undefined_after) ...)
         (in-hole E (lset! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (in-hole E (void)))
        "lset!")

   #;(==> (in-hole P ((λ (x ..._1) e) v ..._1))
        (in-hole P (let ([x v] ...) e))
        "βv")
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
   

   (==> ((store (x_old v-or-undefined_old) ...)
         (in-hole E (let ([x_1 v-or-undefined_1] [x_2 v-or-undefined_2] ...) e)))
        ((store (x_old v-or-undefined_old) ... (x_new v-or-undefined_1))
         (in-hole E (let ([x_2 v-or-undefined_2] ...) (substitute e x_1 x_new))))
        (fresh x_new)
        "let1")
   (==> (in-hole P (let () e))
        (in-hole P e)
        "let0")
   
   (==> (in-hole P (letrec ((x e_1) ...) e_2))
        (in-hole P (let ((x undefined) ...) (begin (lset! x e_1) ... e_2)))
        "letrec")

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
   [(--> a ,(collect (term b))) (==> a b)]))

(define (run e) (traces reductions (term ((store) ,e))))

#;(run
    (term (letrec ((f (λ (x) (begin (set! f x) f))))
            (begin (f 8)
                   f))))
(run
    (term (map (λ (x) (+ 1 x)) (list 1 2 3))))
#;(run
    (term (((λ (x y) (+ x y)) xx) yy)))
#;(run
 (term ((λ (x_1 x_2 x_3)
          (x_1 x_3 (x_2 x_3)))
        (λ (x) x)
        ((λ (x_1 x_2) x_1) xx)
        yy)))

;(run (term (S (K S I) K xx yy)))

;(run (term (S I (K xx) yy)))

;(run (term (I yy ((K xx) yy))))
;(run (term (if (and (and #t #t) (or #t #f)) 1 2)))
#;(apply-reduction-relation reductions (term ((store)
 (S I (K xx) yy)
 )))