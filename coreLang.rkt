#lang racket
(require redex)
(provide lang
         surface-lang
         run)

(define-language surface-lang
  (e (set! x e)
     (let ((x_!_ e) ...) e)
     (letrec ((x_!_ e) ...) e)
     (if e e e)
     (first e)
     (rest e)
     (empty e)
     (cons e e)
     (map e e)
     (begin e e ...)
     (e e ...)
     x
     v)
  (v fv sv)
  (fv (λ (x_!_ ...) e) + - * =)
  (sv number
      (void)
      xx yy
      #t
      #f
      (list e ...)
      S K I
      )
  (x variable-not-otherwise-mentioned)

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))

(define-extended-language lang surface-lang
  (p ((store (x_!_ e) ...)
      e))
  (e ::= ....
     undefined
     (lset! x e))
  (o ::= procedure sv)
  (P ((store (x e) ...) E))
  (E (v ... E e ...)
     (set! x E)
     (lset! x E)
     (let ((x e) ... (x E) (x e) ...) e)
     (if E e e)
     (begin E e e ...)
     (first E)
     (rest E)
     (empty E)
     (cons E e)
     (cons v E)
     (map E e)
     (map v E)
     (list v ... E e ...)
     hole)
  )

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

(define reductions
  (reduction-relation
   lang #:domain p
   (==> (in-hole P_1 (begin v e_1 e_2 ...))
        (in-hole P_1 (begin e_1 e_2 ...))
        "begin many")

   (==> (in-hole P_1 (begin e_1))
        (in-hole P_1 e_1)
        "begin one")

   (==> ((store (x_before e_before) ...
                (x_i e_i)
                (x_after e_after) ...)
         (in-hole E_1 x_i))
        ((store (x_before e_before) ...
                (x_i e_i)
                (x_after e_after) ...)
         (in-hole E_1 e_i))
        "get")

   (==> ((store (x_before e_before) ...
                (x_i v_old)
                (x_after e_after) ...)
         (in-hole E (set! x_i v_new)))
        ((store (x_before e_before) ...
                (x_i v_new)
                (x_after e_after) ...)
         (in-hole E (void)))
        "set!")
   (==> ((store (x_before e_before) ...
                (x_i e)
                (x_after e_after) ...)
         (in-hole E (lset! x_i v_new)))
        ((store (x_before e_before) ...
                (x_i v_new)
                (x_after e_after) ...)
         (in-hole E (void)))
        "lset!")

   #;(==> (in-hole P ((λ (x ..._1) e) v ..._1))
        (in-hole P (let ([x v] ...) e))
        "βv")
   (==> (in-hole P ((λ (x_0 x_1 ... x) e_0) e_1 e_2 ... e))
        (in-hole P (let ([x_0 e_1]) ((λ (x_1 ... x) e_0) e_2 ... e)))
        "βn")
   (==> (in-hole P ((λ (x_0 x_1 ... x) e_0) e_1))
        (in-hole P (let ([x_0 e_1]) (λ (x_1 ... x) e_0)))
        "βn1")
   (==> (in-hole P ((λ (x) e_0) e_1 e_2 ... e))
        (in-hole P (let ([x e_1]) (e_0 e_2 ... e)))
        "βns")
   (==> (in-hole P ((λ (x) e_0) e_1))
        (in-hole P (let ([x e_1]) e_0))
        "βn0")

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
   (==> (in-hole P (zero? number))
        (in-hole P (δ zero? number))
        "zero")

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
   (==> (in-hole P (empty (list v_1 ...)))
        (in-hole P #f)
        "emptyf")
   

   (==> ((store (x_old e_old) ...)
         (in-hole E (let ([x_1 e_1] [x_2 e_2] ...) e)))
        ((store (x_old e_old) ... (x_new e_1))
         (in-hole E (let ([x_2 e_2] ...) (substitute e x_1 x_new))))
        (fresh x_new)
        "let1")
   (==> (in-hole P (let () e))
        (in-hole P e)
        "let0")
   
   (==> (in-hole P (letrec ((x e_1) ...) e_2))
        (in-hole P (let ((x undefined) ...) (begin (lset! x e_1) ... e_2)))
        "letrec")

   (==> (in-hole P (map (list sv_1 sv_2 ...) e))
        (in-hole P (cons (e sv_1) (map (list sv_2 ...) e)))
        "maps")
   (==> (in-hole P (map (list) e))
        (in-hole P (list))
        "map0")
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
#;(run
    (term (let ((f (λ (x) (+ 1 x))))
            (map (list 1 2) f))))
#;(run
    (term (((λ (x y) (+ x y)) xx) yy)))

(run (term (S (K (S I)) K xx yy )))
;(run (term (S I (K xx) yy)))
;(run (term (I yy ((K xx) yy))))
