#lang racket
(require redex)
(require "Lang.rkt")
(define (tagged-list? tag exp)
  (and (pair? exp)
       (eq? tag (car exp))))
(define (CoreHead? exp)
  (member (car exp)
          (list 'if
                'lambda
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

(define (map-of-order head)
  (cond
    ((equal? head 'if) '(1 2 3))
    ((or (equal? head '+)
         (equal? head '-)
         (equal? head '*)
         (equal? head '/)
         (equal? head '>)
         (equal? head '<)
         (equal? head 'eq?))
     '(1 2))
    (else "error in mapoforder")))
(define (map-of-template head)
  (cond
    ((equal? head 'Sg) '(Sg Exp1 Exp2))
    ((equal? head 'And) '(And Exp1 Exp2))
    ((equal? head 'Or) '(Or Exp1 Exp2))
    (else empty)))
(define (exp-to-num exp)
  (cond
    ((equal? exp 'Exp1) 1)
    ((equal? exp 'Exp2) 2)
    ((equal? exp 'Exp3) 3)
    (else (error "please add more in exp-to-num"))))
(define (tmpexp? exp)
  (member exp '(Exp1 Exp2 Exp3)))
(define (desugar-total exp)
  (if (pair? exp)
      (if (SurfHead? exp)
          (let ((desugar-exp (car (filter (lambda (lst) (not (approx-exp? exp lst)))
                                          (apply-reduction-relation Rule exp)))))
            (desugar-total desugar-exp))
          (let ((tmpexp exp))
            (begin
              (for ((i (length exp)))
                (set! tmpexp (list-set tmpexp i (desugar-total (list-ref exp i)))))
              tmpexp)))
      exp))
(define (get-order-recur exp);corner case:some exp useless in exp
  (let ((tmporder (map-of-order (car exp))) (tmpout empty))
    (begin
      (for-each (lambda (loc)
                  (if (pair? (list-ref exp loc))
                      (let ((ret (get-order-recur (list-ref exp loc))))
                        (for-each (lambda (retnum)
                                    (if (member retnum tmpout)
                                        (void)
                                        (set! tmpout (append tmpout (list retnum)))))
                                  ret
                                  ))
                      (if (tmpexp? (list-ref exp loc))
                          (let ((num (exp-to-num (list-ref exp loc))))
                            (if (member num tmpout)
                                (void)
                                (set! tmpout (append tmpout (list num)))
                                   ))
                          (void))))
                tmporder)
      tmpout)))
                      
(define (get-order head)
  (let ((tmpexp (map-of-template head)))
    (let ((desugar-exp (desugar-total tmpexp)))
      (get-order-recur desugar-exp))))
      
(define (SurfExp? exp)
  (if (pair? exp)
      (if (CoreHead? exp)
          #f
          (andmap SurfExp? exp))
      #t))
(define (approx-exp? exp1 exp2)
  (if (and (pair? exp1) (pair? exp2))
      (if (and (equal? (length exp1) (length exp2))
               (equal? (car exp1) (car exp2)))
          (if (equal? (foldl + 0
                             (map (lambda (lst1 lst2)
                                    (if (equal? lst1 lst2) 0 1))
                                  exp1 exp2))
                      1)
              (not (or (member exp1 exp2) (member exp2 exp1)))
              #f)
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
                              #;(set! ret (car (filter (lambda (expinlst) (eq? (list-ref expinlst i) (one-step-reduce subexp)))
                                                     newlst)))
                              (set! ret (list-set exp i (one-step-reduce subexp)))
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
                            (set! ret (car (filter (lambda (expinlst) (approx-exp? (list-ref expinlst i) subexp))
                                                     explst))))
                        
                        (set! ret (list-set exp i (one-step-reduce subexp)))
                        ))
                ))))
      ret)))
            
(define (one-step-try exp)
  (if (equal? empty (map-of-template (car exp)))
      (cbv-reduce exp (filter (lambda (lst) (approx-exp? exp lst))
                              (apply-reduction-relation Rule exp)))
      (let ((tmporder (get-order (car exp))) (tmpexp exp) (flag #f))
        (begin
          (for ((i (length exp)))
            (if flag
                (void)
                (let ((subexp (one-step-reduce (list-ref exp (list-ref tmporder i)))))
                  (if (equal? empty subexp)
                      (void)
                      (begin (set! tmpexp (list-set tmpexp (list-ref tmporder i) subexp)) (set! flag #t))))))
          (if flag
              tmpexp
              (error "in onesteptry2"))))))
          
        
(define (one-step-reduce exp)
  (if (pair? exp)
      (let ((explst (apply-reduction-relation Rule exp)))
        (cond
          ((eq? (length explst) 0)
           '())
          ((eq? (length explst) 1)
           (car explst))
          ((CoreHead? exp);Rule1
           (let ((tmp (filter (lambda (lst) (not (approx-exp? exp lst)))
                              explst)))
             (begin (display "Core") (displayln tmp)
                    (if (eq? (length tmp) 1)
                        (car tmp)
                        (error "e1")))))
          ((or (SurfHead? exp) (CommonHead? exp));Rule0 2
           (let ((tmp (filter (lambda (lst) (approx-exp? exp lst))
                              explst)))
             (if (empty? tmp)
                 (begin (displayln explst) (error "error")) ;(displayln explst) (cbv-reduce exp explst)
                 ;(begin (displayln "begin2") (displayln tmp) (cbv-reduce exp tmp))
                 ;(cbv-reduce exp tmp)
                 (one-step-try exp)
                 )))
             
          ))
      empty))


(define (get-step exp)
  (let ((tmp (one-step-reduce exp)))
    (if (equal? tmp empty)
        (void)
        (begin (if (SurfExp? tmp) (displayln tmp) void) #;(displayln tmp) (get-step tmp))
        )))


#;(apply-reduction-relation Rule
                            (term (Let (x) (2) (apply (lambda (x y z) (apply z x)) 1 2 (lambda (t) (+ t 1))))))

#;(traces Rule
          (term (And (if #t (And #f #t) (And #t #t))
                     (if #f (Or #t #f) (And #f #t)))
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
                        (apply z x)
                        )))
#;(traces Rule
          (term 
           (Let (x) (2)
                (+ (+ 1 (Let (x y z) (1 2 (Lambda (t) (+ t 1)))
                        (Apply z x)
                        )) x))))
(get-step (term 
           (Let (x) (2)
                (+ (+ 1 (Let (x y z) (1 2 (Lambda (t) (+ t 1)))
                        (Apply z x)
                        )) x))))
(displayln "")
#;(get-step
 (term (And (if #t (And #f #t) (And #t #t))
            (if #f (Or #t #f) (And #f #t)))
       ))
;(displayln "")
(get-step
 (term (Sg (And #t #t) (And #t #f))))
(displayln "")
(get-step
 (term (Myor (And #t #f) (Or #f #t))))
#;(apply-reduction-relation Rule
                          (term (Let (x y z) (1 2 (Lambda (t) (+ t 1)))
                                     (Apply z x)
                                     )
                                ))