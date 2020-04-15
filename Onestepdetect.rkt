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
(define (get-change-loc exp desugar-exp desugar-onestep)
  (let ((loc -1))
    (for ([i (length desugar-exp)])
      (if (not (equal? (list-ref desugar-exp i) (list-ref desugar-onestep i)))
          (if (member (list-ref desugar-exp i) exp)
              (let ((tmp (indexes-of exp (list-ref desugar-exp i))))
                (if (equal? (length tmp) 1)
                    (set! loc (car tmp))
                    (let ((tmpexp empty))
                      (begin
                        (for-each (lambda (tmploc)
                                    (begin
                                      (set! tmpexp (list-set exp tmploc (one-step-reduce (list-ref exp tmploc))))
                                      (let ((tmpexplst (apply-reduction-relation Rule tmpexp)))
                                        (let ((desugar-tmpexp (car (filter (lambda (lst) (not (approx-exp? tmpexp lst)))
                                                                           tmpexplst))))
                                          (let ((desugar-tmponestep (one-step-reduce desugar-tmpexp)))
                                            (for ([ii (length desugar-tmpexp)])
                                              (if (not (equal? (list-ref desugar-tmpexp ii) (list-ref desugar-tmponestep ii)))
                                                  (if (not (equal? (list-ref desugar-tmpexp ii) (list-ref desugar-exp i)))
                                                      (set! loc tmploc)
                                                      (void))
                                                  (void))))))))
                                  tmp)
                        (if (not (equal? -1 loc))
                            loc
                            (set! loc (get-change-loc exp (list-ref desugar-exp i) (list-ref desugar-onestep i))))))))
              (set! loc (get-change-loc exp (list-ref desugar-exp i) (list-ref desugar-onestep i))))
          (void)))
    loc))
            
(define (one-step-try exp explst)
  (if (CommonHead? exp)
      (cbv-reduce exp (filter (lambda (lst) (approx-exp? exp lst))
                              explst))
      (let ((desugar-exp (car (filter (lambda (lst) (not (approx-exp? exp lst)))
                                      explst)))
            (tmp (filter (lambda (lst) (approx-exp? exp lst))
                         explst)))
    
        (let ((desugar-onestep (one-step-reduce desugar-exp)))
          (if (approx-exp? desugar-exp desugar-onestep)
              (let ((tmploc (get-change-loc exp desugar-exp desugar-onestep)))
                (list-set exp tmploc (one-step-reduce (list-ref exp tmploc)))
                )
              (cbv-reduce exp tmp))))))
                     

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
                 (one-step-try exp explst)
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
(traces Rule
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
 (term (Sg (And #t #t) #f)))
(displayln "")
(get-step
 (term (Myor (And #t #f) (Or #f #t))))
#;(apply-reduction-relation Rule
                          (term (Let (x y z) (1 2 (Lambda (t) (+ t 1)))
                                     (Apply z x)
                                     )
                                ))