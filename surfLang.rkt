#lang racket
(require redex)
(require "coreLang.rkt")
(define (CoreHead? exp)
  (member (car exp)
          (list 'set!
                'lset!
                'letrec
                'if
                'first
                'rest
                'empty
                'begin))
  )
(define (SurfHead? exp)
  (member (car exp)
          (list
           'map)))
(define (CommonHead? exp)
  (member (car exp)
          (list
           '+
           '-
           '*
           '/
           '>
           '<
           '==
           'cons)))
(define (CbvHead? exp)
  (member (car exp)
          (list
           'map)))
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
(define (SurfExp? exp)
  (if (pair? exp)
      (if (redex-match? lang coreexp (cadr exp))
          #f
          (andmap SurfExp? exp))
      #t))
(define (func desugar-exp desugar-tried exp)
  (define (eq3 e1 e2 e3) (and (equal? e1 e2) (equal? e2 e3)))
  (let ((tmp 0))
    (begin
      (for ((i (length exp)))
        (if (eq3 (list-ref desugar-exp i) (list-ref desugar-tried i) (list-ref exp i))
            (void)
            (if (equal? (list-ref exp i) 'tmpval)
                (set! tmp (+ tmp 1))
                (set! tmp (+ tmp (func (list-ref desugar-exp i) (list-ref desugar-tried i) (list-ref exp i)))))))
      tmp)))
(define (get-index desugar-tried desugar-exp exp)
  (let ((idx -1) (ret -1) (possible empty))
    (begin
      (for ((i (length desugar-exp)))
        (if (equal? (list-ref desugar-exp i) (list-ref desugar-tried i))
            (void)
            (set! idx i)))
      (for ((i (length (cadr exp))))
        (if (and (not (eq? i 0)) (eq? ret -1) (pair? (list-ref (cadr exp) i)))
            (let ((tmpexp (filter (lambda (x) (not (approx-exp? (list-set (cadr exp) i 'tmpval) (cadr x))))
                                  (apply-reduction-relation reductions (list-set exp 1 (list-set (cadr exp) i 'tmpval))))))
              (if (eq? (length tmpexp) 1)
                  (if (equal? 'tmpval (list-ref (cadr (car tmpexp)) idx))
                      (set! ret i)
                      (if (and (not (eq? (list-ref desugar-exp idx) (list-ref (cadr tmpexp) idx)))
                               (eq? 1(func (list-ref desugar-exp idx) (list-ref desugar-tried idx) (list-ref (cadr tmpexp) idx))))
                          (set! ret i)
                          (void))
                      )
                  (begin (displayln tmpexp)(error "1"))))
            (void)))
      ret)))
(define (one-step-try exp)
  (let ((all-possible (apply-reduction-relation reductions exp)))
    (if (CbvHead? (cadr exp))
        (let ((ret empty) (flg #f))
          (begin
            (for ([i (length (cadr exp))])
              (let ([subexp (list-ref (cadr exp) i)])
                (if (or (not (pair? subexp)) flg)
                    (void)
                    (let ((tmplst (filter (lambda (x)
                                            (and (approx-exp? (cadr x) (cadr exp))
                                                 (not (equal? (list-ref (cadr exp) i) (list-ref (cadr x) i)))))
                                          all-possible)))
                      (if (eq? (length tmplst) 1)
                          (begin (set! ret (car tmplst)) (set! flg #t))
                          (error "at line 64 in one-step-try"))))))
            ret))
        (let ((idx -1) (ret empty)  [tmpexp (filter (lambda (x) (not (approx-exp? (cadr exp) (cadr x))))
                                                    all-possible)]);desugar-exp
          (begin
            (if (eq? (length tmpexp) 1)
                (let ((desugar-tried (core-algo (car tmpexp))));todo:core-algo
                  (if (approx-exp? (cadr desugar-tried) (cadr (car tmpexp)))
                          (set! idx (get-index (cadr desugar-tried) (cadr (car tmpexp)) exp))
                          (set! ret desugar-tried)))
                (error "at line 80"))
            (if (not (empty? ret))
                ret
                (car (filter (lambda (x)
                               (and (approx-exp? (cadr x) (cadr exp))
                                    (not (equal? (list-ref (cadr exp) idx) (list-ref (cadr x) idx)))))
                             all-possible))))))))
      
      
          

(define (get-recur-seq exp)
  (let ((tmpexp (core-algo exp)))
    (if (empty? (cadr exp))
        empty
        (if (SurfExp? (cadr exp))
            (append (list (cadr exp)) (get-recur-seq tmpexp));todo:add support for get
            (get-recur-seq tmpexp)))
    ))
    
  
(define (core-algo exp)
  (if (pair? (cadr exp))
      (let ((explst (apply-reduction-relation reductions exp)))
        (cond
          ((equal? (length explst) 0) empty)
          ((equal? (length explst) 1) (car explst))
          ((redex-match? lang coreexp (cadr exp));corner case:(if (and (and ...) (or ...)) ...)
           (let ((tmp (filter (lambda (lst) (not (approx-exp? (cadr exp) (cadr lst))))
                              explst)));maybe have not cover some corner cases
             (if (eq? (length tmp) 1)
                 (car tmp)
                 (let ((idx -1) (ret empty))
                   (begin
                     (for ((i (length explst)))
                       (for ((j (length (cadr exp))))
                         (if (eq? idx -1)
                             (if (eq? (list-ref (cadr exp) j) (list-ref (cadr (list-ref explst i)) j))
                                 (void)
                                 (set! idx j))
                             (if (eq? (list-ref (cadr exp) j) (list-ref (cadr (list-ref explst i)) j))
                                 (void)
                                 (if (eq? j idx) (void) (error exp))))))
                     (let ((subexp (core-algo (list (car exp) (list-ref (cadr exp) idx)))))
                       (for ((i (length explst)))
                         (if (empty? ret)
                             (if (equal? (cadr subexp) (list-ref (cadr (list-ref explst i)) idx))
                                 (set! ret (list-ref explst i))
                                 (void))
                           (void))))
                     ret)))))
          ((or (redex-match? lang commonexp (cadr exp)) (redex-match? lang surfexp (cadr exp)))
           (let ((tmp (filter (lambda (lst) (approx-exp? (cadr exp) (cadr lst)))
                              explst)))
             (if (empty? tmp)
                 (begin (displayln explst) (error "error"))
                 ;(cbv-reduce exp tmp)
                 (one-step-try exp)
                 )))))
      (list (car exp) empty)))

(core-algo (term ((store)
                  (if (and (if #t #t #f) (or #t #f)) 1 2)
                  )))
;(apply-reduction-relation reductions (start (if #t 1 2)))
        