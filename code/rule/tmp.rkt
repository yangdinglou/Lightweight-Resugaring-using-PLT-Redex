#lang racket
(require redex)
(struct IFA ([Q #:mutable]
             [Σ #:mutable]
             [δ #:mutable]
             [s #:mutable]
             [F #:mutable]
             [subst #:mutable])
  #:transparent)

(define (get-tmp-IFA head)
  (case head
    [('let) IFA-LET]
    [('if) IFA-IF]))
(define IFA-IF 
  (IFA (list (term oe_1) (term oe_2) (term oe_3))
       (list (term (if oe_1 oe_2 oe_3)) (term (if #t oe_2 oe_3)) (term (if #f oe_2 oe_3)))
       (hash (term oe_1) (hash 'void (term oe_1) #t (term oe_2) #f (term oe_3)))
       (list (term oe_1))
       (list (term oe_2) (term oe_3))
       (list)
       ))
;(hash-ref (hash-ref (IFA-δ IFA-IF) 'oe_1) 'void)

;(let x e1 e2)-->(let x e1' e2)
;(let x v1 e2)-->(subst x v1 e2)
(define IFA-LET 
  (IFA (list (term x) (term oe_1) (term ov_1)
             (term (subst x ov_1 oe_2)))
       (list (term (let x oe_1 oe_2)) (term (let x ov_1 oe_2)))
       (hash (term oe_1) (hash 'void (term oe_1) (term ov_1) (term (ov_1))) (term ov_1) (hash 'ov_1 '(subst x ov_1 oe_2)))
       (list (term oe_1))
       (list '(subst x ov_1 oe_2))
       (list)
       ))

(define IFA-TMP
  (IFA (list (term oe_1) (term oe_2) '#t '#f)
       (list (term (TMP oe_1 oe_2)))
       (hash (term oe_1) (hash '#t (term oe_2) '#f '#f) (term oe_2) (hash '#t '#f '#f '#t))
       (list (term oe_1))
       (list '#t '#f)
       (list)
       ))
;(or e1 e2)-->(let x e1 (if x x e2))
;(map f e)-->(if (null? e) (list) (cons (f (first e)) (map f (rest e))))

(define (modify-term trm old_term new_term)
  (if (pair? trm)
      (let ((tmp trm))
        (begin
          (for ((i (length tmp)))
            (if (symbol? (list-ref tmp i))
                (if (equal? (list-ref tmp i) old_term) (set! tmp (list-set tmp i new_term)) (void))
                (set! tmp (list-set tmp i (modify-term (list-ref tmp i) old_term new_term)))))
          tmp))
      (if (equal? trm old_term) new_term trm)))

(define (modify-hash hash-table old_term new_term)
  (let ((tmp-key (hash-keys hash-table)) (tmp-hash (make-hash)))
    (begin
      (for ((key tmp-key))
        (hash-set!
         tmp-hash
         (modify-term key old_term new_term)
         (if (hash? (hash-ref hash-table key))
             (modify-hash (hash-ref hash-table key) old_term new_term)
             (modify-term (hash-ref hash-table key) old_term new_term))))
      tmp-hash)))

;(modify-hash (hash (term oe_1) (hash 'void (term oe_1) (term ov_1) (term (subst x ov_1 oe_2)))) 'oe_1 'e_1)
      


#;(modify-term (list (term x) (term oe_1) 
             (term (subst x ov_1 oe_2))) 'ov_1 'v_1)
(define (modify-IFA old-IFA loc new_term)
  (let ([tmpQ (IFA-Q old-IFA)] [tmpΣ (IFA-Σ old-IFA)] (tmpδ (IFA-δ old-IFA)) (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA)) (tmpsubst (IFA-subst old-IFA)))
    (let ((old_term (list-ref (car tmpΣ) loc)))
      (begin (set! tmpQ (modify-term tmpQ old_term new_term))
             (set! tmpΣ (modify-term tmpΣ old_term new_term))
             (set! tmpδ (modify-hash tmpδ old_term new_term))
             (set! tmps (modify-term tmps old_term new_term))
             (set! tmpF (modify-term tmpF old_term new_term))
             (set! tmpsubst (modify-term tmpsubst old_term new_term))
             (IFA tmpQ tmpΣ tmpδ tmps tmpF tmpsubst))));todo:add node merge
  )
;(modify-IFA (modify-IFA (modify-IFA IFA-IF 1 'x) 2 'x) 3 'e_2)
(define (merge-IFA old-IFA loc new_term)
  (let ([tmpQ (IFA-Q old-IFA)] [tmpΣ (IFA-Σ old-IFA)] (tmpδ (IFA-δ old-IFA)) (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA)) (tmpsubst (IFA-subst old-IFA)))
    (let ((old_term (list-ref (car tmpΣ) loc)) (tmpIFA (build-IFA '(1 (list) new_term))))
      (begin
        (void);todo
        )))
  )
  
  
(define (build-IFA rule)
  (case (car rule)
    [(1) (let ((tmp (get-tmp-IFA (car (list-ref rule 2)))))
           (begin
             (for ((i (- (length (list-ref rule 2)) 1)))
               (if (pair? (list-ref (list-ref rule 2) (+ i 1)))
                   (set! tmp (merge-IFA tmp (+ i 1) (list-ref (list-ref rule 2) (+ i 1))))
                   (set! tmp (modify-IFA tmp (+ i 1) (list-ref (list-ref rule 2) (+ i 1))))))
             tmp))]))