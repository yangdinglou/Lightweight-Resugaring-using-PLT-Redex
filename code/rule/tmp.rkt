#lang racket
(require redex)
(require racket/hash)
(struct IFA ([Q #:mutable]
             [Σ #:mutable]
             [δ #:mutable]
             [s #:mutable]
             [F #:mutable]
             [subst #:mutable]
             [alias #:mutable])
  #:transparent)

(define (get-tmp-IFA head)
  (cond 
    [(equal? head 'let) IFA-LET]
    [(equal? head 'if) IFA-IF]))
(define IFA-IF 
  (IFA (list (term oe_1) (term oe_2) (term oe_3))
       (list (term (if oe_1 oe_2 oe_3)) (term (if #t oe_2 oe_3)) (term (if #f oe_2 oe_3)))
       (hash (term oe_1) (hash 'void (term oe_1) #t (term oe_2) #f (term oe_3)))
       (list (term oe_1))
       (list (term oe_2) (term oe_3))
       (hash)
       (hash)
       ))
;(hash-ref (hash-ref (IFA-δ IFA-IF) 'oe_1) 'void)

;(let x e1 e2)-->(let x e1' e2)
;(let x v1 e2)-->(subst x v1 e2)
(define IFA-LET 
  (IFA (list (term ox) (term oe_1) (term ov_1)
             (term oe_2))
       (list (term (let ox oe_1 oe_2)) (term (leto x ov_1 oe_2)))
       (hash (term oe_1) (hash 'void (term oe_1) (term ov_1) (term ov_1)) (term ov_1) (hash 'ov_1 'oe_2))
       (list (term oe_1))
       (list 'oe_2)
       (hash 'oe_2 (hash 'ox 'ov_1) 'ox (hash 'ox 'ox))
       (hash)
       ))

(define IFA-TMP
  (IFA (list (term oe_1) (term oe_2) '#t '#f)
       (list (term (TMP oe_1 oe_2)))
       (hash (term oe_1) (hash '#t (term oe_2) '#f '#f) (term oe_2) (hash '#t '#f '#f '#t))
       (list (term oe_1))
       (list '#t '#f)
       (hash)
       (hash)
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
  (let ((tmpQ (IFA-Q old-IFA)) (tmpΣ (IFA-Σ old-IFA)) (tmpδ (IFA-δ old-IFA))
                               (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA))
                               (tmpsubst (IFA-subst old-IFA)) (tmpalias (IFA-alias old-IFA)))
    (let ((old_term (list-ref (car tmpΣ) loc)) (tmp_term new_term))
      (begin (set! tmpQ (modify-term tmpQ old_term new_term))
             (if (check-duplicates tmpQ)
                 (let ((tmplength (if (hash-has-key? tmpalias tmp_term) (length (hash-ref tmpalias new_term)) 0) ))
                   (begin
                     (set! new_term (string->symbol (string-append (symbol->string new_term) "_a" (number->string tmplength))))
                     (set! tmpQ (list-set tmpQ (last (indexes-of tmpQ tmp_term)) new_term))
                     (hash-set! tmpalias tmp_term (if (hash-has-key? tmpalias tmp_term)
                                                                     (append (hash-ref tmpalias tmp_term) (list new_term))
                                                                     (list new_term)))))
                 (void))
             (set! tmpΣ (modify-term tmpΣ old_term new_term))
             (set! tmpδ (modify-hash tmpδ old_term new_term))
             (set! tmps (modify-term tmps old_term new_term))
             (set! tmpF (modify-term tmpF old_term new_term))
             (set! tmpsubst (modify-hash tmpsubst old_term new_term))
             (set! tmpalias (modify-hash tmpalias old_term new_term))
             (IFA tmpQ tmpΣ tmpδ tmps tmpF tmpsubst tmpalias))))
  )
;(modify-IFA IFA-IF 1 'x)
;(modify-IFA (modify-IFA (modify-IFA IFA-IF 1 'x) 2 'x) 3 'e_2)

(define build-IFA
  (λ (rule)
    (case (car rule)
      [(1) (let ((tmp (get-tmp-IFA (car (list-ref rule 2))))) ;
             (begin
               (for ((i (- (length (list-ref rule 2)) 1)))
                 (if (pair? (list-ref (list-ref rule 2) (+ i 1)))
                     (set! tmp (merge-IFA tmp (+ i 1) (list-ref (list-ref rule 2) (+ i 1))))
                     (set! tmp (modify-IFA tmp (+ i 1) (list-ref (list-ref rule 2) (+ i 1))))))
               tmp))])))
(define (merge-hash old_term old-IFA subIFA)
  (if (member old_term (IFA-F old-IFA))
      (let ((tmphash (modify-hash (IFA-δ old-IFA) old_term (car (IFA-s subIFA)))))
        (begin (hash-union! tmphash (IFA-δ subIFA))tmphash))
      
      (let ((tmphash (IFA-δ old-IFA)) (old_trans (hash-ref (IFA-δ old-IFA) old_term)))
        (begin
          (for ((tmpkey (IFA-F subIFA)))
            (hash-set! tmphash tmpkey old_trans))
          (hash-remove! tmphash old_term)
          (set! tmphash (modify-hash tmphash old_term (car (IFA-s subIFA))))
          (hash-union! tmphash (IFA-δ subIFA))
          tmphash)))
  )
(define (merge-IFA old-IFA loc new_term)
  (let ([tmpQ (IFA-Q old-IFA)]
        [tmpΣ (IFA-Σ old-IFA)] (tmpδ (IFA-δ old-IFA))
        (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA))
        (tmpsubst (hash-copy (IFA-subst old-IFA))) (tmpalias (hash-copy (IFA-alias old-IFA))))
    (let ((old_term (list-ref (car tmpΣ) loc)) (subIFA (build-IFA (list 1 (list) new_term))))
      (begin
        (set! tmpQ (append tmpQ (IFA-Q subIFA)))
        (if (check-duplicates tmpQ)
            (let ((dup_term (check-duplicates tmpQ))
                  (tmplength (if (hash-has-key? tmpalias (check-duplicates tmpQ)) (length (hash-ref tmpalias (check-duplicates tmpQ))) 0)))
              (begin
                (if (hash-has-key? (IFA-alias subIFA) dup_term)
                    (begin
                      (if (eq? tmplength 0)
                          (hash-set! tmpalias dup_term (hash-ref (IFA-alias subIFA) dup_term))
                          (for ((ali-term (hash-ref (IFA-alias subIFA) dup_term)))
                            (let ((tmpnew_term (string->symbol (string-append (symbol->string dup_term) "_a" (number->string tmplength)))))
                              (begin
                                (set! subIFA
                                      (modify-IFA subIFA
                                                  (index-of (car tmpΣ) ali-term)
                                                  tmpnew_term);todo
                                      )
                                (hash-set! tmpalias dup_term (append (hash-ref tmpalias dup_term) (list tmpnew_term)))
                                ))))
                      
                      (let ((copyalias (hash-copy (IFA-alias subIFA))))
                        ;(set-IFA-alias! subIFA (hash-remove copyalias dup_term))
                        (begin
                          (hash-remove! copyalias dup_term)
                          (set-IFA-alias! subIFA copyalias))
                        )
                      ;(hash-remove! subIFA dup_term)
                      )
                    (void))
                (let ((tmpnew_term (string->symbol (string-append (symbol->string dup_term) "_a" (number->string tmplength)))))
                  (begin
                    (set! subIFA
                          (modify-IFA subIFA
                                      (index-of (car tmpΣ) dup_term)
                                      tmpnew_term)
                          )
                    (hash-set! tmpalias dup_term (append (hash-ref tmpalias dup_term) (list tmpnew_term)))
                    ))
                ))
            (void))
        (displayln tmpδ)
        (displayln old_term)
        (displayln old-IFA)
        (displayln subIFA)
        (set! tmpδ (merge-hash old_term old-IFA subIFA))
        (if (member old_term tmps)
            (set! tmps (IFA-s subIFA))
            (void))
        (if (member old_term tmpF)
            (set! tmpF (append (remove old_term tmpF) (IFA-F subIFA)))
            (void))
        (if (hash-has-key? tmpsubst old_term)
            (for ((tmpkey (IFA-Q subIFA)))
              (begin
                (hash-set! tmpsubst tmpkey (hash-ref tmpsubst old_term))
                (if (hash-has-key? (IFA-subst subIFA) tmpkey)
                    (let ((innersubst (hash-ref (IFA-subst subIFA) tmpkey))
                          (outersubst (hash-ref tmpsubst tmpkey)))
                      (begin
                        (for ((tmpkey2 (hash-keys innersubst)))
                          (hash-set! outersubst tmpkey2 (hash-ref innersubst tmpkey2)))
                        (hash-set! tmpsubst tmpkey outersubst)))
                    (void))))
                    
            (hash-union! tmpsubst (IFA-subst subIFA)))
        (hash-union! tmpalias (IFA-alias subIFA))
        (IFA tmpQ tmpΣ tmpδ tmps tmpF tmpsubst tmpalias)
        )
      ))
  )

(merge-IFA (modify-IFA (modify-IFA (modify-IFA IFA-LET 1 'x) 2 'e_1) 3 'e_2) 3 '(if x x e_2))
  
