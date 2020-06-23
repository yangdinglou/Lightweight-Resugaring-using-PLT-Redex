#lang racket
(require redex)
(require racket/hash)
(require dyoo-while-loop)
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
(define subst-cnt 0)
(define IFA-LET 
  (IFA (list (term ox) (term oe_1) (term v_subst)
             (term oe_2))
       (list (term (let ox oe_1 oe_2)) (term (leto x v_subst oe_2)))
       (hash (term oe_1) (hash 'void (term oe_1) (term v_subst) (term v_subst)) (term v_subst) (hash 'v_subst 'oe_2))
       (list (term oe_1))
       (list 'oe_2)
       (hash 'oe_2 (hash 'ox 'v_subst) 'ox (hash 'ox 'ox))
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

#;(modify-term (list (term x) (term oe_1) 
                     (term (subst x ov_1 oe_2))) 'ov_1 'v_1)
(define (modify-IFA old-IFA old_term new_term)
  (let ((tmpQ (IFA-Q old-IFA)) (tmpΣ (IFA-Σ old-IFA)) (tmpδ (IFA-δ old-IFA))
                               (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA))
                               (tmpsubst (IFA-subst old-IFA)) (tmpalias (IFA-alias old-IFA)))
    (let ((tmp_term new_term))
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


(define build-IFA
  (λ (rule)
    (case (car rule)
      [(1) (let ((tmp (get-tmp-IFA (car (list-ref rule 2))))) ;
             (begin
               (if (equal? (car (list-ref rule 2)) 'let)
                   (begin
                     (set! tmp (modify-IFA tmp 'v_subst (string->symbol (string-append "v_subst" (number->string subst-cnt)))))
                     (set! subst-cnt (+ 1 subst-cnt)))
                   (void))
               (for ((i (- (length (list-ref rule 2)) 1)))
                 (if (pair? (list-ref (list-ref rule 2) (+ i 1)))
                     (set! tmp (merge-IFA tmp (list-ref (car (IFA-Σ tmp)) (+ i 1)) (list-ref (list-ref rule 2) (+ i 1))))
                     (set! tmp (modify-IFA tmp (list-ref (car (IFA-Σ tmp)) (+ i 1)) (list-ref (list-ref rule 2) (+ i 1)))))
                 )
                 
               (if (empty? (list-ref rule 1))
                   (void)
                   (set-IFA-Σ! tmp (list (list-ref rule 1))))
               (for ((tmpkeys (hash-keys (IFA-subst tmp))))
                 (if (hash-has-key? (hash-ref (IFA-subst tmp) tmpkeys) (original-id tmpkeys))
                     (set! tmp (modify-IFA tmp tmpkeys (hash-ref (hash-ref (IFA-subst tmp) tmpkeys) (original-id tmpkeys))))
                     (void)))
               tmp
                ))])))

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
(define (merge-IFA old-IFA old_term new_term)
  (let ([tmpQ (IFA-Q old-IFA)]
        [tmpΣ (IFA-Σ old-IFA)] (tmpδ (IFA-δ old-IFA))
        (tmps (IFA-s old-IFA)) (tmpF (IFA-F old-IFA))
        (tmpsubst (hash-copy (IFA-subst old-IFA))) (tmpalias (hash-copy (IFA-alias old-IFA))))
    (let ((subIFA (build-IFA (list 1 (list) new_term))))
      (begin
        (set! tmpQ (append tmpQ (IFA-Q subIFA)))
        (while (not (equal? (check-duplicates tmpQ) #f))
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
                                                  ali-term
                                                  tmpnew_term)
                                      )
                                (set! tmplength (+ tmplength 1))
                                (hash-set! tmpalias dup_term (append (hash-ref tmpalias dup_term) (list tmpnew_term)))
                                ))))
                      (let ((copyalias (hash-copy (IFA-alias subIFA))))
                        (begin
                          (hash-remove! copyalias dup_term)
                          (set-IFA-alias! subIFA copyalias))
                        )
                      )
                    (void))
                (set! tmplength (if (hash-has-key? tmpalias (check-duplicates tmpQ)) (length (hash-ref tmpalias (check-duplicates tmpQ))) 0))
                (let ((tmpnew_term (string->symbol (string-append (symbol->string dup_term) "_a" (number->string tmplength)))))
                  (begin
                    (set! subIFA
                          (modify-IFA subIFA
                                      dup_term
                                      tmpnew_term)
                          )
                    (hash-set! tmpalias dup_term (if (hash-has-key? tmpalias dup_term)
                                                     (append (hash-ref tmpalias dup_term) (list tmpnew_term))
                                                     (list tmpnew_term)))
                    (set! tmpQ (list-set tmpQ (last (indexes-of tmpQ dup_term)) tmpnew_term))
                    ))
                ))
            (void))
        (set! tmpQ (remove old_term tmpQ))
        (set! tmpδ (merge-hash old_term old-IFA subIFA))
        (if (member old_term tmps)
            (set! tmps (IFA-s subIFA))
            (void))
        (if (member old_term tmpF)
            (set! tmpF (append (remove old_term tmpF) (IFA-F subIFA)))
            (void))
        ;hygienic subst
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
        (hash-remove! tmpsubst old_term)
        (hash-union! tmpalias (IFA-alias subIFA))
        (IFA tmpQ tmpΣ tmpδ tmps tmpF tmpsubst tmpalias)
        )
      ))
  )


  
;(build-IFA '(1 (Or e_1 e_2) (let x e_1 (if x x e_2))))

(define (make-context-rule tmppattern tmpnode subst-hash)
  (let ((tmprule (list "context rule" tmppattern tmpnode)))
    (if (string-prefix? (symbol->string tmpnode) "v_subst")
        empty
        tmprule)))
(define (make-reduction-rule tmppattern tmpnode subst-hash)
  (list "reduction rule" tmppattern tmpnode (hash-copy subst-hash)))

(define (original-id name)
  (define (string-index hay needle)
    (define n (string-length needle))
    (define h (string-length hay))
    (and (<= n h) ; if the needle is longer than hay, then the needle can not be found
         (for/or ([i (- h n -1)]
                  #:when (string=? (substring hay i (+ i n)) needle))
           i)))
  (if (string-index (symbol->string name) "_a")
      (string->symbol (substring (symbol->string name) 0 (string-index (symbol->string name) "_a")))
      name))
(define (build-rules the-IFA)
  (let ((rule-list (list))
        (tmpnode-list (IFA-s the-IFA))
        (used-list empty)
        (tmppattern (car (IFA-Σ the-IFA)))
        (pattern (car (IFA-Σ the-IFA)))
        (pattern-hash (make-hash))
        (subst-hash (make-hash))
        )
    (begin (hash-set! pattern-hash (last tmpnode-list) pattern)
           (while (not (empty? tmpnode-list))
                  (if (member (last tmpnode-list) used-list)
                      (void)
                      (begin
                        (if (hash-has-key? (hash-ref (IFA-δ the-IFA) (last tmpnode-list)) 'void)
                            (set! rule-list (append rule-list (if (empty? (make-context-rule tmppattern (last tmpnode-list) subst-hash))
                                                                  empty
                                                                  (list (make-context-rule tmppattern (last tmpnode-list) subst-hash)))
                                                    ))
                            (void))
                        (set! used-list (append used-list (list (last tmpnode-list))))))
                  (let ((flag #f) (tmphash (hash-ref (IFA-δ the-IFA) (last tmpnode-list))))
                    (begin
                      (for ((tmpkey (hash-keys tmphash)))
                        ;(display "1")
                        ;(displayln tmpkey)
                        ;(display "2")
                        ;(displayln tmphash)
                        (if flag
                            (void)
                            (if (or (member (hash-ref tmphash tmpkey) used-list) (equal? tmpkey 'void))
                                (void)
                                (begin
                                  (if (member (original-id (last tmpnode-list)) tmppattern)
                                      (set! tmppattern (list-set tmppattern
                                                                 (index-of tmppattern (original-id (last tmpnode-list)))
                                                                 tmpkey))
                                      (void))
                                  (if (string-prefix? (symbol->string (last tmpnode-list)) "v_subst")
                                      (hash-set! subst-hash (original-id (last tmpnode-list)) tmpkey)
                                      (void))
                                  ;(display "33")
                                  ;(displayln (list (hash-ref tmphash tmpkey)))
                                  (set! tmpnode-list (append tmpnode-list (list (hash-ref tmphash tmpkey))))
                                  (hash-set! pattern-hash (last tmpnode-list) tmppattern)
                                  (set! flag #t)
                                  (if (member (hash-ref tmphash tmpkey) (IFA-F the-IFA))
                                      (begin
                                        (set! rule-list (append rule-list (list (make-reduction-rule tmppattern (last tmpnode-list) subst-hash))))
                                        (set! used-list (append used-list (list (last tmpnode-list))))
                                        (set! tmpnode-list (drop-right tmpnode-list 1))
                                        (if (string-prefix? (symbol->string (last tmpnode-list)) "v_subst")
                                            (hash-remove! subst-hash (original-id (last tmpnode-list)))
                                            (void))
                                        (set! tmppattern (hash-ref pattern-hash (last tmpnode-list)))
                                        )
                                      (void))))))
                      (if flag
                          (void)
                          (begin
                            (set! tmpnode-list (drop-right tmpnode-list 1))
                            (if (empty? tmpnode-list)
                                (void)
                                (begin
                                  (set! tmppattern (hash-ref pattern-hash (last tmpnode-list)))
                                  (if (string-prefix? (symbol->string (last tmpnode-list)) "v_subst")
                                      (hash-remove! subst-hash (original-id (last tmpnode-list)))
                                      (void)))
                                ))))))
           rule-list)
    ))

;(build-IFA '(1 (Or e_1 e_2) (let x e_1 (if x x e_2))))

#;(build-rules (build-IFA '(1 (Or e_1 e_2) (let x e_1 (if x x e_2)))))
;(build-IFA '(1 (Sg e_1 e_2 e_3 e_4 e_5) (if e_1 (if e_2 e_3 e_4) (if e_3 e_4 e_5))))
#;(build-IFA '(1 (Sg e_1 e_2 e_3 e_4 e_5)
                            (let x e_3 (if e_1 (if e_2 x e_4) (if x x e_5)))
                            ))
#;(build-rules (build-IFA '(1 (Sg e_1 e_2 e_3 e_4 e_5)
                            (let x e_3 (if e_1 (if e_2 x e_4) (if x x e_5)))
                            )))
(build-rules (build-IFA '(1 (Sg e_1 e_2 e_3 e_4)
                            (let x e_1 (if x (let x e_2 e_3) e_4))
                            )))