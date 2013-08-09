#lang racket

(define (variable? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define (constant-term? term)
  (cond
    [(pair? term)
     (and (constant-term? (car term))
          (constant-term? (cdr term)))]
    [(variable? term)
     #f]
    [else
     #t]))

(define (collect-sharing-cps term already-seen refers k)
  (cond
    [(member term already-seen)
     (if (member term refers)
         (k term already-seen refers)
         (k term already-seen (cons term refers)))]
    [(null? term)
     (k term already-seen refers)]
    [(constant-term? term)
     (k term (cons term already-seen) refers)]
    [(pair? term)
     (collect-sharing-cps (car term)
                          already-seen
                          refers
                          (lambda (new-car new-as-car new-r-car)
                            (collect-sharing-cps (cdr term)
                                                 new-as-car
                                                 new-r-car
                                                 (lambda (new-cdr new-as-cdr new-r-cdr)
                                                   (let ([new-term (cons new-car new-cdr)])
                                                     (k new-term
                                                        (cons new-term new-as-cdr)
                                                        new-r-cdr))))))]
    [(eq? term '?)
     (let ([new-term (gensym '?)])
       (k new-term (cons new-term already-seen) refers))]
    [(variable? term)
     (k term (cons term already-seen) refers)]
    [else
     (k term (cons term already-seen) refers)]))


'(collect-sharing-cps '(p ?z (h ?z ?w) (f ?w))
                       '() '()
                       (lambda (new-term new-as new-r)
                         (printf "term=~a~n" new-term)
                         (printf "already-seen=~a~n" new-as)
                         (printf "references=~a~n" new-r)))

; expected result
; references=((?w) ?z)

(struct share (term idx) #:transparent)
(struct share-ref (idx) #:transparent)

(define (idx-in-frame term refers)
  (- (length refers) (length (member term refers))))

(define (annotate-cps term already-seen refers k)
  (cond
    [(member term refers)
     (if (member term already-seen)
         (k (share-ref (idx-in-frame term refers)) already-seen refers)
         (k (share term (idx-in-frame term refers))
            (cons term already-seen) refers))]
    [(pair? term)
     (annotate-cps (car term)
                   already-seen
                   refers
                   (lambda (new-car new-as-car new-r-car)
                     (annotate-cps (cdr term)
                                   new-as-car
                                   new-r-car
                                   (lambda (new-cdr new-as-cdr new-r-cdr)
                                     (let ([new-term (cons new-car new-cdr)])
                                       (k new-term
                                          (cons new-term new-as-cdr)
                                          new-r-cdr))))))]
    [else
     (if (member term already-seen)
         (k term already-seen refers)
         (k term (cons term already-seen) refers))]))

(define (preprocess term)
  (collect-sharing-cps term
                       '()
                       '()
                       (lambda (new-term new-as new-r)
                         (annotate-cps new-term '() new-r
                                       (lambda (annotated-term new-as2 new-r2)
                                         (values annotated-term
                                                 (length new-r2)))))))

'(preprocess '(p ?z (h ?z ?w) (f ?w)))

(define (copy-term template frame)
  (cond
    [(share? template)
     (let ([new-term (copy-term (share-term template) frame)])
       (vector-set! frame (share-idx template) new-term)
       new-term)]
    [(share-ref? template)
     (vector-ref frame (share-ref-idx template))]
    [(pair? template)
     (cons (copy-term (car template) frame) (copy-term (cdr template) frame))]
    [(variable? template)
     (gensym template)]
    [else
     template]))



;; the code is still buggy and/or bad design
;;;;; see this test case:
; (preprocess '(p (q ?z ?z) (q ?z ?z)))
; (copy-term (list 'p (share '(q ?z ?z) 0) (share-ref 0)) (make-vector 2))
; ==> '(p (q ?z11187 ?z11188) (q ?z11187 ?z11188))






