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


