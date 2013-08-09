#lang racket

(define (test a b)
  (cond
    [(and (pair? a) (pair? b))
     (and (test (car a) (car b))
          (test (cdr a) (cdr b)))]
    [(and (symbol? a) (symbol? b))
     (eq? a b)]
    ; non-interned constants
    [else
     (equal? a b)]))

(define (make-test b)
  (cond
    [(pair? b)
     (let ([car-tester (make-test (car b))]
           [cdr-tester (make-test (cdr b))])
       (lambda (a)
         (and (pair? a)
              (car-tester (car a))
              (cdr-tester (cdr a)))))]
    [(symbol? b)
     (lambda (a)
       (and (symbol? a)
            (eq? a b)))]
    [else
     (lambda (a)
       (equal? a b))]))



