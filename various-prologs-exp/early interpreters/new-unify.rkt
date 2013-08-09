#lang racket

(define (var? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define empty-s '())
(define (ext-s x v s) (cons (cons x v) s))
(define (lhs pr) (car pr))
(define (rhs pr) (cdr pr))

(define (walk u s)
  (cond
    [(not (var? u)) u]
    [(assq u s) => (lambda (pr) (walk (rhs pr) s))]
    [else u]))

(define (occurs-check? x v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) (eq? v x)]
      [(pair? v)
       (or (occurs-check? x (car v) s)
           (occurs-check? x (cdr v) s))]
      [else #f])))

(define (process-equations e s)
  (cond
    [(null? e) s]
    [else
     (let loop ([u (caar e)]
                [v (cdar e)]
                [e (cdr e)])
       (let ([u (walk u s)]
             [v (walk v s)])
         (cond
           [(eq? u v) (process-equations e s)]
           [(var? u)
            (and (not (occurs-check? u v s))
                 (process-equations e (ext-s u v s)))]
           [(var? v)
            (and (not (occurs-check? v u s))
                 (process-equations e (ext-s v u s)))]
           [(and (pair? u) (pair? v))
            (loop (car u)
                  (car v)
                  (cons (cons (cdr u) (cdr v)) e))]
           [(equal? u v)
            (process-equations e s)]
           [else #f])))]))

(define (unify x y s)
  (process-equations (list (cons x y)) s))

