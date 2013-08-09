#lang scheme

(define (var? x) (and (symbol? x)
                      (char=? (string-ref (symbol->string x) 0) #\?)))
(define (bound? x subst) (assoc x subst))
(define (lookup var subst) (cdr (assoc var subst)))
(define (extend-subst var val subst) (cons (cons var val) subst))

(define (occurs-in? var x subst)
  (cond
    [(equal? var x) #t]
    [(bound? x subst)
     (occurs-in? var (lookup x subst))]
    [(pair? x) (or (occurs-in? var (car x) subst)
                   (occurs-in? var (cdr x) subst))]
    [else #f]))

(define (unify-variable var val subst)
  (cond
    [(equal? var val)
     subst]
    [(bound? var subst)
     (unify (lookup var subst) val subst)]
    [(and (var? val) (bound? val subst))
     (unify var (lookup val subst) subst)]
    [(occurs-in? var val subst)
     #f]
    [else
     (extend-subst var val subst)]))

(define (unify x y [subst '()])
  (cond
    [(equal? x y)
     subst]
    [(eq? subst #f)
     #f]
    [(var? x)
     (unify-variable x y subst)]
    [(var? y)
     (unify-variable y x subst)]
    [(and (pair? x) (pair? y))
     (unify (cdr x) (cdr y)
            (unify (car x) (car y) subst))]
    [else
     #f]))

'(unify '(?a 3 ?b) '(1 ?b 3))
'(unify '(?a 3 1) '(?c ?b ?c))





