#lang racket

(define (var? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define (unify x x-idx y y-idx subst)
  (cond
    [(eq? subst #f)
     #f]
    [(var? x)
     (unify-variable x x-idx y y-idx subst)]
    [(var? y) (unify-variable y y-idx x x-idx subst)]
    [(and (pair? x) (pair? y))
     (unify (cdr x) x-idx (cdr y) y-idx
                 (unify (car x) x-idx (car y) y-idx subst))]
    [(equal? x y)
     subst]
    [else #f]))

(define (unify-variable var var-idx val val-idx subst)
  (if (and (equal? var val) (= var-idx val-idx))
      subst
      (let ([binding (bound? (cons var var-idx) subst)])
        (if binding
            (unify (cadr binding) (cddr binding) val val-idx subst)
            (let ([binding (and (var? val) (bound? (cons val val-idx) subst))])
              (if binding
                  (unify var var-idx (cadr binding) (cddr binding) subst)
                  (extend-subst (cons var var-idx) (cons val val-idx) subst)))))))

; would need update for structure sharing
;(define (occurs-in? var x subst)
;  (if (equal? var x)
;      #t
;      (let ([binding (bound? x subst)])
;        (if binding
;            (occurs-in? var (cdr binding) subst)
;            (if (pair? x)
;                (or (occurs-in? var (car x) subst)
;                    (occurs-in? var (cdr x) subst))
;                #f)))))

(define bound? assoc)

(define (extend-subst var-mol val-mol subst)
  (cons (cons var-mol val-mol) subst))



