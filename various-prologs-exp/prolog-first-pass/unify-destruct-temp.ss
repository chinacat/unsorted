#lang scheme

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name n [val #:auto])
  #:transparent
  #:mutable
  #:auto-value *unbound*)

(define new-counter
  (let ([counter 0])
    (lambda ()
      (let ([result counter])
        (set! counter (+ counter 1))
        result))))

(define-syntax (transform-vars stx)
  (define (varsym? stx)
    (let ([x (syntax-e stx)])
      (and (symbol? x)
           (char=? (string-ref (symbol->string x) 0) #\?))))
  (define (walk stx bindings)
    (syntax-case stx ()
      [()
       (values #'(quote ()) bindings)]
      [(a . b)
       (let-values ([(lft lft-bindings) (walk #'a bindings)])
         (let-values ([(rgt rgt-bindings) (walk #'b lft-bindings)])
           (values #`(cons #,lft #,rgt) rgt-bindings)))]
      [var
       (and (identifier? #'var) (varsym? #'var))
       (let ([varsym (syntax-e #'var)])
         (if (eq? '? varsym)
             (values #'(make-variable (gensym '?) (new-counter)) bindings)
             (let ([binding (assq varsym bindings)])
               (if binding
                   (values (cdr binding) bindings)
                   (let ([var-tmp (car (generate-temporaries #'(var)))])
                     (values var-tmp (cons (cons varsym var-tmp) bindings)))))))]
      [id
       (identifier? #'id)
       (values #'(quote id) bindings)]
      [other
       (values #'other bindings)]))
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term bindings) (walk #'(term0 term ...) '())])
       #`(let #,(map (lambda (binding)
                       (list (cdr binding)
                             #`(make-variable (quote #,(car binding)) (new-counter))))
                     (reverse bindings))
           #,new-term))]))

(define-syntax make-copier
  (syntax-rules ()
    [(_ term0 term ...)
     (lambda () (transform-vars term0 term ...))]))

;(define (var? x) (and (symbol? x)
;                      (char=? (string-ref (symbol->string x) 0) #\?)))
(define var? variable?)
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





