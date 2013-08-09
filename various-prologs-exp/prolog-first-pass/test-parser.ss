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

(define-for-syntax (varsym? stx)
  (let ([x (syntax-e stx)])
    (and (symbol? x)
         (char=? (string-ref (symbol->string x) 0) #\?))))

(define-for-syntax (walk stx bindings)
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

(define-syntax (transform-vars stx)
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

(define x (transform-vars (goop ?a ?b)))

