#lang scheme


(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct predicate (name arity [clauses #:auto])
  #:transparent
  #:mutable
  #:auto-value '())

(define *clause-database* (make-hash))

(define (intern-functor name arity)
  (hash-ref! *clause-database*
             (cons name arity)
             (lambda () (make-predicate name arity))))

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

(define-for-syntax (walk stx functor-bindings var-bindings)
  (syntax-case stx ()
    [()
     (values #'(quote ()) functor-bindings var-bindings)]
    [(functor arg ...)
     (and (identifier? #'functor) (not (varsym? #'functor)))
     (let* ([functor-sym (syntax-e #'functor)]
            [arity (length (syntax->list #'(arg ...)))]
            [functor-key (cons functor-sym arity)])
       (define (parse-args args functor-bindings var-bindings)
         (syntax-case args ()
           [()
            (values #'(quote ()) functor-bindings var-bindings)]
           [(arg . rest)
            (let-values ([(new-arg arg-functor-bindings arg-var-bindings)
                          (walk #'arg functor-bindings var-bindings)])
              (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                            (parse-args #'rest arg-functor-bindings arg-var-bindings)])
                (values #`(cons #,new-arg #,new-rest) rest-functor-bindings rest-var-bindings)))]))
       (let ([binding (assoc functor-key functor-bindings)])
         (if binding
             (let-values ([(new-args arg-functor-bindings arg-var-bindings)
                           (parse-args #'(arg ...) functor-bindings var-bindings)])
               (values #`(cons #,(cdr binding) #,new-args)
                       arg-functor-bindings
                       arg-var-bindings))
             (let ([functor-tmp (car (generate-temporaries #'(functor)))])
               (let-values ([(new-args arg-functor-bindings arg-var-bindings)
                             (parse-args #'(arg ...)
                                         (cons (cons functor-key functor-tmp)
                                               functor-bindings)
                                         var-bindings)])
                 (values #`(cons #,functor-tmp #,new-args)
                         arg-functor-bindings
                         arg-var-bindings))))))]
    [(item0 item ... . tail)
     (let iter ([items #'(item0 item ...)]
                [functor-bindings functor-bindings]
                [var-bindings var-bindings])
       (syntax-case items ()
         [()
          (walk #'tail functor-bindings var-bindings)]
         [(a . rest)
          (let-values ([(new-a a-functor-bindings a-var-bindings)
                        (walk #'a functor-bindings var-bindings)])
            (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                          (iter #'rest a-functor-bindings a-var-bindings)])
              (values #`(cons #,new-a #,new-rest)
                      rest-functor-bindings
                      rest-var-bindings)))]))]
    [var
     (and (identifier? #'var) (varsym? #'var))
     (let ([varsym (syntax-e #'var)])
       (if (eq? '? varsym)
           (values #'(make-variable (gensym '?) (new-counter))
                   functor-bindings
                   var-bindings)
           (let ([binding (assq varsym var-bindings)])
             (if binding
                 (values (cdr binding) functor-bindings var-bindings)
                 (let ([var-tmp (car (generate-temporaries #'(var)))])
                   (values var-tmp
                           functor-bindings
                           (cons (cons varsym var-tmp) var-bindings)))))))]
    [id
     (identifier? #'id)
     (values #'(quote id) functor-bindings var-bindings)]
    [other
     (values #'other functor-bindings var-bindings)]))

(define-syntax (transform-query-vars stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term functor-bindings var-bindings)
                   (walk #'(term0 term ...) '() '())])
       #`(let #,(map (lambda (binding)
                       (list (cdr binding)
                             #`(intern-functor (quote #,(caar binding))
                                               (quote #,(cdar binding)))))
                     (reverse functor-bindings))
           (let #,(map (lambda (binding)
                         (list (cdr binding)
                               #`(make-variable (quote #,(car binding)) #f)))
                       (reverse var-bindings))
             #,new-term)))]))

(define-syntax (make-copier stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term functor-bindings var-bindings)
                   (walk #'(term0 term ...) '() '())])
       #`(let #,(map (lambda (binding)
                       (list (cdr binding)
                             #`(intern-functor (quote #,(caar binding))
                                               (quote #,(cdar binding)))))
                     (reverse functor-bindings))
           (lambda ()
             (let #,(map (lambda (binding)
                           (list (cdr binding)
                                 #`(make-variable (quote #,(car binding)) (new-counter))))
                         (reverse var-bindings))
               #,new-term))))]))

;(define-syntax (transform-vars stx)
;  (syntax-case stx ()
;    [(_ term0 term ...)
;     (let-values ([(new-term functor-bindings var-bindings)
;                   (walk #'(term0 term ...) '() '())])
;       #`(let #,(map (lambda (binding)
;                       (list (cdr binding)
;                             #`(make-variable (quote #,(car binding)) (new-counter))))
;                     (reverse var-bindings))
;           #,new-term))]))






