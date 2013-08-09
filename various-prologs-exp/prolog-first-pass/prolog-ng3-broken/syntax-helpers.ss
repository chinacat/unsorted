#lang scheme

(provide (all-defined-out))

(define (varsym? stx)
  (let ([x (syntax-e stx)])
    (and (symbol? x)
         (char=? (string-ref (symbol->string x) 0) #\?))))

(define (walk stx functor-bindings var-bindings)
  (syntax-case stx ()
    [()
     (values #'(quote ()) functor-bindings var-bindings)]
    [(functor arg ...)
     (and (identifier? #'functor) (not (eq? '! (syntax-e #'functor))) (not (varsym? #'functor)))
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

(define (walk-seq seq functor-bindings var-bindings)
  (syntax-case seq ()
    [()
     (values #'(quote ()) functor-bindings var-bindings)]
    [(item . rest)
     (let-values ([(new-item item-functor-bindings item-var-bindings)
                   (walk #'item functor-bindings var-bindings)])
       (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                     (walk-seq #'rest item-functor-bindings item-var-bindings)])
         (values #`(cons #,new-item #,new-rest) rest-functor-bindings rest-var-bindings)))]))

;(define (compile-unification arity goal args functor-bindings var-bindings)
(define (compile-unification arity args functor-bindings var-bindings)
  (case arity
    [(1)
     (syntax-case args ()
       [(arg)
        (let-values ([(new-arg arg-functor-bindings arg-var-bindings)
                      (walk #'arg functor-bindings var-bindings)])
          (values #`(unify! (cadr goal) #,new-arg)
                  arg-functor-bindings
                  arg-var-bindings))])]
    [(2)
     (syntax-case args ()
       [(arg0 arg1)
        (let*-values ([(new-arg0 arg0-functor-bindings arg0-var-bindings)
                       (walk #'arg0 functor-bindings var-bindings)]
                      [(new-arg1 arg1-functor-bindings arg1-var-bindings)
                       (walk #'arg1 arg0-functor-bindings arg0-var-bindings)])
          (values #`(let ([arg-list (cdr goal)])
                      (and (unify! (car arg-list) #,new-arg0)
                           (unify! (cadr arg-list) #,new-arg1)))
                  arg1-functor-bindings
                  arg1-var-bindings))])]
    [(3)
     (syntax-case args ()
       [(arg0 arg1 arg2)
        (let*-values ([(new-arg0 arg0-functor-bindings arg0-var-bindings)
                       (walk #'arg0 functor-bindings var-bindings)]
                      [(new-arg1 arg1-functor-bindings arg1-var-bindings)
                       (walk #'arg1 arg0-functor-bindings arg0-var-bindings)]
                      [(new-arg2 arg2-functor-bindings arg2-var-bindings)
                       (walk #'arg2 arg1-functor-bindings arg1-var-bindings)])
          (values #`(let ([arg-list (cdr goal)])
                      (and (unify! (car arg-list) #,new-arg0)
                           (unify! (cadr arg-list) #,new-arg1)
                           (unify! (caddr arg-list) #,new-arg2)))
                  arg2-functor-bindings
                  arg2-var-bindings))])]
    [else
     (let-values ([(new-args args-functor-bindings args-var-bindings)
                   (walk-seq args functor-bindings var-bindings)])
       (values #`(unify! (cdr goal) #,new-args)
               args-functor-bindings
               args-var-bindings))]))

(define (compile-fact stx)
  (let-values ([(functor arity args)
                (syntax-case stx ()
                  [(f arg ...)
                   (values #'f (length (syntax->list #'(arg ...))) #'(arg ...))])])
    (if (= 0 arity)
        #`(add-clause '#,functor #,arity
                      (lambda (goal success-cont cut-cont failure-cont)
                        (success-cont failure-cont)))
        (let-values ([(new-unify-test functor-bindings var-bindings)
;                      (compile-unification arity #'goal args '() '())])
                      (compile-unification arity args '() '())])
          #`(let #,(map (lambda (binding)
                          (list (cdr binding)
                                #`(intern-functor (quote #,(caar binding))
                                                  (quote #,(cdar binding)))))
                        (reverse functor-bindings))
              (add-clause '#,functor #,arity
                          (lambda (goal success-cont cut-cont failure-cont)
                            (let #,(map (lambda (binding)
                                          (list (cdr binding)
                                                #`(make-variable (quote #,(car binding))
                                                                 (new-counter))))
                                        (reverse var-bindings))
                              (if #,new-unify-test
                                  (success-cont failure-cont)
                                  (failure-cont))))))))))

(define (compile-rule head body)
  (let*-values ([(new-body body-functor-bindings body-var-bindings)
                 (walk body '() '())]
                [(functor arity args)
                 (syntax-case head ()
                   [(f arg ...)
                    (values #'f (length (syntax->list #'(arg ...))) #'(arg ...))])])
    (if (= 0 arity)
        #`(let #,(map (lambda (binding)
                        (list (cdr binding)
                              #`(intern-functor (quote #,(caar binding))
                                                (quote #,(cdar binding)))))
                      (reverse body-functor-bindings))
            (add-clause '#,functor #,arity
                        (lambda (goal success-cont cut-cont failure-cont)
                          (let #,(map (lambda (binding)
                                        (list (cdr binding)
                                              #`(make-variable (quote #,(car binding))
                                                               (new-counter))))
                                      (reverse body-var-bindings))
                            (prove-goals #,new-body
                                         success-cont
                                         cut-cont
                                         failure-cont)))))
        (let-values ([(new-unify-test args-functor-bindings args-var-bindings)
;                      (compile-unification arity #'goal args body-functor-bindings body-var-bindings)])
                      (compile-unification arity args body-functor-bindings body-var-bindings)])
          #`(let #,(map (lambda (binding)
                          (list (cdr binding)
                                #`(intern-functor (quote #,(caar binding))
                                                  (quote #,(cdar binding)))))
                        (reverse args-functor-bindings))
              (add-clause '#,functor #,arity
                          (lambda (goal success-cont cut-cont failure-cont)
                            (let #,(map (lambda (binding)
                                          (list (cdr binding)
                                                #`(make-variable (quote #,(car binding))
                                                                 (new-counter))))
                                        (reverse args-var-bindings))
                              (if #,new-unify-test
                                  (prove-goals #,new-body
                                               success-cont
                                               cut-cont
                                               failure-cont)
                                  (failure-cont))))))))))




