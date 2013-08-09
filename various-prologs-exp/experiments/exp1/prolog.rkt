#lang racket

(provide <- ?- benchmark)

; To do:
; [8/22/2012]
; 1. [DONE] Update ?- to support multiple goals
; 2. [DONE] Add support of cut
; 3. Add support of built-in predicates
; 4. 'Improve' compilation of head matching / unification
; 5. Add primitives

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name id val) #:transparent #:mutable)

(define *trail* '())

(define (reset-trail old)
  (cond
    [(null? *trail*)
     (void)]
    [(eq? *trail* old)
     (void)]
    [else (set-variable-val! (car *trail*) *unbound*)
          (set! *trail* (cdr *trail*))
          (reset-trail old)]))

(define (bound? x) (not (eq? *unbound* (variable-val x))))

(define (deref exp)
  (if (and (variable? exp) (bound? exp))
      (deref (variable-val exp))
      exp))

(define (set-binding! var val)
  (unless (eq? var val)
    (set! *trail* (cons var *trail*))
    (set-variable-val! var val))
  #t)

(define (unify! x y)
  (let ([x (deref x)]
        [y (deref y)])
    (cond
      [(equal? x y)
       #t]
      [(variable? x)
       (set-binding! x y)]
      [(variable? y)
       (set-binding! y x)]
      [(and (pair? x) (pair? y))
       (and (unify! (car x) (car y)) (unify! (cdr x) (cdr y)))]
      [(and (string? x) (pair? y))
       (unify! (map char->integer (string->list x)) y)]
      [(and (pair? x) (string? y))
       (unify! (map char->integer (string->list y)) x)]
      [else
       #f])))

(define *variable-counter* 0)
(define (new-variable name)
  (let ([id *variable-counter*])
    (set! *variable-counter* (+ 1 *variable-counter*))
    (make-variable name id *unbound*)))

(define *database* (make-hasheq))

(define-syntax exists
  (syntax-rules ()
    [(_ (var ...) exp0 exp ...)
     (let ([var (new-variable 'var)] ...)
       exp0 exp ...)]))

(define-for-syntax (variable-symbol? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define-syntax (transform-term stx)
  (define (walk stx)
    (syntax-case stx ()
      [(a . b)
       #`(#,(walk #'a) . #,(walk #'b))]
      [id
       (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
       #'(unquote id)]
      [any
       #'any]))
  (syntax-case stx ()
    [(_ goal)
     #`(quasiquote #,(walk #'goal))]))

(define-for-syntax (already-seen? id vars)
  (if (null? vars)
      #f
      (if (eq? (syntax-e id) (syntax-e (car vars)))
          #t
          (already-seen? id (cdr vars)))))

(define-for-syntax (walk-term stx vars)
  (syntax-case stx ()
    [(a . b)
     (let-values ([(new-a a-vars) (walk-term #'a vars)])
       (let-values ([(new-b b-vars) (walk-term #'b a-vars)])
         (values #`(#,new-a . #,new-b) b-vars)))]
    [id
     (and (identifier? #'id) (eq? '? (syntax-e #'id)))
     (let ([new-id (car (generate-temporaries #'(id)))])
       (values new-id (cons new-id vars)))]
    [id
     (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
     (if (already-seen? #'id vars)
         (values #'id vars)
         (values #'id (cons #'id vars)))]
    [any
     (values #'any vars)]))

(define-for-syntax (compute-goal goal vars)
  (let-values ([(new-goal new-vars) (walk-term goal vars)])
    (syntax-case new-goal ()
      [(functor arg ...)
       (let* ([name (syntax-e #'functor)]
              [arity (length (syntax->list #'(arg ...)))]
              [predname (string->symbol (string-append (symbol->string name)
                                                       "/"
                                                       (number->string arity)))])
         (values #`(#,predname arg ...) new-vars))]
      [id
       (and (identifier? #'id) (eq? '! (syntax-e #'id)))
       (values #'id new-vars)])))

(define-for-syntax (compute-goals in-goals acc-goals vars)
  (if (null? in-goals)
      (values (reverse acc-goals) vars)
      (let-values ([(new-goal new-vars) (compute-goal (car in-goals) vars)])
        (compute-goals (cdr in-goals)
                       (cons new-goal acc-goals)
                       new-vars))))

; compute-head-match:
; IN: params, terms
; OUT: var-filter-list, bindings, tests
(define-for-syntax (compute-head-match params terms)
  (define (iter params terms filter-list acc-bindings acc-tests)
    (cond
      [(null? params)
       (values filter-list (reverse acc-bindings) (reverse acc-tests))]
      [(and (identifier? (car terms)) (variable-symbol? (syntax-e (car terms))))
       (if (already-seen? (car terms) filter-list)
           (iter (cdr params)
                 (cdr terms)
                 filter-list
                 acc-bindings
                 (cons #`(unify! #,(car params) #,(car terms))
                       acc-tests))
           (iter (cdr params)
                 (cdr terms)
                 (cons (car terms) filter-list)
                 (cons #`(#,(car terms) #,(car params))
                       acc-bindings)
                 acc-tests))]
      [else
       (iter (cdr params)
             (cdr terms)
             filter-list
             acc-bindings
             (cons #`(unify! #,(car params) (transform-term #,(car terms)))
                   acc-tests))]))
  (iter params terms '() '() '()))

(define-for-syntax (filter-var-list filter-list vars)
  (let loop ([vars vars])
    (cond
      [(null? vars)
       '()]
      [(already-seen? (car vars) filter-list)
       (loop (cdr vars))]
      [else
       (cons (car vars) (loop (cdr vars)))])))

(define-syntax (compile-clause stx)
  (define (compute-params args)
    (if (null? args)
        '()
        (cons (car (generate-temporaries (list (car args))))
              (compute-params (cdr args)))))
  (syntax-case stx ()
    [(_ head)
     (let*-values ([(new-head vars) (walk-term #'head '())])
       (with-syntax ([(functor arg ...) new-head])
         (let*-values ([(new-args) (syntax->list #'(arg ...))]
                       [(new-params) (compute-params new-args)]
                       [(filter-list bindings tests) (compute-head-match new-params new-args)])
           (with-syntax ([(param ...) new-params])
             (let* ([name (syntax-e #'functor)]
                    [arity (length (syntax->list #'(arg ...)))]
                    [predname (string->symbol (string-append (symbol->string name)
                                                             "/"
                                                             (number->string arity)))])
               #`(begin
                   (add-clause '#,predname
                               (lambda (sk cutk fk param ...)
                                 (let #,bindings
                                   (exists #,(filter-var-list filter-list vars)
                                           (if (and . #,tests)
                                               (sk fk)
                                               (fk))))))
                   (void)))))))]
    [(_ head body)
     (let*-values ([(new-head vars0) (walk-term #'head '())]
                   [(new-goals vars) (compute-goals (syntax->list #'body) '() vars0)])
       (with-syntax ([(functor arg ...) new-head])
         (let*-values ([(new-args) (syntax->list #'(arg ...))]
                       [(new-params) (compute-params new-args)]
                       [(filter-list bindings tests) (compute-head-match new-params new-args)])
           (with-syntax ([(param ...) new-params]
                         [(ng ...) new-goals])
             (let* ([name (syntax-e #'functor)]
                    [arity (length (syntax->list #'(arg ...)))]
                    [predname (string->symbol (string-append (symbol->string name)
                                                             "/"
                                                             (number->string arity)))])
               #`(begin
                   (add-clause '#,predname
                               (lambda (sk cutk fk param ...)
                                 (let #,bindings
                                   (exists #,(filter-var-list filter-list vars)
                                           (if (and . #,tests)
                                               (execute-goals sk
                                                              cutk
                                                              fk
                                                              (list (transform-term ng) ...))
                                               (fk))))))
                   (void)))))))]))

(define (add-clause functor compiled-clause)
  (let ([existing-clauses (hash-ref *database* functor '())])
    (if (procedure? existing-clauses)
        (hash-set! *database* functor (list compiled-clause))
        (hash-set! *database* functor (append existing-clauses (list compiled-clause))))))

(define (compute-functor-name name arity)
  (string->symbol (string-append (symbol->string name)
                                 "/"
                                 (number->string arity))))

(define (add-primitive functor arity proc)
  (unless (symbol? functor)
    (error '<- "invalid predicate name (symbol required), given ~a" functor))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  (hash-set! *database* (compute-functor-name functor arity) proc))

(define-syntax <-
  (syntax-rules ()
    [(_ head g ...)
     (compile-clause head (g ...))]))

(define (execute-goals sk cutk fk goals)
  (cond
    [(null? goals)
     (set! count-null-goals (+ count-null-goals 1))
     (sk fk)]
    [(null? (cdr goals))
     (let ([goal (car goals)])
       (if (eq? '! goal)
           (sk cutk)
           (dispatch (car goal)
                     sk
                     fk
                     (cdr goal))))]
    [(eq? '! (car goals))
     (execute-goals sk cutk cutk (cdr goals))]
    [else
     (let ([goal (car goals)])
       (dispatch (car goal)
                 (begin (set! count-sk (+ count-sk 1))
                        (lambda (fk2)
                          (execute-goals sk cutk fk2 (cdr goals))))
                 fk
                 (cdr goal)))]))

(define (dispatch functor sk fk args)
  (let ([old-trail *trail*])
    (let ([clauses (hash-ref *database* functor
                             (lambda () (error "predicate not defined, given" functor)))])
      (cond
        [(procedure? clauses)
         (apply clauses sk fk args)]
        [(null? (cdr clauses))
         (apply (car clauses)
                sk
                fk
                fk
                args)]
        [else
         (let iter ([clauses clauses])
           (cond
             ;[(null? clauses)
             ; (fk)]
             [(null? (cdr clauses))
              (apply (car clauses)
                     sk
                     fk
                     fk
                     args)]
             [else
              (apply (car clauses)
                     sk
                     fk
                     (begin (set! count-fk (+ count-fk 1))
                            (lambda ()
                              (reset-trail old-trail)
                              (iter (cdr clauses))))
                     args)]))]))))

(define (residualize-var var)
  (if (variable-id var)
      (string->symbol (format "~a_~a" (variable-name var) (variable-id var)))
      (variable-name var)))

(define (simplify-term term)
  (cond
    [(pair? term)
     (cons (simplify-term (car term)) (simplify-term (cdr term)))]
    [(variable? term)
     (if (bound? term)
         (simplify-term (deref term))
         (residualize-var term))]
    [else
     term]))

(define (show-prolog-vars vars)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (if (eq? '? (variable-name var))
                      (void)
                      (printf "~n~a = ~a" (residualize-var var) (simplify-term (variable-val var)))))
                vars)))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

(define-syntax (?- stx)
  (syntax-case stx ()
    [(_ g ...)
     (let-values ([(ngs nvs) (compute-goals (syntax->list #'(g ...)) '() '())])
       (with-syntax ([(ng ...) ngs]
                     [(var ...) (reverse nvs)])
         #`(let/ec exit
             (let ([fail (lambda ()
                           (reset-trail '())
                           (printf "~nNo.")
                           (exit))]
                   [var (make-variable 'var #f *unbound*)] ...)
               (execute-goals (lambda (fk)
                                (show-prolog-vars (list var ...))
                                (cond
                                  [(eq? fail fk)
                                   (reset-trail '())
                                   (exit)]
                                  [(continue?) (fk)]
                                  [else (fail)]))
                              fail
                              fail
                              (list (transform-term ng) ...))))))]))

(define (always-continue) #t)

(define count-sk 0)
(define count-fk 0)
(define count-null-goals 0)

(define (reset-counts)
  (set! count-sk 0)
  (set! count-fk 0)
  (set! count-null-goals 0))

(define-syntax (benchmark stx)
  (syntax-case stx ()
    [(_ g ...)
     (let-values ([(ngs nvs) (compute-goals (syntax->list #'(g ...)) '() '())])
       (with-syntax ([(ng ...) ngs]
                     [(var ...) (reverse nvs)])
         #`(begin (reset-counts)
                  (time (let/ec exit
                          (let ([fail (lambda ()
                                        (reset-trail '())
                                        (printf "~nNo.")
                                        (exit))]
                                [var (make-variable 'var #f *unbound*)] ...)
                            (execute-goals (lambda (fk)
                                             (show-prolog-vars (list var ...))
                                             (cond
                                               [(eq? fail fk)
                                                (reset-trail '())
                                                (exit)]
                                               [(always-continue) (fk)]
                                               [else (fail)]))
                                           fail
                                           fail
                                           (list (transform-term ng) ...)))))
                  (printf "# of sk: ~a; # of fk: ~a~n" count-sk count-fk)
                  (printf "# of hits on empty goal-list test: ~a~n" count-null-goals))))]))



