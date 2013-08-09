#lang racket

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

(define variable-counter 0)
(define (new-variable name)
  (let ([id variable-counter])
    (set! variable-counter (+ 1 variable-counter))
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

(define-syntax (parse-term stx)
  (define (already-seen? id vars)
    (if (null? vars)
        #f
        (if (eq? (syntax-e id) (syntax-e (car vars)))
            #t
            (already-seen? id (cdr vars)))))
  (define (walk stx vars)
    (syntax-case stx ()
      [(a . b)
       (let-values ([(new-a a-vars) (walk #'a vars)])
         (let-values ([(new-b b-vars) (walk #'b a-vars)])
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
  (syntax-case stx ()
    [(_ term)
     (let-values ([(new-term vars) (walk #'term '())])
       (with-syntax ([(functor arg ...) new-term])
         (with-syntax ([(param ...) (generate-temporaries #'(arg ...))])
           (let* ([name (syntax-e #'functor)]
                  [arity (length (syntax->list #'(arg ...)))]
                  [predname (string->symbol (string-append (symbol->string name)
                                                           "/"
                                                           (number->string arity)))])
             #`(begin
                 (hash-set! *database*
                            '#,predname
                            (lambda (param ...)
                              (exists #,vars
                                      (and (unify! param (transform-term arg)) ...))))
                 (void))))))]))

(define-syntax <-
  (syntax-rules ()
    [(_ term)
     (parse-term term)]))

(define-syntax (parse-query-term stx)
  (define (already-seen? id vars)
    (if (null? vars)
        #f
        (if (eq? (syntax-e id) (syntax-e (car vars)))
            #t
            (already-seen? id (cdr vars)))))
  (define (walk stx vars)
    (syntax-case stx ()
      [(a . b)
       (let-values ([(new-a a-vars) (walk #'a vars)])
         (let-values ([(new-b b-vars) (walk #'b a-vars)])
           (values #`(#,new-a . #,new-b) b-vars)))]
      [id
       (and (identifier? #'id) (eq? '? (syntax-e #'id)))
       (let ([new-id #'(unquote (new-variable #f))])
         (values new-id vars))]
      [id
       (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
       (if (already-seen? #'id vars)
           (values #'(unquote id) vars)
           (values #'(unquote id) (cons #'id vars)))]
      [any
       (values #'any vars)]))
  (syntax-case stx ()
    [(_ term0 term ...)
     (let*-values ([(new-terms vars) (walk #'(term0 term ...) '())])
       #`(prepare-query-goals #,vars (quasiquote #,new-terms)))]))

(define-syntax prepare-query-goals
  (syntax-rules ()
    [(_ predname (var ...) (arg ...))
     (let ([var (make-variable 'var #f *unbound*)] ...)
       ((hash-ref *database* 'predname) `arg ...))]))

(define-syntax (parse-query-goal stx)
  (define (already-seen? id vars)
    (if (null? vars)
        #f
        (if (eq? (syntax-e id) (syntax-e (car vars)))
            #t
            (already-seen? id (cdr vars)))))
  (define (walk stx vars)
    (syntax-case stx ()
      [(a . b)
       (let-values ([(new-a a-vars) (walk #'a vars)])
         (let-values ([(new-b b-vars) (walk #'b a-vars)])
           (values #`(#,new-a . #,new-b) b-vars)))]
      [id
       (and (identifier? #'id) (eq? '? (syntax-e #'id)))
       (let ([new-id #'(unquote (new-variable #f))])
         (values new-id vars))]
      [id
       (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
       (if (already-seen? #'id vars)
           (values #'(unquote id) vars)
           (values #'(unquote id) (cons #'id vars)))]
      [any
       (values #'any vars)]))
  (syntax-case stx ()
    [(_ predname (arg ...))
     (let*-values ([(new-args vars) (walk #'(arg ...) '())])
       #`(prepare-query-goals predname #,vars #,new-args))]))

(define-syntax (?- stx)
  (syntax-case stx ()
    [(_ (functor arg ...))
     (let* ([name (syntax-e #'functor)]
            [arity (length (syntax->list #'(arg ...)))]
            [predname (string->symbol (string-append (symbol->string name)
                                                           "/"
                                                           (number->string arity)))])
       #`(parse-query-goal #,predname (arg ...)))]))

'(<- (foo 1))
'(?- (foo ?z))


