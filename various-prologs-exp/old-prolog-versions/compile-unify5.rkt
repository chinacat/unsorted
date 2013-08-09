#lang racket

(provide <- ?-)

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

(define-syntax (compile-clause stx)
  (define (compute-params args)
    (if (null? args)
        '()
        (cons (car (generate-temporaries (list (car args))))
              (compute-params (cdr args)))))
  (syntax-case stx ()
    [(_ head body)
     (let*-values ([(new-head vars0) (walk-term #'head '())]
                   [(new-goals vars) (compute-goals (syntax->list #'body) '() vars0)])
       (with-syntax ([(functor arg ...) new-head])
         (with-syntax ([(param ...) (compute-params (syntax->list #'(arg ...)))]
                       [(ng ...) new-goals])
           (let* ([name (syntax-e #'functor)]
                  [arity (length (syntax->list #'(arg ...)))]
                  [predname (string->symbol (string-append (symbol->string name)
                                                           "/"
                                                           (number->string arity)))])
             #`(begin
                 (hash-set! *database*
                            '#,predname
                            (append (hash-ref *database* '#,predname '())
                                    (list (lambda (sk cutk fk param ...)
                                            (exists #,vars
                                                    (if (and (unify! param (transform-term arg)) ...)
                                                        (execute-goals sk
                                                                       cutk
                                                                       fk
                                                                       (list (transform-term ng) ...))
                                                        (fk)))))))
                 (void))))))]))

(define-syntax <-
  (syntax-rules ()
    [(_ head g ...)
     (compile-clause head (g ...))]))

(define (execute-goals sk cutk fk goals)
  (cond
    [(null? goals)
     (sk fk)]
    [(eq? '! (car goals))
     (execute-goals sk cutk cutk (cdr goals))]
    [else
     (let ([goal (car goals)])
       (apply dispatch
              (car goal)
              (lambda (fk2)
                (execute-goals sk cutk fk2 (cdr goals)))
              fk
              (cdr goal)))]))

(define (dispatch functor sk fk . args)
  (let ([old-trail *trail*])
    (let iter ([clauses (hash-ref *database* functor)])
      (if (null? clauses)
          (fk)
          (apply (car clauses)
                 sk
                 fk
                 (lambda ()
                   (reset-trail old-trail)
                   (iter (cdr clauses)))
                 args)))))

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

