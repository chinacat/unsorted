#lang racket

(define-syntax exists
  (syntax-rules ()
    [(_ (var ...) exp0 exp ...)
     (let ([var (gensym 'var)] ...)
       exp0 exp ...)]))

(define-for-syntax (variable? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define-syntax (transform-term stx)
  (define (walk stx)
    (syntax-case stx ()
      [(a . b)
       #`(#,(walk #'a) . #,(walk #'b))]
      [id
       (and (identifier? #'id) (variable? (syntax-e #'id)))
       #'(unquote id)]
      [any
       #'any]))
  (syntax-case stx ()
    [(_ goal)
     #`(quasiquote #,(walk #'goal))]))

(define-syntax (process-clause stx)
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
       (and (identifier? #'id) (variable? (syntax-e #'id)))
       (if (already-seen? #'id vars)
           (values #'id vars)
           (values #'id (cons #'id vars)))]
      [any
       (values #'any vars)]))
  (syntax-case stx ()
    [(_ (term0 term ...))
     (let*-values ([(new-terms vars) (walk #'(term0 term ...) '())])
       #`(exists #,vars
                 (list #,@(map (lambda (t) #`(transform-term #,t)) (syntax->list new-terms)))))]))

'(process-clause ((foo ?a ?b)))
'(process-clause ((foo ?a ?b) (bar ?a ?c) (ask ?b ?c)))
