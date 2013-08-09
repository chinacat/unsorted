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
       (walk #'b (walk #'a vars))]
      [id
       (and (identifier? #'id) (variable? (syntax-e #'id)))
       (if (already-seen? #'id vars)
           vars
           (cons #'id vars))]
      [any
       vars]))
  (syntax-case stx ()
    [(_ (term0 term ...))
     (let ([vars (walk #'(term0 term ...) '())])
       #`(exists #,vars
                 (transform-term term0)
                 (transform-term term) ...))]))

'(process-clause ((foo ?a ?b)))

