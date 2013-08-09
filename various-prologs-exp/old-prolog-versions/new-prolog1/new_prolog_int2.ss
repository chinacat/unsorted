#lang scheme

; log_interp0: beginnings of a Prolog interpreter... based on Norvig's PAIP book.
; log_interp1: switch from "batch" to "incremental" backtracking (part 1)
; log_interp2: add ability to "fail" and retrieve additional solutions

(require (only-in mzlib/compat
                  getprop
                  putprop))

(provide <- ?-)

(define fail '())
(define no-bindings '((#t . #t)))

(define (variable? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define (get-binding var bindings)
  (assq var bindings))

(define (binding-val binding)
  (cdr binding))

(define (lookup var bindings)
  (binding-val (get-binding var bindings)))

(define (extend-bindings var val bindings)
  (cons (cons var val)
        (if (eq? bindings no-bindings)
            '()
            bindings)))

(define *occurs-check* (make-parameter #t))

(define (unify x y [bindings no-bindings])
  (cond
    [(eq? bindings fail) fail]
    [(eq? x y) bindings]
    [(variable? x) (unify-variable x y bindings)]
    [(variable? y) (unify-variable y x bindings)]
    [(and (pair? x) (pair? y))
     (unify (cdr x)
            (cdr y)
            (unify (car x) (car y) bindings))]
    [(equal? x y) bindings]
    [else fail]))

(define (unify-variable var x bindings)
  (cond
    [(get-binding var bindings)
     => (lambda (binding) (unify (binding-val binding) x bindings))]
    [(variable? x)
     (cond
       [(get-binding x bindings)
        => (lambda (binding) (unify var (binding-val binding) bindings))]
       [else (extend-bindings var x bindings)])]
    [(and (*occurs-check*) (occurs-check var x bindings))
     fail]
    [else
     (extend-bindings var x bindings)]))

(define (occurs-check var x bindings)
  (cond
    [(eq? var x) #t]
    [(and (variable? x) (get-binding x bindings))
     => (lambda (binding) (occurs-check var (binding-val binding) bindings))]
    [(pair? x)
     (or (occurs-check var (car x) bindings)
         (occurs-check var (cdr x) bindings))]
    [else #f]))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

(define (subst-bindings bindings x)
  (cond
    [(eq? bindings fail) fail]
    [(eq? bindings no-bindings) x]
    [(and (variable? x) (get-binding x bindings))
     => (lambda (binding) (subst-bindings bindings (binding-val binding)))]
    [(pair? x)
     (reuse-cons (subst-bindings bindings (car x))
                 (subst-bindings bindings (cdr x))
                 x)]
    [else x]))

(define (unifier x y)
  (subst-bindings (unify x y) x))

(define (clause-head clause)
  (car clause))

(define (clause-body clause)
  (cdr clause))

(define (get-clauses pred)
  (getprop pred 'clauses '()))

(define (predicate relation)
  (car relation))

(define *db-predicates* '())

(define (add-clause pred clause)
  (unless (memq pred *db-predicates*)
    (set! *db-predicates* (cons pred *db-predicates*)))
  (putprop pred 'clauses
           (append (get-clauses pred) (list clause)))
  ; pred
  (void))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

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

(define-syntax (parse-clause stx)
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
    [(_ term0 term ...)
     (let*-values ([(new-terms vars) (walk #'(term0 term ...) '())])
       #`(lambda (goal bindings success-cont cut-cont failure-cont)
           (let ([new-clause (exists #,vars
                                     (list #,@(map (lambda (t) #`(transform-term #,t))
                                                   (syntax->list new-terms))))])
             (prove-goals (clause-body new-clause)
                          (unify goal (clause-head new-clause) bindings)
                          success-cont
                          cut-cont
                          failure-cont))))]))

(define-syntax (<- stx)
  (syntax-case stx ()
    [(_ (pred . args) . rest)
     (identifier? #'pred)
     (let ([parsed-clause #'((pred . args) . rest)])
       #`(add-clause 'pred
                     (parse-clause #,@parsed-clause)))]))

(define (clear-db)
  (for-each clear-predicate *db-predicates*))

(define (clear-predicate predicate)
  (putprop predicate 'clauses '()))

(define (mapcan f lst)
  (foldr (lambda (v l) (append (f v) l)) '() lst))

(define (unique-find-anywhere-if predicate tree [found-so-far '()])
  (if (pair? tree)
      (unique-find-anywhere-if predicate
                               (car tree)
                               (unique-find-anywhere-if predicate
                                                        (cdr tree)
                                                        found-so-far))
      (if (predicate tree)
          (if (memq tree found-so-far)
              found-so-far
              (cons tree found-so-far))
          found-so-far)))

(define (variables-in exp)
  (unique-find-anywhere-if variable? exp))

(define (sublis bindings tree)
  (if (pair? tree)
      (reuse-cons (sublis bindings (car tree))
                  (sublis bindings (cdr tree))
                  tree)
      (cond
        [(assq tree bindings)
         => (lambda (binding) (cdr binding))]
        [else tree])))

(define (rename-variables x)
  (sublis (map (lambda (var) (cons var (gensym var)))
               (variables-in x))
          x))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

(define (show-prolog-vars vars bindings success-cont failure-cont)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~a" var (subst-bindings bindings var)))
                vars))
  (if (continue?)
      (failure-cont)
      (success-cont bindings failure-cont)))

; prove-goals : goal-list bindings success-cont failure-cont -> void
(define (prove-goals goal-list bindings success-cont cut-cont failure-cont)
  (cond
    [(eq? bindings fail) (failure-cont)]
    [(null? goal-list)
     (success-cont bindings failure-cont)]
    [(eq? '! (car goal-list))
     (prove-goals (cdr goal-list) bindings success-cont cut-cont cut-cont)]
    [else (search-choices (car goal-list)
                          bindings
                          (lambda (b2 fc2)
                            (prove-goals (cdr goal-list) b2 success-cont cut-cont fc2))
                          failure-cont)]))

(define (prove goal clause bindings success-cont cut-cont failure-cont)
  (let ([new-clause (rename-variables clause)])
    (prove-goals (clause-body new-clause)
                 (unify goal (clause-head new-clause) bindings)
                 success-cont
                 cut-cont
                 failure-cont)))

(define (search-choices goal bindings success-cont failure-cont)
  (let iter ([clauses (get-clauses (predicate goal))])
    (if (null? clauses)
        (failure-cont)
        ((car clauses) goal
                       bindings
                       success-cont
                       failure-cont
                       (lambda () (iter (cdr clauses)))))))

(define (top-level-prove goals)
  (let ([fail (lambda ()
                (printf "~nNo."))])
    (prove-goals goals
                 no-bindings
                 (lambda (bindings failure-cont)
                   (show-prolog-vars (variables-in goals)
                                     bindings
                                     (lambda (bindings failure-cont)
                                       (fail))
                                     failure-cont))
                 fail
                 fail)))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove 'goals)]))



