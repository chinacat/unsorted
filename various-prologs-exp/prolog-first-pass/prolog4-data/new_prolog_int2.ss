#lang scheme

(require (only-in mzlib/compat
                  getprop
                  putprop))

(provide <- ?-)

(define fail #f)

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name n [val #:auto])
  #:transparent
  #:mutable
  #:auto-value *unbound*)

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
      [else
       #f])))

(define-syntax make-prover
  (syntax-rules ()
    [(_ term0 term ...)
     (lambda (goal success-cont cut-cont failure-cont)
       (let ([new-clause (transform-vars term0 term ...)])
         (if (unify! goal (clause-head new-clause))
             (prove-goals (clause-body new-clause)
                          success-cont
                          cut-cont
                          failure-cont)
             (invoke/failure failure-cont))))]))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

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
  (unless (and (symbol? pred) (not (variable? pred)))
    (error '<- "invalid predicate name (symbol required), given ~a" pred))
  (unless (memq pred *db-predicates*)
    (set! *db-predicates* (cons pred *db-predicates*)))
  (putprop pred 'clauses
           (append (get-clauses pred) (list clause)))
  (void))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

(define-syntax <-
  (syntax-rules ()
    [(_ goal0 goal ...)
     (add-clause (predicate 'goal0) (make-prover goal0 goal ...))]))

(define (clear-db)
  (for-each clear-predicate *db-predicates*))

(define (clear-predicate predicate)
  (putprop predicate 'clauses '()))

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

(define (simplify-term term)
  (cond
    [(pair? term)
     (cons (simplify-term (car term)) (simplify-term (cdr term)))]
    [(variable? term)
     (if (bound? term)
         (simplify-term (deref term))
         (variable-name term))]
    [else
     term]))

(define (show-prolog-vars vars success-cont failure-cont)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~a" (variable-name var) (simplify-term (variable-val var))))
                vars))
  (if (continue?)
      (invoke/failure failure-cont)
      (invoke/success success-cont failure-cont)))

(define (invoke/success success-cont failure-cont)
  (cond
    [(procedure? success-cont)
     (success-cont failure-cont)]
    [(prove-goals-success-cont? success-cont)
     (prove-goals (prove-goals-success-cont-other-goals success-cont)
                  (prove-goals-success-cont-success-cont success-cont)
                  (prove-goals-success-cont-cut-cont success-cont)
                  failure-cont)]
    [else (error 'invoke/success "unknown continuation type, given ~s" success-cont)]))

(define (invoke/failure failure-cont)
  (cond
    [(procedure? failure-cont)
     (failure-cont)]
    [(search-choices-failure-cont? failure-cont)
     (reset-trail (search-choices-failure-cont-old-trail failure-cont))
     (process-choices (search-choices-failure-cont-goal failure-cont)
                      (search-choices-failure-cont-other-clauses failure-cont)
                      (search-choices-failure-cont-old-trail failure-cont)
                      (search-choices-failure-cont-success-cont failure-cont)
                      (search-choices-failure-cont-cut-cont failure-cont)
                      (search-choices-failure-cont-failure-cont failure-cont))]
    [else (error 'invoke/failure "unknown continuation type, given ~s" failure-cont)]))

; prove-goals : goal-list success-cont failure-cont -> void

(define-struct prove-goals-success-cont (other-goals success-cont cut-cont))

(define (prove-goals goal-list success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (invoke/success success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (prove-goals (cdr goal-list) success-cont cut-cont cut-cont)]
    [(null? (cdr goal-list))
     (search-choices (car goal-list)
                     success-cont
                     failure-cont)]
    [else (search-choices (car goal-list)
                          (make-prove-goals-success-cont (cdr goal-list) success-cont cut-cont)
                          failure-cont)]))

(define-struct search-choices-failure-cont (goal other-clauses old-trail success-cont cut-cont failure-cont))

(define (process-choices goal clauses old-trail success-cont cut-cont failure-cont)
  (cond
    [(null? clauses)
     (invoke/failure failure-cont)]
    [(null? (cdr clauses))
     ((car clauses) goal
                    success-cont
                    cut-cont
                    failure-cont)]
    [else
     ((car clauses) goal
                    success-cont
                    cut-cont
                    (make-search-choices-failure-cont goal
                                                      (cdr clauses)
                                                      old-trail
                                                      success-cont
                                                      cut-cont
                                                      failure-cont))]))

(define (search-choices goal success-cont failure-cont)
  (let ([old-trail *trail*])
    (process-choices goal
                     (get-clauses (predicate goal))
                     old-trail
                     success-cont
                     failure-cont
                     failure-cont)))

(define (top-level-prove goals)
  (let ([fail (lambda ()
                (reset-trail '())
                (printf "~nNo."))])
    (prove-goals goals
                 (lambda (failure-cont)
                   (show-prolog-vars (variables-in goals)
                                     (lambda (failure-cont)
                                       (fail))
                                     failure-cont))
                 fail
                 fail)))

(define-syntax ?-
  (syntax-rules ()
    [(_ goal ...)
     (top-level-prove (transform-vars goal ...))]))



