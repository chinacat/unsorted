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

;(define (var? x) (and (symbol? x)
;                      (char=? (string-ref (symbol->string x) 0) #\?)))
(define var? variable?)
;(define (bound? x subst) (assoc x subst))
;(define (lookup var subst) (cdr (assoc var subst)))
;(define (extend-subst var val subst) (cons (cons var val) subst))

(define (bound? x) (not (eq? *unbound* (variable-val x))))

;(define (unify-variable var val)
;  (cond
;    [(equal? var val)
;     #t]
;    [(bound? var)
;     (unify! (variable-val var) val)]
;    [(and (var? val) (bound? val))
;     (unify! var (variable-val val))]
;    [else
;     (set! *trail* (cons var *trail*))
;     (set-variable-val! var val)]))

;(define (unify! x y)
;  (cond
;    [(equal? x y)
;     #t]
;    [(var? x)
;     (unify-variable x y)]
;    [(var? y)
;     (unify-variable y x)]
;    [(and (pair? x) (pair? y))
;     (and (unify! (car x) (car y)) (unify! (cdr x) (cdr y)))]
;    [else
;     #f]))

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
      [(var? x)
       (set-binding! x y)]
      [(var? y)
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
             (failure-cont))))]))

;(define fail '())
;(define no-bindings '((#t . #t)))
;
;;(define (variable? x)
;;  (and (symbol? x)
;;       (char=? (string-ref (symbol->string x) 0) #\?)))
;
;(define (get-binding var bindings)
;  (assq var bindings))
;
;(define (binding-val binding)
;  (cdr binding))
;
;(define (lookup var bindings)
;  (binding-val (get-binding var bindings)))
;
;(define (extend-bindings var val bindings)
;  (cons (cons var val)
;        (if (eq? bindings no-bindings)
;            '()
;            bindings)))
;
;(define *occurs-check* (make-parameter #t))
;
;(define (unify x y [bindings no-bindings])
;  (cond
;    [(eq? bindings fail) fail]
;    [(eq? x y) bindings]
;    [(variable? x) (unify-variable x y bindings)]
;    [(variable? y) (unify-variable y x bindings)]
;    [(and (pair? x) (pair? y))
;     (unify (cdr x)
;            (cdr y)
;            (unify (car x) (car y) bindings))]
;    [(equal? x y) bindings]
;    [else fail]))
;
;(define (unify-variable var x bindings)
;  (cond
;    [(get-binding var bindings)
;     => (lambda (binding) (unify (binding-val binding) x bindings))]
;    [(variable? x)
;     (cond
;       [(get-binding x bindings)
;        => (lambda (binding) (unify var (binding-val binding) bindings))]
;       [else (extend-bindings var x bindings)])]
;    [(and (*occurs-check*) (occurs-check var x bindings))
;     fail]
;    [else
;     (extend-bindings var x bindings)]))
;
;(define (occurs-check var x bindings)
;  (cond
;    [(eq? var x) #t]
;    [(and (variable? x) (get-binding x bindings))
;     => (lambda (binding) (occurs-check var (binding-val binding) bindings))]
;    [(pair? x)
;     (or (occurs-check var (car x) bindings)
;         (occurs-check var (cdr x) bindings))]
;    [else #f]))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

;(define (subst-bindings bindings x)
;  (cond
;    [(eq? bindings fail) fail]
;    [(eq? bindings no-bindings) x]
;    [(and (variable? x) (get-binding x bindings))
;     => (lambda (binding) (subst-bindings bindings (binding-val binding)))]
;    [(pair? x)
;     (reuse-cons (subst-bindings bindings (car x))
;                 (subst-bindings bindings (cdr x))
;                 x)]
;    [else x]))
;
;(define (unifier x y)
;  (subst-bindings (unify x y) x))

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

(define-syntax <-
  (syntax-rules ()
    [(_ goal0 goal ...)
     (add-clause (predicate 'goal0) (make-prover goal0 goal ...))]))

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
      (failure-cont)
      (success-cont failure-cont)))

; prove-goals : goal-list success-cont failure-cont -> void
(define (prove-goals goal-list success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (prove-goals (cdr goal-list) success-cont cut-cont cut-cont)]
    [(null? (cdr goal-list))
     (search-choices (car goal-list)
                     success-cont
                     failure-cont)]
    [else (search-choices (car goal-list)
                          (lambda (fc2)
                            (prove-goals (cdr goal-list) success-cont cut-cont fc2))
                          failure-cont)]))

;(define (prove goal clause bindings success-cont cut-cont failure-cont)
;  ;(let ([new-clause (rename-variables clause)])
;  (let ([new-clause (clause)])
;    (prove-goals (clause-body new-clause)
;                 (unify goal (clause-head new-clause) bindings)
;                 success-cont
;                 cut-cont
;                 failure-cont)))

;(define (search-choices goal bindings success-cont failure-cont)
;  (let iter ([clauses (get-clauses (predicate goal))])
;    (cond
;      [(null? clauses)
;       (failure-cont)]
;      [(null? (cdr clauses))
;       (prove goal
;              (car clauses)
;              bindings
;              success-cont
;              failure-cont
;              failure-cont)]
;      [else
;       (prove goal
;              (car clauses)
;              bindings
;              success-cont
;              failure-cont
;              (lambda () (iter (cdr clauses))))])))

(define (search-choices goal success-cont failure-cont)
  (let ([old-trail *trail*])
    (let iter ([clauses (get-clauses (predicate goal))])
      (cond
        [(null? clauses)
         (failure-cont)]
        [(null? (cdr clauses))
         ((car clauses) goal
                        success-cont
                        failure-cont
                        failure-cont)]
        [else
         ((car clauses) goal
                        success-cont
                        failure-cont
                        (lambda ()
                          (reset-trail old-trail)
                          (iter (cdr clauses))))]))))

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



