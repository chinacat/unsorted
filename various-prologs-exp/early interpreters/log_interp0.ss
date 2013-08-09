#lang scheme

; log_interp0: beginnings of a Prolog interpreter... based on Norvig's PAIP book.

(require (only-in mzlib/compat
                  getprop
                  putprop))

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

(define (match-variable var input bindings)
  (let ([binding (get-binding var bindings)])
    (cond
      [(not binding) (extend-bindings var input bindings)]
      [(equal? input (binding-val binding)) bindings]
      [else fail])))

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

(define (add-clause clause)
  (let ([pred (predicate (clause-head clause))])
    (unless (and (symbol? pred) (not (variable? pred)))
      (error '<- "invalid predicate name (symbol required), given ~a" pred))
    (unless (memq pred *db-predicates*)
      (set! *db-predicates* (cons pred *db-predicates*)))
    (putprop pred 'clauses
             (append (get-clauses pred) (list clause)))
    pred))

(define-syntax <-
  (syntax-rules ()
    [(_ . clause)
     (add-clause 'clause)]))

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

(define (prove goal bindings)
  (mapcan (lambda (clause)
            (let ([new-clause (rename-variables clause)])
              (prove-all (clause-body new-clause)
                         (unify goal (clause-head new-clause) bindings))))
          (get-clauses (predicate goal))))

(define (prove-all goals bindings)
  (cond
    [(eq? bindings fail)
     fail]
    [(null? goals)
     (list bindings)]
    [else
     (mapcan (lambda (goal1-solution)
               (prove-all (cdr goals) goal1-solution))
             (prove (car goals) bindings))]))

(define (show-prolog-solutions vars solutions)
  (if (null? solutions)
      (printf "~nNo.")
      (for-each (lambda (solution)
                  (show-prolog-vars vars solution))
                solutions)))

(define (show-prolog-vars vars bindings)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~a" var (subst-bindings bindings var)))
                vars))
  (printf ";"))

(define (top-level-prove goals)
  (show-prolog-solutions (variables-in goals)
                         (prove-all goals no-bindings)))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove 'goals)]))

(<- (likes Kim Robin))
(<- (likes Sandy Lee))
(<- (likes Sandy Kim))
(<- (likes Robin cats))
(<- (likes Sandy ?x) (likes ?x cats))
(<- (likes Kim ?x) (likes ?x Lee) (likes ?x Kim))
(<- (likes ?x ?x))

(?- (likes Sandy ?who))
