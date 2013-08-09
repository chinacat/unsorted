#lang scheme

(provide <- ?-)

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

(define-for-syntax (varsym? stx)
  (let ([x (syntax-e stx)])
    (and (symbol? x)
         (char=? (string-ref (symbol->string x) 0) #\?))))

(define-for-syntax (walk stx bindings)
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

(define-syntax (transform-query-vars stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term bindings) (walk #'(term0 term ...) '())])
       #`(let #,(map (lambda (binding)
                       (list (cdr binding)
                             #`(make-variable (quote #,(car binding)) #f)))
                     (reverse bindings))
           #,new-term))]))

(define-syntax (transform-vars stx)
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
      [(and (string? x) (pair? y))
       (unify! (map char->integer (string->list x)) y)]
      [(and (pair? x) (string? y))
       (unify! (map char->integer (string->list y)) x)]
      [else
       #f])))

(define-syntax make-prover
  (syntax-rules ()
    [(_ term0)
     (lambda (goal success-cont cut-cont failure-cont)
       (let ([new-clause (transform-vars term0)])
         (if (unify! goal (clause-head new-clause))
             (success-cont failure-cont)
             (failure-cont))))]
    [(_ term0 term1 term ...)
     (lambda (goal success-cont cut-cont failure-cont)
       (let ([new-clause (transform-vars term0 term1 term ...)])
         (if (unify! goal (clause-head new-clause))
             (prove-goals (clause-body new-clause)
                          success-cont
                          cut-cont
                          failure-cont)
             (failure-cont))))]))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

(define (clause-head clause)
  (car clause))

(define (clause-body clause)
  (cdr clause))

(define (get-clauses pred)
  ;(getprop pred 'clauses '()))
  (hash-ref! *clause-database* pred '()))

(define (predicate relation)
  (car relation))

(define *clause-database* (make-hasheq))

(define *db-predicates* '())

(define (add-primitive pred proc)
  (unless (and (symbol? pred) (not (variable? pred)))
    (error 'add-primitive "invalid predicate name (symbol required), given ~a" pred))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  (unless (memq pred *db-predicates*)
    (set! *db-predicates* (cons pred *db-predicates*)))
  ;(putprop pred 'clauses proc)
  (hash-set! *clause-database* pred proc)
  (void))

(define (add-clause pred clause)
  (unless (and (symbol? pred) (not (variable? pred)))
    (error '<- "invalid predicate name (symbol required), given ~a" pred))
  (unless (memq pred *db-predicates*)
    (set! *db-predicates* (cons pred *db-predicates*)))
  ;(putprop pred 'clauses
  ;         (append (get-clauses pred) (list clause)))
  (let ([existing-clauses (get-clauses pred)])
    (if (procedure? existing-clauses)
        ; allow user to replace a built-in with a user defined predicate
        (hash-set! *clause-database* pred (list clause))
        (hash-set! *clause-database* pred 
                   (append existing-clauses (list clause))))
    (void)))

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
  ;(putprop predicate 'clauses '())
  (hash-set! *clause-database* predicate '()))

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

(define (residualize-variable term)
  (if (variable-n term)
      (string->symbol (string-append (symbol->string (variable-name term))
                                     (number->string (variable-n term))))
      (variable-name term)))

(define (simplify-term term)
  (cond
    [(pair? term)
     (cons (simplify-term (car term)) (simplify-term (cdr term)))]
    [(variable? term)
     (if (bound? term)
         (simplify-term (deref term))
         (residualize-variable term))]
    [else
     term]))

(define (show-prolog-vars vars success-cont failure-cont)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~s" (residualize-variable var) (simplify-term (variable-val var))))
                vars))
  (if (continue?)
      (failure-cont)
      (success-cont failure-cont)))

; prove-goals : goal-list success-cont failure-cont -> void
(define (prove-goals goal-list success-cont cut-cont failure-cont)
  (cond
    [(eq? '! (car goal-list))
     (if (null? (cdr goal-list))
         (success-cont cut-cont)
         (prove-goals (cdr goal-list) success-cont cut-cont cut-cont))]
    [(null? (cdr goal-list))
     (search-choices (car goal-list)
                     success-cont
                     failure-cont)]
    [else (search-choices (car goal-list)
                          (lambda (fc2)
                            (prove-goals (cdr goal-list) success-cont cut-cont fc2))
                          failure-cont)]))

(define (search-choices goal success-cont failure-cont)
  (let ([clauses (get-clauses (predicate goal))])
    (cond
      [(procedure? clauses)
       (clauses (cdr goal) success-cont failure-cont)]
      [(null? clauses)
       (failure-cont)]
      [else
       (let ([old-trail *trail*])
         (let iter ([clauses clauses])
           (if (null? (cdr clauses))
               ((car clauses) goal
                              success-cont
                              failure-cont
                              failure-cont)
               ((car clauses) goal
                              success-cont
                              failure-cont
                              (lambda ()
                                (reset-trail old-trail)
                                (iter (cdr clauses)))))))])))

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
    [(_ goal0 goal ...)
     (top-level-prove (transform-query-vars goal0 goal ...))]))

(add-primitive '=
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '= "incorrect arity, expected two arguments, given ~s" args))
                 (if (unify! (car args) (cadr args))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'member
               (letrec ([mem-proc (lambda (args success-cont failure-cont)
                                    (unless (= 2 (length args))
                                      (error 'member "incorrect arity, expected two arguments, given ~s" args))
                                    (let ([old-trail *trail*]
                                          [?arg1 (car args)]
                                          [?arg2 (cadr args)])
                                      (let ([clause2 (lambda ()
                                                       (reset-trail old-trail)
                                                       (let ([?x (make-variable '?x (new-counter))]
                                                             [?item (make-variable '?item (new-counter))]
                                                             [?rest (make-variable '?rest (new-counter))])
                                                         (if (unify! ?arg1 ?item)
                                                             (if (unify! ?arg2 (cons ?x ?rest))
                                                                 (mem-proc (list ?item ?rest)
                                                                           success-cont
                                                                           failure-cont)
                                                                 (failure-cont))
                                                             (failure-cont))))])
                                        (let ([?item (make-variable '?item (new-counter))]
                                              [?rest (make-variable '?rest (new-counter))])
                                          (if (unify! ?arg1 ?item)
                                              (if (unify! ?arg2 (cons ?item ?rest))
                                                  (success-cont clause2)
                                                  (clause2))
                                              (clause2))))))])
                 mem-proc))

(define (force-arith term)
  (cond
    [(pair? term)
     (let ([op (car term)]
           [args (cdr term)])
       (case op
         [(+) (unless (= 2 (length args))
                (error '+ "incorrect arity, expected two arguments, given ~s" args))
              (+ (force-arith (car args)) (force-arith (cadr args)))]
         [(-) (unless (= 2 (length args))
                (error '- "incorrect arity, expected two arguments, given ~s" args))
              (- (force-arith (car args)) (force-arith (cadr args)))]
         [(*) (unless (= 2 (length args))
                (error '* "incorrect arity, expected two arguments, given ~s" args))
              (* (force-arith (car args)) (force-arith (cadr args)))]
         [(/) (unless (= 2 (length args))
                (error '/ "incorrect arity, expected two arguments, given ~s" args))
              (/ (force-arith (car args)) (force-arith (cadr args)))]
         [(quotient) (unless (= 2 (length args))
                       (error 'quotient "incorrect arity, expected two arguments, given ~s" args))
                     (quotient (force-arith (car args)) (force-arith (cadr args)))]
         [(remainder) (unless (= 2 (length args))
                        (error 'remainder "incorrect arity, expected two arguments, given ~s" args))
                      (remainder (force-arith (car args)) (force-arith (cadr args)))]
         [(max) (unless (= 2 (length args))
                  (error 'max "incorrect arity, expected two arguments, given ~s" args))
                (max (force-arith (car args)) (force-arith (cadr args)))]
         [(min) (unless (= 2 (length args))
                  (error 'min "incorrect arity, expected two arguments, given ~s" args))
                (min (force-arith (car args)) (force-arith (cadr args)))]
         [(abs) (unless (= 1 (length args))
                  (error 'abs "incorrect arity, expected one argument, given ~s" args))
                (abs (force-arith (car args)))]
         [(gcd) (unless (= 2 (length args))
                  (error 'gcd "incorrect arity, expected two arguments, given ~s" args))
                (gcd (force-arith (car args)) (force-arith (cadr args)))]
         [(lcm) (unless (= 2 (length args))
                  (error 'lcm "incorrect arity, expected two arguments, given ~s" args))
                (lcm (force-arith (car args)) (force-arith (cadr args)))]
         [(numerator) (unless (= 1 (length args))
                        (error 'numerator "incorrect arity, expected one argument, given ~s" args))
                      (numerator (force-arith (car args)))]
         [(denominator) (unless (= 1 (length args))
                          (error 'denominator "incorrect arity, expected one argument, given ~s" args))
                        (denominator (force-arith (car args)))]
         [(floor) (unless (= 1 (length args))
                    (error 'floor "incorrect arity, expected one argument, given ~s" args))
                  (floor (force-arith (car args)))]
         [(ceiling) (unless (= 1 (length args))
                      (error 'ceiling "incorrect arity, expected one argument, given ~s" args))
                    (ceiling (force-arith (car args)))]
         [(truncate) (unless (= 1 (length args))
                       (error 'truncate "incorrect arity, expected one argument, given ~s" args))
                     (truncate (force-arith (car args)))]
         [(round) (unless (= 1 (length args))
                    (error 'round "incorrect arity, expected one argument, given ~s" args))
                  (round (force-arith (car args)))]
         [(rationalize) (unless (= 2 (length args))
                          (error 'rationalize "incorrect arity, expected two arguments, given ~s" args))
                        (rationalize (force-arith (car args)) (force-arith (cadr args)))]
         [(exp) (unless (= 1 (length args))
                  (error 'exp "incorrect arity, expected one argument, given ~s" args))
                (exp (force-arith (car args)))]
         [(log) (unless (= 1 (length args))
                  (error 'log "incorrect arity, expected one argument, given ~s" args))
                (log (force-arith (car args)))]
         [(sin) (unless (= 1 (length args))
                  (error 'sin "incorrect arity, expected one argument, given ~s" args))
                (sin (force-arith (car args)))]
         [(cos) (unless (= 1 (length args))
                  (error 'cos "incorrect arity, expected one argument, given ~s" args))
                (cos (force-arith (car args)))]
         [(tan) (unless (= 1 (length args))
                  (error 'tan "incorrect arity, expected one argument, given ~s" args))
                (tan (force-arith (car args)))]
         [(asin) (unless (= 1 (length args))
                   (error 'asin "incorrect arity, expected one argument, given ~s" args))
                 (asin (force-arith (car args)))]
         [(acos) (unless (= 1 (length args))
                   (error 'acos "incorrect arity, expected one argument, given ~s" args))
                 (acos (force-arith (car args)))]
         [(atan) (cond
                   [(= 1 (length args))
                    (atan (force-arith (car args)))]
                   [(= 2 (length args))
                    (atan (force-arith (car args)) (force-arith (cadr args)))]
                   [else
                    (error 'atan "incorrect arity, expected one or two arguments, given ~s" args)])]
         [(sqrt) (unless (= 1 (length args))
                   (error 'sqrt "incorrect arity, expected one argument, given ~s" args))
                 (sqrt (force-arith (car args)))]
         [(expt) (unless (= 2 (length args))
                   (error 'expt "incorrect arity, expected two arguments, given ~s" args))
                 (expt (force-arith (car args)) (force-arith (cadr args)))]
         [(make-rectangular)
          (unless (= 2 (length args))
            (error 'make-rectangular "incorrect arity, expected two arguments, given ~s" args))
          (make-rectangular (force-arith (car args)) (force-arith (cadr args)))]
         [(make-polar) (unless (= 2 (length args))
                         (error 'make-polar "incorrect arity, expected two arguments, given ~s" args))
                       (make-polar (force-arith (car args)) (force-arith (cadr args)))]
         [(real-part) (unless (= 1 (length args))
                        (error 'real-part "incorrect arity, expected one argument, given ~s" args))
                      (real-part (force-arith (car args)))]
         [(imag-part) (unless (= 1 (length args))
                        (error 'imag-part "incorrect arity, expected one argument, given ~s" args))
                      (imag-part (force-arith (car args)))]
         [(magnitude) (unless (= 1 (length args))
                        (error 'magnitude "incorrect arity, expected one argument, given ~s" args))
                      (magnitude (force-arith (car args)))]
         [(angle) (unless (= 1 (length args))
                    (error 'angle "incorrect arity, expected one argument, given ~s" args))
                  (angle (force-arith (car args)))]
         [(exact->inexact) (unless (= 1 (length args))
                             (error 'exact->inexact "incorrect arity, expected one argument, given ~s" args))
                           (exact->inexact (force-arith (car args)))]
         [(inexact->exact) (unless (= 1 (length args))
                             (error 'inexact->exact "incorrect arity, expected one argument, given ~s" args))
                           (inexact->exact (force-arith (car args)))]
         [else (error 'arithmetic-function "expected an arithmetic operator, given ~s" op)]))]
    [(variable? term)
     (if (bound? term)
         (force-arith (deref term))
         (error 'arithmetic-function "arguments insufficiently instantiated, given ~s" term))]
    [(number? term)
     term]
    [else
     (error 'arithmetic-function "type error, given ~s" term)]))

(add-primitive 'is
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error 'is "incorrect arity, expected two arguments, given ~s" args))
                 (if (unify! (car args) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '<
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '< "incorrect arity, expected two arguments, given ~s" args))
                 (if (< (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=<
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '=< "incorrect arity, expected two arguments, given ~s" args))
                 (if (<= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '>
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '> "incorrect arity, expected two arguments, given ~s" args))
                 (if (> (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '>=
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '>= "incorrect arity, expected two arguments, given ~s" args))
                 (if (>= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=:=
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '=:= "incorrect arity, expected two arguments, given ~s" args))
                 (if (= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=/=
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 2 (length args))
                   (error '=/= "incorrect arity, expected two arguments, given ~s" args))
                 (if (not (= (force-arith (car args)) (force-arith (cadr args))))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'integer?
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 1 (length args))
                   (error 'integer? "incorrect arity, expected one argument, given ~s" args))
                 (if (integer? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'number?
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 1 (length args))
                   (error 'number? "incorrect arity, expected one argument, given ~s" args))
                 (if (number? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'not
               (lambda (args success-cont failure-cont)
                 (unless (= 1 (length args))
                   (error 'not "incorrect arity, expected one argument, given ~s" args))
                 (search-choices (car args)
                                 (lambda (fc) failure-cont)
                                 (lambda () (success-cont failure-cont)))))

(add-primitive 'fail
               (lambda (args success-cont failure-cont)
                 (unless (null? args)
                   (error 'fail "incorrect arity, expected zero arguments, given ~s" args))
                 (failure-cont)))

(add-primitive 'true
               (lambda (args success-cont failure-cont)
                 (unless (null? args)
                   (error 'true "incorrect arity, expected zero arguments, given ~s" args))
                 (success-cont failure-cont)))

(add-primitive 'pretty-print
               (lambda (args success-cont failure-cont)
                 ; can be removed once the arity checking is made part of clause indexing
                 (unless (= 1 (length args))
                   (error 'pretty-print "incorrect arity, expected one argument, given ~s" args))
                 (pretty-print (deref (car args)))
                 (success-cont failure-cont)))



