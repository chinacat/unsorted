#lang scheme

(provide <- ?-)

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name n [val #:auto])
  ;#:transparent
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

(define-struct predicate (name arity [clauses #:auto])
  ;#:transparent
  #:mutable
  #:auto-value '())

(define *clause-database* (make-hash))

(define (intern-functor name arity)
  (hash-ref! *clause-database*
             (cons name arity)
             (lambda () (make-predicate name arity))))

(define-for-syntax (walk stx functor-bindings var-bindings)
  (syntax-case stx ()
    [()
     (values #'(quote ()) functor-bindings var-bindings)]
    [(functor arg ...)
     (and (identifier? #'functor) (not (eq? '! (syntax-e #'functor))) (not (varsym? #'functor)))
     (let* ([functor-sym (syntax-e #'functor)]
            [arity (length (syntax->list #'(arg ...)))]
            [functor-key (cons functor-sym arity)])
       (define (parse-args args functor-bindings var-bindings)
         (syntax-case args ()
           [()
            (values #'(quote ()) functor-bindings var-bindings)]
           [(arg . rest)
            (let-values ([(new-arg arg-functor-bindings arg-var-bindings)
                          (walk #'arg functor-bindings var-bindings)])
              (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                            (parse-args #'rest arg-functor-bindings arg-var-bindings)])
                (values #`(cons #,new-arg #,new-rest) rest-functor-bindings rest-var-bindings)))]))
       (let ([binding (assoc functor-key functor-bindings)])
         (if binding
             (let-values ([(new-args arg-functor-bindings arg-var-bindings)
                           (parse-args #'(arg ...) functor-bindings var-bindings)])
               (values #`(cons #,(cdr binding) #,new-args)
                       arg-functor-bindings
                       arg-var-bindings))
             (let ([functor-tmp (car (generate-temporaries #'(functor)))])
               (let-values ([(new-args arg-functor-bindings arg-var-bindings)
                             (parse-args #'(arg ...)
                                         (cons (cons functor-key functor-tmp)
                                               functor-bindings)
                                         var-bindings)])
                 (values #`(cons #,functor-tmp #,new-args)
                         arg-functor-bindings
                         arg-var-bindings))))))]
    [(item0 item ... . tail)
     (let iter ([items #'(item0 item ...)]
                [functor-bindings functor-bindings]
                [var-bindings var-bindings])
       (syntax-case items ()
         [()
          (walk #'tail functor-bindings var-bindings)]
         [(a . rest)
          (let-values ([(new-a a-functor-bindings a-var-bindings)
                        (walk #'a functor-bindings var-bindings)])
            (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                          (iter #'rest a-functor-bindings a-var-bindings)])
              (values #`(cons #,new-a #,new-rest)
                      rest-functor-bindings
                      rest-var-bindings)))]))]
    [var
     (and (identifier? #'var) (varsym? #'var))
     (let ([varsym (syntax-e #'var)])
       (if (eq? '? varsym)
           (values #'(make-variable (gensym '?) (new-counter))
                   functor-bindings
                   var-bindings)
           (let ([binding (assq varsym var-bindings)])
             (if binding
                 (values (cdr binding) functor-bindings var-bindings)
                 (let ([var-tmp (car (generate-temporaries #'(var)))])
                   (values var-tmp
                           functor-bindings
                           (cons (cons varsym var-tmp) var-bindings)))))))]
    [id
     (identifier? #'id)
     (values #'(quote id) functor-bindings var-bindings)]
    [other
     (values #'other functor-bindings var-bindings)]))

(define-for-syntax (walk-seq seq functor-bindings var-bindings)
  (syntax-case seq ()
    [()
     (values #'(quote ()) functor-bindings var-bindings)]
    [(item . rest)
     (let-values ([(new-item item-functor-bindings item-var-bindings)
                   (walk #'item functor-bindings var-bindings)])
       (let-values ([(new-rest rest-functor-bindings rest-var-bindings)
                     (walk-seq #'rest item-functor-bindings item-var-bindings)])
         (values #`(cons #,new-item #,new-rest) rest-functor-bindings rest-var-bindings)))]))

(define-syntax (transform-query-vars stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term functor-bindings var-bindings)
                   (walk #'(term0 term ...) '() '())])
       #`(let #,(map (lambda (binding)
                       (list (cdr binding)
                             #`(intern-functor (quote #,(caar binding))
                                               (quote #,(cdar binding)))))
                     (reverse functor-bindings))
           (let #,(map (lambda (binding)
                         (list (cdr binding)
                               #`(make-variable (quote #,(car binding)) #f)))
                       (reverse var-bindings))
             #,new-term)))]))

(define-syntax ?-
  (syntax-rules ()
    [(_ goal0 goal ...)
     (top-level-prove (transform-query-vars goal0 goal ...))]))

;(define-for-syntax (walk-wrapper seq functor-bindings var-bindings)
;  (walk seq functor-bindings var-bindings))

(define-for-syntax (compile-fact stx)
  (let*-values ([(functor arity args)
                 (syntax-case stx ()
                   [(f arg ...)
                    (values #'f (length (syntax->list #'(arg ...))) #'(arg ...))])]
                [(new-args functor-bindings var-bindings)
                 (walk-seq args '() '())])
    (if (= 0 arity)
        #`(add-clause '#,functor #,arity
                      (lambda (goal success-cont cut-tag)
                        (success-cont)))
        #`(let #,(map (lambda (binding)
                        (list (cdr binding)
                              #`(intern-functor (quote #,(caar binding))
                                                (quote #,(cdar binding)))))
                      (reverse functor-bindings))
            (add-clause '#,functor #,arity
                        (lambda (goal success-cont cut-tag)
                          (let #,(map (lambda (binding)
                                        (list (cdr binding)
                                              #`(make-variable (quote #,(car binding))
                                                               (new-counter))))
                                      (reverse var-bindings))
                            (if (unify! (cdr goal) #,new-args)
                                (success-cont)
                                (void)))))))))

(define-for-syntax (compile-rule head body)
  (let*-values ([(new-body body-functor-bindings body-var-bindings)
                 (walk body '() '())]
                [(functor arity args)
                 (syntax-case head ()
                   [(f arg ...)
                    (values #'f (length (syntax->list #'(arg ...))) #'(arg ...))])]
                [(new-args args-functor-bindings args-var-bindings)
                 (walk-seq args body-functor-bindings body-var-bindings)])
    (if (= 0 arity)
        #`(let #,(map (lambda (binding)
                        (list (cdr binding)
                              #`(intern-functor (quote #,(caar binding))
                                                (quote #,(cdar binding)))))
                      (reverse args-functor-bindings))
            (add-clause '#,functor #,arity
                        (lambda (goal success-cont cut-tag)
                          (let #,(map (lambda (binding)
                                        (list (cdr binding)
                                              #`(make-variable (quote #,(car binding))
                                                               (new-counter))))
                                      (reverse args-var-bindings))
                            (prove-goals #,new-body success-cont cut-tag)))))
        #`(let #,(map (lambda (binding)
                        (list (cdr binding)
                              #`(intern-functor (quote #,(caar binding))
                                                (quote #,(cdar binding)))))
                      (reverse args-functor-bindings))
            (add-clause '#,functor #,arity
                        (lambda (goal success-cont cut-tag)
                          (let #,(map (lambda (binding)
                                        (list (cdr binding)
                                              #`(make-variable (quote #,(car binding))
                                                               (new-counter))))
                                      (reverse args-var-bindings))
                            (if (unify! (cdr goal) #,new-args)
                                (prove-goals #,new-body success-cont cut-tag)
                                (void)))))))))

(define-syntax (<- stx)
  (syntax-case stx ()
    [(_ term0)
     (compile-fact #'term0)]
    [(_ term0 term1 term ...)
     (compile-rule #'term0 #'(term1 term ...))]))

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

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

(define (clause-head clause)
  (car clause))

(define (clause-body clause)
  (cdr clause))

;(define (get-clauses pred)
;  ;(getprop pred 'clauses '()))
;  (hash-ref! *clause-database* pred '()))

(define (functor term)
  (car term))

; (define *db-predicates* '())

(define (add-primitive functor arity proc)
  (unless (symbol? functor)
    (error 'add-primitive "invalid predicate name (symbol required), given ~a" functor))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  ;(unless (memq pred *db-predicates*)
  ;  (set! *db-predicates* (cons pred *db-predicates*)))
  ;(putprop pred 'clauses proc)
  (let ([pred (intern-functor functor arity)])
    (set-predicate-clauses! pred proc))
  (void))

(define (add-clause functor arity clause)
  (unless (symbol? functor)
    (error '<- "invalid predicate name (symbol required), given ~a" functor))
  ;(unless (memq pred *db-predicates*)
  ;  (set! *db-predicates* (cons pred *db-predicates*)))
  ;(putprop pred 'clauses
  ;         (append (get-clauses pred) (list clause)))
  (let ([pred (intern-functor functor arity)])
    (let ([existing-clauses (predicate-clauses pred)])
      (if (procedure? existing-clauses)
          ; allow user to replace a built-in with a user defined predicate
          (set-predicate-clauses! pred (list clause))
          (set-predicate-clauses! pred (append existing-clauses (list clause))))))
  (void))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

;(define (clear-db)
;  (for-each clear-predicate *db-predicates*))

;(define (clear-predicate predicate)
;  ;(putprop predicate 'clauses '())
;  (hash-set! *clause-database* predicate '()))

;(define (mapcan f lst)
;  (foldr (lambda (v l) (append (f v) l)) '() lst))

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
    [(predicate? term)
     (predicate-name term)]
    [(variable? term)
     (if (bound? term)
         (simplify-term (deref term))
         (residualize-variable term))]
    [else
     term]))

(define (show-prolog-vars vars success-cont)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~s" (residualize-variable var) (simplify-term (variable-val var))))
                vars))
  (if (continue?)
      (void)
      (success-cont)))

; prove-goals : goal-list success-cont cut-tag -> void
(define (prove-goals goal-list success-cont cut-tag)
  (cond
    [(eq? '! (car goal-list))
     (if (null? (cdr goal-list))
         (begin (success-cont)
                (abort-current-continuation cut-tag))
         (prove-goals/cut (cdr goal-list) success-cont cut-tag))]
    [(null? (cdr goal-list))
     (search-choices (car goal-list) success-cont)]
    [else (search-choices (car goal-list)
                          (lambda ()
                            (prove-goals (cdr goal-list) success-cont cut-tag)))]))

; prove-goals : goal-list success-cont cut-tag -> void
(define (prove-goals/cut goal-list success-cont cut-tag)
  (cond
    [(eq? '! (car goal-list))
     (if (null? (cdr goal-list))
         (begin (success-cont)
                (abort-current-continuation cut-tag))
         (begin (prove-goals/cut (cdr goal-list) success-cont cut-tag)
                (abort-current-continuation cut-tag)))]
    [(null? (cdr goal-list))
     (search-choices (car goal-list) success-cont)
     (abort-current-continuation cut-tag)]
    [else (search-choices (car goal-list)
                          (lambda ()
                            (prove-goals/cut (cdr goal-list) success-cont cut-tag)))
          (abort-current-continuation cut-tag)]))

(define (search-choices goal success-cont)
  (let ([cut-tag (make-continuation-prompt-tag)])
    (call-with-continuation-prompt
     (lambda ()
       (let ([clauses (predicate-clauses (functor goal))])
         (cond
           [(procedure? clauses)
            (clauses (cdr goal) success-cont)]
           [(null? clauses)
            ; irrespective of how failure is implemented, this should probably raise an error!
            (void)]
           [else
            (let ([old-trail *trail*])
              (let iter ([clauses clauses])
                (if (null? (cdr clauses))
                    ((car clauses) goal success-cont cut-tag)
                    (begin ((car clauses) goal success-cont cut-tag)
                           (reset-trail old-trail)
                           (iter (cdr clauses))))))])))
     cut-tag
     (lambda () (void)))))

(define (top-level-prove goals)
  (let ([fail (lambda ()
                (reset-trail '())
                (printf "~nNo."))]
        [var-list (variables-in goals)])
    (let ([cut-tag (make-continuation-prompt-tag)])
      (call-with-continuation-prompt
       (lambda ()
         (prove-goals goals
                      (lambda ()
                        (show-prolog-vars var-list
                                          (lambda ()
                                            (abort-current-continuation cut-tag))))
                      cut-tag))
       cut-tag
       (lambda () (fail))))))

(add-primitive '= 2
               (lambda (args success-cont)
                 (if (unify! (car args) (cadr args))
                     (success-cont)
                     (void))))

(add-primitive 'member 2
               (letrec ([mem-proc (lambda (args success-cont)
                                    (let ([old-trail *trail*]
                                          [?arg1 (car args)]
                                          [?arg2 (cadr args)])
                                      (let ([?item (make-variable '?item (new-counter))]
                                            [?rest (make-variable '?rest (new-counter))])
                                        (if (unify! ?arg1 ?item)
                                            (if (unify! ?arg2 (cons ?item ?rest))
                                                (success-cont)
                                                (void))
                                            (void)))
                                      (reset-trail old-trail)
                                      (let ([?x (make-variable '?x (new-counter))]
                                            [?item (make-variable '?item (new-counter))]
                                            [?rest (make-variable '?rest (new-counter))])
                                        (if (unify! ?arg1 ?item)
                                            (if (unify! ?arg2 (cons ?x ?rest))
                                                (mem-proc (list ?item ?rest) success-cont)
                                                (void))
                                            (void)))))])
                 mem-proc))

;(define (force-arith term)
;  (cond
;    [(pair? term)
;     (let ([op (predicate-name (car term))]
;           [args (cdr term)])
;       (case op
;         [(+) (unless (= 2 (length args))
;                (error '+ "incorrect arity, expected two arguments, given ~s" args))
;              (+ (force-arith (car args)) (force-arith (cadr args)))]
;         [(-) (unless (= 2 (length args))
;                (error '- "incorrect arity, expected two arguments, given ~s" args))
;              (- (force-arith (car args)) (force-arith (cadr args)))]
;         [(*) (unless (= 2 (length args))
;                (error '* "incorrect arity, expected two arguments, given ~s" args))
;              (* (force-arith (car args)) (force-arith (cadr args)))]
;         [(/) (unless (= 2 (length args))
;                (error '/ "incorrect arity, expected two arguments, given ~s" args))
;              (/ (force-arith (car args)) (force-arith (cadr args)))]
;         [(quotient) (unless (= 2 (length args))
;                       (error 'quotient "incorrect arity, expected two arguments, given ~s" args))
;                     (quotient (force-arith (car args)) (force-arith (cadr args)))]
;         [(remainder) (unless (= 2 (length args))
;                        (error 'remainder "incorrect arity, expected two arguments, given ~s" args))
;                      (remainder (force-arith (car args)) (force-arith (cadr args)))]
;         [(max) (unless (= 2 (length args))
;                  (error 'max "incorrect arity, expected two arguments, given ~s" args))
;                (max (force-arith (car args)) (force-arith (cadr args)))]
;         [(min) (unless (= 2 (length args))
;                  (error 'min "incorrect arity, expected two arguments, given ~s" args))
;                (min (force-arith (car args)) (force-arith (cadr args)))]
;         [(abs) (unless (= 1 (length args))
;                  (error 'abs "incorrect arity, expected one argument, given ~s" args))
;                (abs (force-arith (car args)))]
;         [(gcd) (unless (= 2 (length args))
;                  (error 'gcd "incorrect arity, expected two arguments, given ~s" args))
;                (gcd (force-arith (car args)) (force-arith (cadr args)))]
;         [(lcm) (unless (= 2 (length args))
;                  (error 'lcm "incorrect arity, expected two arguments, given ~s" args))
;                (lcm (force-arith (car args)) (force-arith (cadr args)))]
;         [(numerator) (unless (= 1 (length args))
;                        (error 'numerator "incorrect arity, expected one argument, given ~s" args))
;                      (numerator (force-arith (car args)))]
;         [(denominator) (unless (= 1 (length args))
;                          (error 'denominator "incorrect arity, expected one argument, given ~s" args))
;                        (denominator (force-arith (car args)))]
;         [(floor) (unless (= 1 (length args))
;                    (error 'floor "incorrect arity, expected one argument, given ~s" args))
;                  (floor (force-arith (car args)))]
;         [(ceiling) (unless (= 1 (length args))
;                      (error 'ceiling "incorrect arity, expected one argument, given ~s" args))
;                    (ceiling (force-arith (car args)))]
;         [(truncate) (unless (= 1 (length args))
;                       (error 'truncate "incorrect arity, expected one argument, given ~s" args))
;                     (truncate (force-arith (car args)))]
;         [(round) (unless (= 1 (length args))
;                    (error 'round "incorrect arity, expected one argument, given ~s" args))
;                  (round (force-arith (car args)))]
;         [(rationalize) (unless (= 2 (length args))
;                          (error 'rationalize "incorrect arity, expected two arguments, given ~s" args))
;                        (rationalize (force-arith (car args)) (force-arith (cadr args)))]
;         [(exp) (unless (= 1 (length args))
;                  (error 'exp "incorrect arity, expected one argument, given ~s" args))
;                (exp (force-arith (car args)))]
;         [(log) (unless (= 1 (length args))
;                  (error 'log "incorrect arity, expected one argument, given ~s" args))
;                (log (force-arith (car args)))]
;         [(sin) (unless (= 1 (length args))
;                  (error 'sin "incorrect arity, expected one argument, given ~s" args))
;                (sin (force-arith (car args)))]
;         [(cos) (unless (= 1 (length args))
;                  (error 'cos "incorrect arity, expected one argument, given ~s" args))
;                (cos (force-arith (car args)))]
;         [(tan) (unless (= 1 (length args))
;                  (error 'tan "incorrect arity, expected one argument, given ~s" args))
;                (tan (force-arith (car args)))]
;         [(asin) (unless (= 1 (length args))
;                   (error 'asin "incorrect arity, expected one argument, given ~s" args))
;                 (asin (force-arith (car args)))]
;         [(acos) (unless (= 1 (length args))
;                   (error 'acos "incorrect arity, expected one argument, given ~s" args))
;                 (acos (force-arith (car args)))]
;         [(atan) (cond
;                   [(= 1 (length args))
;                    (atan (force-arith (car args)))]
;                   [(= 2 (length args))
;                    (atan (force-arith (car args)) (force-arith (cadr args)))]
;                   [else
;                    (error 'atan "incorrect arity, expected one or two arguments, given ~s" args)])]
;         [(sqrt) (unless (= 1 (length args))
;                   (error 'sqrt "incorrect arity, expected one argument, given ~s" args))
;                 (sqrt (force-arith (car args)))]
;         [(expt) (unless (= 2 (length args))
;                   (error 'expt "incorrect arity, expected two arguments, given ~s" args))
;                 (expt (force-arith (car args)) (force-arith (cadr args)))]
;         [(make-rectangular)
;          (unless (= 2 (length args))
;            (error 'make-rectangular "incorrect arity, expected two arguments, given ~s" args))
;          (make-rectangular (force-arith (car args)) (force-arith (cadr args)))]
;         [(make-polar) (unless (= 2 (length args))
;                         (error 'make-polar "incorrect arity, expected two arguments, given ~s" args))
;                       (make-polar (force-arith (car args)) (force-arith (cadr args)))]
;         [(real-part) (unless (= 1 (length args))
;                        (error 'real-part "incorrect arity, expected one argument, given ~s" args))
;                      (real-part (force-arith (car args)))]
;         [(imag-part) (unless (= 1 (length args))
;                        (error 'imag-part "incorrect arity, expected one argument, given ~s" args))
;                      (imag-part (force-arith (car args)))]
;         [(magnitude) (unless (= 1 (length args))
;                        (error 'magnitude "incorrect arity, expected one argument, given ~s" args))
;                      (magnitude (force-arith (car args)))]
;         [(angle) (unless (= 1 (length args))
;                    (error 'angle "incorrect arity, expected one argument, given ~s" args))
;                  (angle (force-arith (car args)))]
;         [(exact->inexact) (unless (= 1 (length args))
;                             (error 'exact->inexact "incorrect arity, expected one argument, given ~s" args))
;                           (exact->inexact (force-arith (car args)))]
;         [(inexact->exact) (unless (= 1 (length args))
;                             (error 'inexact->exact "incorrect arity, expected one argument, given ~s" args))
;                           (inexact->exact (force-arith (car args)))]
;         [else (error 'arithmetic-function "expected an arithmetic operator, given ~s" op)]))]
;    [(variable? term)
;     (if (bound? term)
;         (force-arith (deref term))
;         (error 'arithmetic-function "arguments insufficiently instantiated, given ~s" term))]
;    [(number? term)
;     term]
;    [else
;     (error 'arithmetic-function "type error, given ~s" term)]))
;
;(add-primitive 'is 2
;               (lambda (args success-cont failure-cont)
;                 (if (unify! (car args) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '< 2
;               (lambda (args success-cont failure-cont)
;                 (if (< (force-arith (car args)) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '=< 2
;               (lambda (args success-cont failure-cont)
;                 (if (<= (force-arith (car args)) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '> 2
;               (lambda (args success-cont failure-cont)
;                 (if (> (force-arith (car args)) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '>= 2
;               (lambda (args success-cont failure-cont)
;                 (if (>= (force-arith (car args)) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '=:= 2
;               (lambda (args success-cont failure-cont)
;                 (if (= (force-arith (car args)) (force-arith (cadr args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive '=/= 2
;               (lambda (args success-cont failure-cont)
;                 (if (not (= (force-arith (car args)) (force-arith (cadr args))))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive 'integer? 1
;               (lambda (args success-cont failure-cont)
;                 (if (integer? (deref (car args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive 'number? 1
;               (lambda (args success-cont failure-cont)
;                 (if (number? (deref (car args)))
;                     (success-cont failure-cont)
;                     (failure-cont))))
;
;(add-primitive 'not 1
;               (lambda (args success-cont failure-cont)
;                 (search-choices (car args)
;                                 (lambda (fc) failure-cont)
;                                 (lambda () (success-cont failure-cont)))))
;
;(add-primitive 'fail 0
;               (lambda (args success-cont failure-cont)
;                 (failure-cont)))
;
;(add-primitive 'true 0
;               (lambda (args success-cont failure-cont)
;                 (success-cont failure-cont)))
;
;(add-primitive 'pretty-print 1
;               (lambda (args success-cont failure-cont)
;                 (pretty-print (deref (car args)))
;                 (success-cont failure-cont)))



