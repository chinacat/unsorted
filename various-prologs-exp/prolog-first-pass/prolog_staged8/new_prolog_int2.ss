#lang scheme

; stage 0: naive, unstaged interpreter
; stage 0a: turn off occurs check; cuts time by about half

(provide <- ?- benchmark add-clause)

(define fail #f)
(define no-bindings '())

(define (var-text? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define (get-binding var bindings)
  (assq var bindings))

(define (binding-val binding)
  (cdr binding))

(define (lookup var bindings)
  (binding-val (get-binding var bindings)))

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name counter [val #:auto])
  #:mutable
  #:auto-value *unbound*)

(define-struct variable-template (index))
(define new-counter
  (let ([counter 0])
    (lambda ()
      (let ([result counter])
        (set! counter (+ counter 1))
        result))))

(define-struct clause (num-vars var-list head body))

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

(define *database* (make-hash))

(define (get-clauses pred arity)
  (hash-ref *database* (cons pred arity) '()))

(define (predicate relation)
  (car relation))

(define (add-primitive functor arity proc)
  (unless (and (symbol? functor) (not (var-text? functor)))
    (error '<- "invalid predicate name (symbol required), given ~a" functor))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  (hash-set! *database* (cons functor arity) proc)
  (void))

(define (add-clause new-clause)
  (let ([clause (preprocess-clause (replace-?-variables new-clause))])
    (let ([pred (predicate (clause-head clause))]
          [arity (length (cdr (clause-head clause)))])
      (unless (and (symbol? pred) (not (var-text? pred)))
        (error '<- "invalid predicate name (symbol required), given ~a" pred))
      (let ([existing-clauses (get-clauses pred arity)])
        (if (procedure? existing-clauses)
            ; allow user to replace a built-in with a user defined predicate
            (hash-set! *database* (cons pred arity) (list clause))
            (hash-set! *database* (cons pred arity) 
                       (append existing-clauses (list (analyze-clause clause))))))
      (void))))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

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

(define (raw-variables-in exp)
  (unique-find-anywhere-if var-text? exp))

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

;(define (rename-variables x)
;  (sublis (map (lambda (var) (cons var (gensym var)))
;               (variables-in x))
;          x))

(define (preprocess-query x)
  (sublis (map (lambda (var) (cons var (make-variable var #f)))
               (raw-variables-in x))
          x))

(define (preprocess-clause x)
  (let ([vars (raw-variables-in x)]
        [counter 0])
    (define (template-counter)
      (let ([result counter])
        (set! counter (+ counter 1))
        result))
    (let ([new-x (sublis (map (lambda (var) (cons var (make-variable-template (template-counter))))
                              vars)
                         x)])
      (make-clause (length vars)
                   (list->vector vars)
                   (car new-x)
                   (cdr new-x)))))

(define (new-activation-frame num-vars var-list)
  (build-vector num-vars
                (lambda (i)
                  (make-variable (vector-ref var-list i)
                                 (new-counter)))))

(define (instantiate x activation-frame)
  (cond
    [(variable-template? x) (vector-ref activation-frame (variable-template-index x))]
    [(pair? x) (cons (instantiate (car x) activation-frame)
                     (instantiate (cdr x) activation-frame))]
    [else x]))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

(define (residualize-var var)
  (if (variable-counter var)
      (string->symbol (format "~a_~a" (variable-name var) (variable-counter var)))
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
                  (printf "~n~a = ~a" (residualize-var var) (simplify-term (variable-val var))))
                vars)))

(define (prove-query goal-list success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (if (pair? (cdr goal-list))
         (prove-query (cdr goal-list) success-cont cut-cont cut-cont)
         (success-cont cut-cont))]
    [(null? (cdr goal-list))
     (search-choices (car goal-list)
                     success-cont
                     failure-cont)]
    [else (search-choices (car goal-list)
                          (lambda (b2 fc2)
                            (prove-query (cdr goal-list) b2 success-cont cut-cont fc2))
                          failure-cont)]))

(define (memo-instantiate goal new-frame copy-stack index)
  (let ([val (vector-ref copy-stack index)])
    (if (eq? val *unbound*)
        (let ([new-val (instantiate goal new-frame)])
          (vector-set! copy-stack index new-val)
          new-val)
        val)))

(define (prove-goals goal-list new-frame copy-stack index success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (if (pair? (cdr goal-list))
         (prove-goals (cdr goal-list)
                      new-frame
                      copy-stack
                      (+ index 1)
                      success-cont
                      cut-cont
                      cut-cont)
         (success-cont cut-cont))]
    [(null? (cdr goal-list))
     (search-choices (memo-instantiate (car goal-list) new-frame copy-stack index)
                     success-cont
                     failure-cont)]
    [else (search-choices (memo-instantiate (car goal-list) new-frame copy-stack index)
                          (lambda (fc2)
                            (prove-goals (cdr goal-list)
                                         new-frame
                                         copy-stack
                                         (+ index 1)
                                         success-cont
                                         cut-cont
                                         fc2))
                          failure-cont)]))

(define (search-choices goal success-cont failure-cont)
  (let* ([goal-args (cdr goal)]
         [clauses (get-clauses (predicate goal) (length goal-args))])
    (cond
      [(procedure? clauses)
       (clauses goal-args success-cont failure-cont)]
      [(null? clauses)
       (failure-cont)]
      [else
       (let ([old-trail *trail*])
         (let iter ([clauses clauses])
           (if (null? (cdr clauses))
               ((car clauses) goal-args
                              success-cont
                              failure-cont
                              failure-cont)
               ((car clauses) goal-args
                              success-cont
                              failure-cont
                              (lambda ()
                                (reset-trail old-trail)
                                (iter (cdr clauses)))))))])))

(define (top-level-prove goals continue?)
  (let/ec exit
    (let ([fail (lambda ()
                  (reset-trail '())
                  (printf "~nNo.")
                  (exit))])
      (prove-query goals
                   (lambda (failure-cont)
                     (show-prolog-vars (variables-in goals))
                     (if (continue?)
                         (failure-cont)
                         (fail)))
                   fail
                   fail))))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove (preprocess-query 'goals) continue?)]))

(define (always-continue) #t)

(define-syntax benchmark
  (syntax-rules ()
    [(_ . goals)
     (time (top-level-prove (preprocess-query 'goals) always-continue))]))

(define-syntax <-
  (syntax-rules ()
    [(_ . clause)
     (add-clause 'clause)]))

(define (analyze-head head-args)
  (lambda (goal-args new-frame)
    (unify! goal-args (instantiate head-args new-frame))))

(define (analyze-goal goal index)
  (lambda (new-frame copy-stack success-cont cut-cont failure-cont)
    (search-choices (memo-instantiate goal new-frame copy-stack index)
                    success-cont
                    failure-cont)))

(define (analyze-sequence body)
  (define (sequentially a b)
    (lambda (new-frame copy-stack success-cont cut-cont failure-cont)
      (a new-frame
         copy-stack
         (lambda (fail2)
           (b new-frame copy-stack success-cont cut-cont fail2))
         cut-cont
         failure-cont)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (define (goals->procs goals)
    (let iter ([goals goals]
               [index 0])
      (if (null? goals)
          '()
          (cons (analyze-goal (car goals) index)
                (iter (cdr goals) (+ index 1))))))
  (let ([procs (goals->procs body)])
    (if (null? procs)
        (lambda (new-frame copy-stack success-cont cut-cont failure-cont)
          (success-cont failure-cont))
        (loop (car procs) (cdr procs)))))

(define (analyze-sequence/cut body)
  (lambda (new-frame copy-stack success-cont cut-cont failure-cont)
    (prove-goals body
                 new-frame
                 copy-stack
                 0
                 success-cont
                 cut-cont
                 failure-cont)))

(define (analyze-body body)
  (if (memq '! body)
      (analyze-sequence/cut body)
      (analyze-sequence body)))

(define (analyze-clause clause)
  (let* ([args (cdr (clause-head clause))]
         [body (clause-body clause)]
         [copy-size (length body)]
         [num-vars (clause-num-vars clause)]
         [var-vector (clause-var-list clause)]
         [eval-head (analyze-head args)]
         [eval-body (analyze-body body)])
    (lambda (goal-args success-cont cut-cont failure-cont)
      (let ([new-frame (new-activation-frame num-vars
                                             var-vector)]
            [copy-stack (make-vector copy-size *unbound*)])
        (if (eval-head goal-args new-frame)
            (eval-body new-frame
                       copy-stack
                       success-cont
                       cut-cont
                       failure-cont)
            (failure-cont))))))

(add-primitive '= 2
               (lambda (args success-cont failure-cont)
                 (if (unify! (car args) (cadr args))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'member 2
               (letrec ([mem-proc (lambda (args success-cont failure-cont)
                                    (let ([old-trail *trail*]
                                          [?arg1 (car args)]
                                          [?arg2 (cadr args)])
                                      (let ([clause2 (lambda ()
                                                       (reset-trail old-trail)
                                                       (let ([?x (make-variable '?x (new-counter))]
                                                             [?rest (make-variable '?rest (new-counter))])
                                                         (if (unify! ?arg2 (cons ?x ?rest))
                                                             (mem-proc (list ?arg1 ?rest)
                                                                       success-cont
                                                                       failure-cont)
                                                             (failure-cont))))])
                                        (let ([?rest (make-variable '?rest (new-counter))])
                                          (if (unify! ?arg2 (cons ?arg1 ?rest))
                                              (success-cont clause2)
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

(add-primitive 'is 2
               (lambda (args success-cont failure-cont)
                 (if (unify! (car args) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '< 2
               (lambda (args success-cont failure-cont)
                 (if (< (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=< 2
               (lambda (args success-cont failure-cont)
                 (if (<= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '> 2
               (lambda (args success-cont failure-cont)
                 (if (> (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '>= 2
               (lambda (args success-cont failure-cont)
                 (if (>= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=:= 2
               (lambda (args success-cont failure-cont)
                 (if (= (force-arith (car args)) (force-arith (cadr args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '=/= 2
               (lambda (args success-cont failure-cont)
                 (if (not (= (force-arith (car args)) (force-arith (cadr args))))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'integer? 1
               (lambda (args success-cont failure-cont)
                 (if (integer? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'number? 1
               (lambda (args success-cont failure-cont)
                 (if (number? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'not 1
               (lambda (args success-cont failure-cont)
                 (search-choices (car args)
                                 (lambda (fc) failure-cont)
                                 (lambda () (success-cont failure-cont)))))

(add-primitive 'fail 0
               (lambda (args success-cont failure-cont)
                 (failure-cont)))

(add-primitive 'true 0
               (lambda (args success-cont failure-cont)
                 (success-cont failure-cont)))

(add-primitive 'pretty-print 1
               (lambda (args success-cont failure-cont)
                 (pretty-print (deref (car args)))
                 (success-cont failure-cont)))




