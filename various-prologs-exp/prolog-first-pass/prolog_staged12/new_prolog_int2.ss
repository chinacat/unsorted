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

(define-struct anonymous-variable-template ())
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

(define-struct predicate (functor arity type clauses sources)
  #:mutable)

(define (intern-functor name arity)
  (hash-ref! *database*
             (cons name arity)
             (lambda ()
               (make-predicate name arity #f '() '()))))

(define (add-primitive functor arity proc)
  (unless (and (symbol? functor) (not (var-text? functor)))
    (error '<- "invalid predicate name (symbol required), given ~a" functor))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  (let ([new-pred (intern-functor functor arity)])
    (set-predicate-clauses! new-pred proc)
    (set-predicate-type! new-pred 'primitive))
  (void))

(define (add-clause-worker new-clause last?)
  (let ([functor (car (car new-clause))]
        [arity (length (cdr (car new-clause)))])
    (let ([clause (preprocess-clause (replace-?-variables/clause new-clause))])
      (unless (and (symbol? functor) (not (var-text? functor)))
        (error '<- "invalid predicate name (symbol required), given ~a" functor))
      (let* ([pred (intern-functor functor arity)]
             [existing-clauses (predicate-clauses pred)]
             [compiled-clause (analyze-clause clause)])
        (set-predicate-type! pred 'user-defined)
        (if (procedure? existing-clauses)
            ; allow user to replace a built-in with a user defined predicate
            (set-predicate-clauses! pred (list compiled-clause))
            (if last?
                (set-predicate-clauses! pred (append existing-clauses (list compiled-clause)))
                (set-predicate-clauses! pred (cons compiled-clause existing-clauses))))
        (set-predicate-sources! pred (append (predicate-sources pred) (list clause))))
      (void))))

(define (add-clause new-clause)
  (add-clause-worker new-clause #t))

(define (add-clause/first new-clause)
  (add-clause-worker new-clause #f))

; original version
;(define (replace-?-variables exp)
;  (cond
;    [(eq? exp '?) (gensym '?)]
;    [(pair? exp)
;     (reuse-cons (replace-?-variables (car exp))
;                 (replace-?-variables (cdr exp))
;                 exp)]
;    [else exp]))

(define (replace-?-variables/query exp)
  (cond
    [(eq? exp '?) (make-variable '? (new-counter))]
    [(pair? exp)
     (reuse-cons (replace-?-variables/query (car exp))
                 (replace-?-variables/query (cdr exp))
                 exp)]
    [else exp]))

(define (replace-?-variables/clause exp)
  (cond
    [(eq? exp '?) (make-anonymous-variable-template)]
    [(pair? exp)
     (reuse-cons (replace-?-variables/clause (car exp))
                 (replace-?-variables/clause (cdr exp))
                 exp)]
    [else exp]))

(define (unique-find-anywhere-if test tree [found-so-far '()])
  (if (pair? tree)
      (unique-find-anywhere-if test
                               (car tree)
                               (unique-find-anywhere-if test
                                                        (cdr tree)
                                                        found-so-far))
      (if (test tree)
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

(define (intern-term term)
  (if (and (list? term) (symbol? (car term)))
      (cons (intern-functor (car term) (length (cdr term))) (cdr term))
      term))

(define (intern-term-list lst)
  (cond
    [(null? lst)
     '()]
    [(list? lst)
     (cons (intern-term (car lst)) (intern-term-list (cdr lst)))]
    [else
     (error 'intern-term-list "expected a proper list, given ~s" lst)]))

(define (preprocess-query x)
  (intern-term-list (sublis (map (lambda (var) (cons var (make-variable var #f)))
                                 (raw-variables-in x))
                            x)))

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
                   (intern-term-list (cdr new-x))))))

(define (new-activation-frame num-vars var-list)
  (build-vector num-vars
                (lambda (i)
                  (make-variable (vector-ref var-list i)
                                 (new-counter)))))

; this should copy anonymous variables (represented as variable structures
; currently the code only "copies" variable-templates, not variables
(define (instantiate x activation-frame)
  (cond
    [(variable-template? x) (vector-ref activation-frame (variable-template-index x))]
    [(anonymous-variable-template? x) (make-variable '? (new-counter))]
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
    [(predicate? term)
     (predicate-functor term)]
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

(define (prove-query goal-list success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (if (pair? (cdr goal-list))
         (prove-query (cdr goal-list) success-cont cut-cont cut-cont)
         (success-cont cut-cont))]
    [(null? (cdr goal-list))
     (let ([goal (car goal-list)])
       (search-choices (car goal)
                       (cdr goal)
                       success-cont
                       failure-cont))]
    [else (let ([goal (car goal-list)])
            (search-choices (car goal)
                            (cdr goal)
                            (lambda (fc2)
                              (prove-query (cdr goal-list) success-cont cut-cont fc2))
                            failure-cont))]))

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
     (let ([goal (car goal-list)])
       (search-choices (car goal)
                       (memo-instantiate (cdr goal) new-frame copy-stack index)
                       success-cont
                       failure-cont))]
    [else (let ([goal (car goal-list)])
            (search-choices (car goal)
                            (memo-instantiate (cdr goal) new-frame copy-stack index)
                            (lambda (fc2)
                              (prove-goals (cdr goal-list)
                                           new-frame
                                           copy-stack
                                           (+ index 1)
                                           success-cont
                                           cut-cont
                                           fc2))
                            failure-cont))]))

(define (search-choices functor goal-args success-cont failure-cont)
  (let* ([clauses (predicate-clauses functor)])
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

; original version
;(define (top-level-prove goals continue?)
;  (let/ec exit
;    (let ([fail (lambda ()
;                  (reset-trail '())
;                  (printf "~nNo.")
;                  (exit))])
;      (prove-query goals
;                   (lambda (failure-cont)
;                     (show-prolog-vars (variables-in goals))
;                     (if (continue?)
;                         (failure-cont)
;                         (fail)))
;                   fail
;                   fail))))

; for deterministic queries, don't ask if user wants to continue
; (This aligns with SWI-Prolog behavior)
(define (top-level-prove goals continue?)
  (let/ec exit
    (let ([fail (lambda ()
                  (reset-trail '())
                  (printf "~nNo.")
                  (exit))])
      (prove-query goals
                   (lambda (failure-cont)
                     (show-prolog-vars (variables-in goals))
                     (cond
                       [(eq? fail failure-cont)
                        (reset-trail '())
                        (exit)]
                       [(continue?) (failure-cont)]
                       [else (fail)]))
                   fail
                   fail))))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove (preprocess-query (replace-?-variables/query 'goals)) continue?)]))

(define (always-continue) #t)

(define-syntax benchmark
  (syntax-rules ()
    [(_ . goals)
     (time (top-level-prove (preprocess-query (replace-?-variables/query 'goals)) always-continue))]))

(define-syntax <-
  (syntax-rules ()
    [(_ . clause)
     (add-clause 'clause)]))

(define (analyze-head head-args)
  (lambda (goal-args new-frame)
    (unify! goal-args (instantiate head-args new-frame))))

(define (analyze-goal goal index)
  (let ([functor (car goal)]
        [args (cdr goal)])
    (lambda (new-frame copy-stack success-cont cut-cont failure-cont)
      (search-choices functor
                      (memo-instantiate args new-frame copy-stack index)
                      success-cont
                      failure-cont))))

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

(define (test-analyze-sequence/cut body)
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
      (cond
        [(null? goals)
         '()]
        [(eq? '! (car goals))
         '!]
        [else
         (cons (analyze-goal (car goals) index)
               (iter (cdr goals) (+ index 1)))])))
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

(add-primitive '/= 2
               (lambda (args success-cont failure-cont)
                 (let* ([old-trail *trail*]
                        [result (unify! (car args) (cadr args))])
                   (reset-trail old-trail)
                   (if result
                       (failure-cont)
                       (success-cont failure-cont)))))

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

(add-primitive 'integer 1
               (lambda (args success-cont failure-cont)
                 (if (integer? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'float 1
               (lambda (args success-cont failure-cont)
                 (if (inexact? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'number 1
               (lambda (args success-cont failure-cont)
                 (if (number? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'atom 1
               (lambda (args success-cont failure-cont)
                 (if (symbol? (deref (car args)))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive 'atomic 1
               (lambda (args success-cont failure-cont)
                 (let ([arg (deref (car args))])
                   (if (or (symbol? arg) (number? arg))
                       (success-cont failure-cont)
                       (failure-cont)))))

; This code is currently broken... 
;  #1: the functor needs to be interned -- currently this will fail because the car of (car args)
;          is not a predicate object
;  #2: this should do a deref of (car args)
;  #3: need to add error checking (e.g. to ensure (car args) is a well-formed term
;  #4: the above should probably be implemented by a call to call/1, though the error checking
;          should report errors against the call to not/1, rather than call/1
(add-primitive 'not 1
               (lambda (args success-cont failure-cont)
                 (let* ([old-trail *trail*]
                        [arg (deref (car args))]
                        [goal-args (cdr arg)])
                   (search-choices (intern-functor (car arg) (length goal-args))
                                   goal-args
                                   (lambda (fc)
                                     (reset-trail old-trail)
                                     (failure-cont))
                                   (lambda ()
                                     (reset-trail old-trail)
                                     (success-cont failure-cont))))))

; still needs error checking!!!
(add-primitive 'call 1
               (lambda (args success-cont failure-cont)
                 (let* ([arg (deref (car args))]
                        [goal-args (cdr arg)])
                   (search-choices (intern-functor (car arg) (length goal-args))
                                   goal-args
                                   success-cont
                                   failure-cont))))

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

(add-primitive 'var 1
               (lambda (args success-cont failure-cont)
                 (let ([arg (deref (car args))])
                   (if (and (variable? arg) (eq? *unbound* (variable-val arg)))
                       (success-cont failure-cont)
                       (failure-cont)))))

(add-primitive 'nonvar 1
               (lambda (args success-cont failure-cont)
                 (let ([arg (deref (car args))])
                   (if (and (variable? arg) (eq? *unbound* (variable-val arg)))
                       (failure-cont)
                       (success-cont failure-cont)))))

(define (deref-copy term)
  (let ([varlst '()])
    (let walk ([term (deref term)])
      (cond
        [(pair? term)
         (reuse-cons (walk (deref (car term)))
                     (walk (deref (cdr term)))
                     term)]
        [(variable? term)
         (let ([entry (assq term varlst)])
           (if entry
               (cdr entry)
               (let ([new-var (make-variable (variable-name term) (new-counter))])
                 (set! varlst (cons (cons term new-var) varlst))
                 new-var)))]
        [else
         term]))))

(add-primitive 'copy_term 2
               (lambda (args success-cont failure-cont)
                 (if (unify! (deref-copy (car args)) (cadr args))
                     (success-cont failure-cont)
                     (failure-cont))))

(define (deref-equal? x y)
  (let ([x (deref x)]
        [y (deref y)])
    (or (equal? x y)
        (and (pair? x) (pair? y)
             (deref-equal? (car x) (car y))
             (deref-equal? (cdr x) (cdr y))))))

(add-primitive '== 2
               (lambda (args success-cont failure-cont)
                 (if (deref-equal? (car args) (cadr args))
                     (success-cont failure-cont)
                     (failure-cont))))

(add-primitive '/== 2
               (lambda (args success-cont failure-cont)
                 (if (deref-equal? (car args) (cadr args))
                     (failure-cont)
                     (success-cont failure-cont))))

(add-primitive 'findall 3
               (lambda (args success-cont failure-cont)
                 (let* ([exp (car args)]
                        [goal (deref (cadr args))]
                        [result (caddr args)]
                        [name (car goal)]
                        [goal-args (cdr goal)]
                        [answers '()])
                   (search-choices (intern-functor name (length goal-args))
                                   goal-args
                                   (lambda (fc)
                                     (set! answers (cons (deref-copy exp) answers))
                                     (fc))
                                   (lambda ()
                                     (if (and (pair? answers)
                                              (unify! (reverse answers) result))
                                         (success-cont failure-cont)
                                         (failure-cont)))))))

;; need to fix the handling of variables in the asserted clause
;; the code needs to be changed to convert variables to variable-templates
;; also, to properly handle vars in assertions, this needs to do a deref-copy
;; of the assertion (replacing instantiated vars with their values)
;(add-primitive 'assert 1
;               (lambda (args success-cont failure-cont)
;                 (let ([arg (deref (car args))])
;                   (cond
;                     [(and (variable? arg) (eq? *unbound* (variable-val arg)))
;                      (error 'assert "argument insufficiently instantiated, given ~s" (variable-name arg))]
;                     [(and (not (null? arg)) (list? arg))
;                      (if (eq? '<- (car arg))
;                          (add-clause (cdr arg))
;                          (add-clause (list arg)))
;                      
;                      (success-cont failure-cont)]
;                     [else
;                      (error 'assert "ill-formed clause, given ~s" arg)]))))
;
;; need to fix the handling of variables in the asserted clause
;; the code needs to be changed to convert variables to variable-templates
;(add-primitive 'asserta 1
;               (lambda (args success-cont failure-cont)
;                 (let ([arg (deref (car args))])
;                   (cond
;                     [(and (variable? arg) (eq? *unbound* (variable-val arg)))
;                      (error 'asserta "argument insufficiently instantiated, given ~s" (variable-name arg))]
;                     [(and (not (null? arg)) (list? arg))
;                      (if (eq? '<- (car arg))
;                          (add-clause/first (cdr arg))
;                          (add-clause/first (list arg)))
;                      (success-cont failure-cont)]
;                     [else
;                      (error 'asserta "ill-formed clause, given ~s" arg)]))))
;
;; need to fix the handling of variables in the asserted clause
;; the code needs to be changed to convert variables to variable-templates
;(add-primitive 'assertz 1
;               (lambda (args success-cont failure-cont)
;                 (let ([arg (deref (car args))])
;                   (cond
;                     [(and (variable? arg) (eq? *unbound* (variable-val arg)))
;                      (error 'assertz "argument insufficiently instantiated, given ~s" (variable-name arg))]
;                     [(and (not (null? arg)) (list? arg))
;                      (if (eq? '<- (car arg))
;                          (add-clause (cdr arg))
;                          (add-clause (list arg)))
;                      (success-cont failure-cont)]
;                     [else
;                      (error 'assertz "ill-formed clause, given ~s" arg)]))))
;
;; Notes on retract/1
;;   - retract should delete the first matching clause only; backtracking will search
;;     for additional matching clauses
;;   - need to find a representation for the clause list (and/or retract algorithm) 
;;     where retract is not quadratic in the number of clauses
;



