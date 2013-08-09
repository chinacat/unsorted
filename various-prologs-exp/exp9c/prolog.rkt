#lang racket

(provide <- ?- benchmark)

; To do:
; [9/2/2012]
; Change the code for compiling clauses and queries to eliminate the calls to execute goals for
; facts (done), binary clauses, and single-goal queries
; change <- to check for facts, binary clauses vs. n-ary clauses, 
;    creating special versions of compile-clause for each

; To do:
; [8/22/2012]
; 1. [DONE] Update ?- to support multiple goals
; 2. [DONE] Add support of cut
; 3. Add support of built-in predicates
; 4. 'Improve' compilation of head matching / unification
; 5. Add primitives

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name id val) #:transparent #:mutable)

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

(define count-trailed-vars 0)

(define last-cp 0)
(define (set-last-cp! fk)
  (when (failk? fk)
    (set! last-cp (failk-cp-id fk))))

(define (set-binding! var val)
  (unless (eq? var val)
    (when (< (variable-id var) last-cp)
      (set! *trail* (cons var *trail*))
      (set! count-trailed-vars (+ count-trailed-vars 1)))
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

(define count-var-creates 0)
(define count-max-vars 0)

(define *variable-counter* 0)
(define (new-variable name)
  (let ([id *variable-counter*])
    (set! *variable-counter* (+ 1 *variable-counter*))
    (when (> *variable-counter* count-max-vars)
      (set! count-max-vars *variable-counter*))
    (set! count-var-creates (+ count-var-creates 1))
    (make-variable name id *unbound*)))

(define *database* (make-hasheq))

(define-syntax exists
  (syntax-rules ()
    [(_ (var ...) exp0 exp ...)
     (let ([var (new-variable 'var)] ...)
       exp0 exp ...)]))

(define-for-syntax (variable-symbol? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define-syntax (transform-term stx)
  (define (walk stx)
    (syntax-case stx ()
      [(a . b)
       #`(#,(walk #'a) . #,(walk #'b))]
      [id
       (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
       #'(unquote id)]
      [any
       #'any]))
  (syntax-case stx ()
    [(_ goal)
     #`(quasiquote #,(walk #'goal))]))

(define-for-syntax (already-seen? id vars)
  (if (null? vars)
      #f
      (if (eq? (syntax-e id) (syntax-e (car vars)))
          #t
          (already-seen? id (cdr vars)))))

(define-for-syntax (walk-term stx vars)
  (syntax-case stx ()
    [(a . b)
     (let-values ([(new-a a-vars) (walk-term #'a vars)])
       (let-values ([(new-b b-vars) (walk-term #'b a-vars)])
         (values #`(#,new-a . #,new-b) b-vars)))]
    [id
     (and (identifier? #'id) (eq? '? (syntax-e #'id)))
     (let ([new-id (car (generate-temporaries #'(id)))])
       (values new-id (cons new-id vars)))]
    [id
     (and (identifier? #'id) (variable-symbol? (syntax-e #'id)))
     (if (already-seen? #'id vars)
         (values #'id vars)
         (values #'id (cons #'id vars)))]
    [any
     (values #'any vars)]))

(define-for-syntax (compute-goal goal vars)
  (let-values ([(new-goal new-vars) (walk-term goal vars)])
    (syntax-case new-goal ()
      [(functor arg ...)
       (let* ([name (syntax-e #'functor)]
              [arity (length (syntax->list #'(arg ...)))]
              [predname (string->symbol (string-append (symbol->string name)
                                                       "/"
                                                       (number->string arity)))])
         (values #`(#,predname arg ...) new-vars))]
      [id
       (and (identifier? #'id) (eq? '! (syntax-e #'id)))
       (values #'id new-vars)])))

(define-for-syntax (compute-goals in-goals acc-goals vars)
  (if (null? in-goals)
      (values (reverse acc-goals) vars)
      (let-values ([(new-goal new-vars) (compute-goal (car in-goals) vars)])
        (compute-goals (cdr in-goals)
                       (cons new-goal acc-goals)
                       new-vars))))

; compute-head-match:
; IN: params, terms
; OUT: var-filter-list, bindings, tests
(define-for-syntax (compute-head-match params terms)
  (define (iter params terms filter-list acc-bindings acc-tests)
    (cond
      [(null? params)
       (values filter-list (reverse acc-bindings) (reverse acc-tests))]
      [(and (identifier? (car terms)) (variable-symbol? (syntax-e (car terms))))
       (if (already-seen? (car terms) filter-list)
           (iter (cdr params)
                 (cdr terms)
                 filter-list
                 acc-bindings
                 (cons #`(unify! #,(car params) #,(car terms))
                       acc-tests))
           (iter (cdr params)
                 (cdr terms)
                 (cons (car terms) filter-list)
                 (cons #`(#,(car terms) #,(car params))
                       acc-bindings)
                 acc-tests))]
      [else
       (iter (cdr params)
             (cdr terms)
             filter-list
             acc-bindings
             (cons #`(unify! #,(car params) (transform-term #,(car terms)))
                   acc-tests))]))
  (iter params terms '() '() '()))

(define-for-syntax (filter-var-list filter-list vars)
  (let loop ([vars vars])
    (cond
      [(null? vars)
       '()]
      [(already-seen? (car vars) filter-list)
       (loop (cdr vars))]
      [else
       (cons (car vars) (loop (cdr vars)))])))

(define-syntax (compile-clause stx)
  (define (compute-params args)
    (if (null? args)
        '()
        (cons (car (generate-temporaries (list (car args))))
              (compute-params (cdr args)))))
  (syntax-case stx ()
    [(_ head body)
     (let*-values ([(new-head vars0) (walk-term #'head '())]
                   [(new-goals vars) (compute-goals (syntax->list #'body) '() vars0)])
       (with-syntax ([(functor arg ...) new-head])
         (let*-values ([(new-args) (syntax->list #'(arg ...))]
                       [(new-params) (compute-params new-args)]
                       [(filter-list bindings tests) (compute-head-match new-params new-args)])
           (with-syntax ([(param ...) new-params]
                         [(ng ...) new-goals])
             (let* ([name (syntax-e #'functor)]
                    [arity (length (syntax->list #'(arg ...)))]
                    [predname (string->symbol (string-append (symbol->string name)
                                                             "/"
                                                             (number->string arity)))])
               #`(begin
                   (add-clause '#,predname
                               (lambda (sk cutk fk param ...)
                                 (set-last-cp! fk)
                                 (let #,bindings
                                   (exists #,(filter-var-list filter-list vars)
                                           (if (and . #,tests)
                                               (compile-goals sk cutk fk (ng ...))
                                               (apply-fk fk))))))
                   (void)))))))]))

(define-syntax compile-goals
  (syntax-rules (!)
    [(_ sk cutk fk ())
     (apply-sk sk fk)]
    [(_ sk cutk fk (!))
     (apply-sk sk cutk)]
    [(_ sk cutk fk (g))
     (let ([goal (transform-term g)])
       (dispatch (car goal) sk fk (cdr goal)))]
    [(_ sk cutk fk (g ...))
     (execute-goals sk cutk fk (list (transform-term g) ...))]))

(define (add-clause functor compiled-clause)
  (let ([existing-clauses (hash-ref *database* functor '())])
    (if (procedure? existing-clauses)
        (hash-set! *database* functor (list compiled-clause))
        (hash-set! *database* functor (append existing-clauses (list compiled-clause))))))

(define (compute-functor-name name arity)
  (string->symbol (string-append (symbol->string name)
                                 "/"
                                 (number->string arity))))

(define (add-primitive functor arity proc)
  (unless (symbol? functor)
    (error '<- "invalid predicate name (symbol required), given ~a" functor))
  (unless (procedure? proc)
    (error 'add-primitive "procedure required, given ~a" proc))
  (hash-set! *database* (compute-functor-name functor arity) proc))

(define-syntax <-
  (syntax-rules ()
    [(_ head g ...)
     (compile-clause head (g ...))]))

(define (execute-goals sk cutk fk goals)
  (cond
    [(null? goals)
     (set! count-null-goals (+ count-null-goals 1))
     (apply-sk sk fk)]
    [(null? (cdr goals))
     (let ([goal (car goals)])
       (if (eq? '! goal)
           (apply-sk sk cutk)
           (dispatch (car goal)
                     sk
                     fk
                     (cdr goal))))]
    [(eq? '! (car goals))
     (execute-goals sk cutk cutk (cdr goals))]
    [else
     (let ([goal (car goals)])
       (dispatch (car goal)
                 (build-sk sk cutk (cdr goals))
                 fk
                 (cdr goal)))]))

(define (dispatch functor sk fk args)
  (let ([clauses (hash-ref *database* functor
                           (lambda () (error "predicate not defined, given" functor)))])
    (cond
      [(procedure? clauses)
       (apply clauses sk fk args)]
      [(null? (cdr clauses))
       (apply (car clauses)
              sk
              fk
              fk
              args)]
      [else
       (let ([choice-point (build-fk sk fk (cdr clauses) args *trail*)])
         (set! count-choice-points (+ count-choice-points 1))
         (apply (car clauses)
                sk
                fk
                choice-point
                args))])))

(define (update-fk fk remaining-clauses)
  (set-failk-clauses! fk remaining-clauses)
  fk)

(define (try-again fk)
  (reset-trail (failk-old-trail fk))
  (let ([clauses (failk-clauses fk)]
        [cutk (failk-parent-fk fk)])
    (cond
      [(null? (cdr clauses))
       (let ([sk (failk-sk fk)]
             [args (failk-args fk)])
         (recycle-fk fk)
         (apply (car clauses)
                sk
                cutk
                cutk
                args))]
      [else
       (apply (car clauses)
              (failk-sk fk)
              cutk
              (update-fk fk (cdr clauses))
              (failk-args fk))])))

(define (residualize-var var)
  (if (>= (variable-id var) 0)
      (string->symbol (format "~a_~a" (variable-name var) (variable-id var)))
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
                  (if (eq? '? (variable-name var))
                      (void)
                      (printf "~n~a = ~a" (residualize-var var) (simplify-term (variable-val var)))))
                vars)))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

(define-syntax (?- stx)
  (syntax-case stx ()
    [(_ g ...)
     (let-values ([(ngs nvs) (compute-goals (syntax->list #'(g ...)) '() '())])
       (with-syntax ([(ng ...) ngs]
                     [(var ...) (reverse nvs)])
         #`(let/ec exit
             (let ([fail (build-top-fk exit)]
                   [var (make-variable 'var -1 *unbound*)] ...)
               (compile-goals (build-top-sk fail exit (list var ...))
                              fail
                              fail
                              (ng ...))))))]))

(define-struct failk (sk parent-fk clauses args old-trail next cp-id)
  #:mutable
  #:transparent)

(define *recycle-list* '())

(define (recycle-fk fk)
  (set-failk-next! fk *recycle-list*)
  (set-failk-sk! fk #f)
  (set-failk-parent-fk! fk #f)
  (set-failk-clauses! fk #f)
  (set-failk-args! fk #f)
  (set-failk-old-trail! fk #f)
  (set! *recycle-list* fk))

(define (reuse-fk sk parent-fk clauses args old-trail)
  (let ([fk *recycle-list*])
    (set! *recycle-list* (failk-next *recycle-list*))
    (set-failk-sk! fk sk)
    (set-failk-parent-fk! fk parent-fk)
    (set-failk-clauses! fk clauses)
    (set-failk-args! fk args)
    (set-failk-old-trail! fk old-trail)
    (set-failk-next! fk '())
    (set-failk-cp-id! fk *variable-counter*)
    fk))

(define (build-fk sk parent-fk clauses args old-trail)
  (if (failk? *recycle-list*)
      (reuse-fk sk parent-fk clauses args old-trail)
      (begin (set! count-fk (+ count-fk 1))
             (make-failk sk parent-fk clauses args old-trail #f *variable-counter*))))

(define (build-sk sk cutk goals)
  (set! count-sk (+ count-sk 1))
  (lambda (fk)
    (execute-goals sk cutk fk goals)))

(define-struct top-fk (exit cp-id)
  #:mutable
  #:transparent)

(define (build-top-fk exit)
  (make-top-fk exit *variable-counter*))

(define (build-top-sk fail exit vars)
  (lambda (fk)
    (show-prolog-vars vars)
    (cond
      [(eq? fail fk)
       (reset-trail '())
       (exit)]
      [(continue?) (apply-fk fk)]
      [else (fail)])))

(define (build-benchmark-sk fail exit vars)
  (lambda (fk)
    (show-prolog-vars vars)
    (cond
      [(eq? fail fk)
       (reset-trail '())
       (exit)]
      [else (apply-fk fk)])))

(define (apply-fk fk)
  (cond
    [(failk? fk)
     (set! *variable-counter* (failk-cp-id fk))
     (try-again fk)]
    [(top-fk? fk)
     (reset-trail '())
     (set! *variable-counter* (top-fk-cp-id fk))
     (printf "~nNo.")
     ((top-fk-exit fk))]
    [else
     (error 'apply-fk "expected a failure continuation, given ~a" fk)]))

(define (apply-sk sk fk)
  (sk fk))

(add-primitive '= 2
               (lambda (sk fk a1 a2)
                 (if (unify! a1 a2)
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '/= 2
               (lambda (sk fk a1 a2)
                 (let* ([old-trail *trail*]
                        [result (unify! a1 a2)])
                   (reset-trail old-trail)
                   (if result
                       (apply-fk fk)
                       (apply-sk sk fk)))))

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
               (lambda (sk fk a1 a2)
                 (if (unify! a1 (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '< 2
               (lambda (sk fk a1 a2)
                 (if (< (force-arith a1) (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '> 2
               (lambda (sk fk a1 a2)
                 (if (> (force-arith a1) (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '=< 2
               (lambda (sk fk a1 a2)
                 (if (<= (force-arith a1) (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '>= 2
               (lambda (sk fk a1 a2)
                 (if (>= (force-arith a1) (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '=:= 2
               (lambda (sk fk a1 a2)
                 (if (= (force-arith a1) (force-arith a2))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '=/= 2
               (lambda (sk fk a1 a2)
                 (if (not (= (force-arith a1) (force-arith a2)))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive 'fail 0
               (lambda (sk fk)
                 (apply-fk fk)))

(add-primitive 'true 0
               (lambda (sk fk)
                 (apply-sk sk fk)))

(add-primitive 'call 1
               (lambda (sk fk a)
                 (let ([term (deref a)])
                   (if (variable? term)
                       (error 'call "argument insufficiently instantiated, given ~s" term)
                       (let ([args (cdr term)])
                         (dispatch (compute-functor-name (car term) (length args)) sk fk args))))))

(<- (not ?term) (call ?term) ! (fail))
(<- (not ?) (true))

(add-primitive 'pretty-print 1
               (lambda (sk fk a)
                 (pretty-print (deref a))
                 (apply-sk sk fk)))

(add-primitive 'var 1
               (lambda (sk fk a)
                 (let ([arg (deref a)])
                   (if (and (variable? arg) (eq? *unbound* (variable-val arg)))
                       (apply-sk sk fk)
                       (apply-fk fk)))))

(add-primitive 'nonvar 1
               (lambda (sk fk a)
                 (let ([arg (deref a)])
                   (if (and (variable? arg) (eq? *unbound* (variable-val arg)))
                       (apply-fk fk)
                       (apply-sk sk fk)))))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

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
               (let ([new-var (new-variable (variable-name term))])
                 (set! varlst (cons (cons term new-var) varlst))
                 new-var)))]
        [else
         term]))))

(define (deref-equal? x y)
  (let ([x (deref x)]
        [y (deref y)])
    (or (equal? x y)
        (and (pair? x) (pair? y)
             (deref-equal? (car x) (car y))
             (deref-equal? (cdr x) (cdr y))))))

(add-primitive 'copy_term 2
               (lambda (sk fk a1 a2)
                 (if (unify! (deref-copy a1) a2)
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '== 2
               (lambda (sk fk a1 a2)
                 (if (deref-equal? a1 a2)
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive '/== 2
               (lambda (sk fk a1 a2)
                 (if (deref-equal? a1 a2)
                     (apply-fk fk)
                     (apply-sk sk fk))))

(add-primitive 'integer 1
               (lambda (sk fk a)
                 (if (integer? (deref a))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive 'float 1
               (lambda (sk fk a)
                 (if (inexact? (deref a))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive 'number 1
               (lambda (sk fk a)
                 (if (number? (deref a))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive 'atom 1
               (lambda (sk fk a)
                 (if (symbol? (deref a))
                     (apply-sk sk fk)
                     (apply-fk fk))))

(add-primitive 'atomic 1
               (lambda (sk fk a)
                 (let ([arg (deref a)])
                   (if (or (symbol? arg) (number? arg))
                       (apply-sk sk fk)
                       (apply-fk fk)))))

(define count-sk 0)
(define count-fk 0)
(define count-null-goals 0)
(define count-choice-points 0)

(define (reset-counts)
  (set! count-sk 0)
  (set! count-fk 0)
  (set! count-null-goals 0)
  (set! count-choice-points 0)
  (set! count-var-creates 0)
  (set! count-max-vars 0)
  (set! count-trailed-vars 0))

(define-syntax (benchmark stx)
  (syntax-case stx ()
    [(_ g ...)
     (let-values ([(ngs nvs) (compute-goals (syntax->list #'(g ...)) '() '())])
       (with-syntax ([(ng ...) ngs]
                     [(var ...) (reverse nvs)])
         #`(begin (reset-counts)
                  (time (let/ec exit
                          (let ([fail (build-top-fk exit)]
                                [var (make-variable 'var -1 *unbound*)] ...)
                            (execute-goals (build-benchmark-sk fail exit (list var ...))
                                           fail
                                           fail
                                           (list (transform-term ng) ...)))))
                  (printf "# of sk: ~a; # of fk: ~a~n" count-sk count-fk)
                  (printf "# of choice points: ~a~n" count-choice-points)
                  (printf "# of hits on empty goal-list test: ~a~n" count-null-goals)
                  (printf "# of var creates: ~a; max counter val: ~a~n"
                          count-var-creates
                          count-max-vars)
                  (printf "# of trailed vars: ~a~n" count-trailed-vars))))]))



