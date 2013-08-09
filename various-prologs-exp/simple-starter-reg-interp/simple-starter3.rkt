#lang racket

(define *database* (make-hasheq))

(define (get-clauses name)
  (hash-ref *database* name
            (lambda () (error "predicate not defined, given" name))))

(define (add-clause name new-clause)
  (let ([existing-clauses (hash-ref *database* name '())])
    (hash-set! *database* name (append existing-clauses (list new-clause)))))

(define (show-db)
  (hash-for-each *database*
                 (lambda (pred clauses)
                   (printf "PREDICATE: ~a~n" pred)
                   (for-each (lambda (clause)
                               (printf "CLAUSE: ~a~n" (cons '<- clause)))
                             clauses)
                   (printf "~n"))))

(define (var? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define (unify x y subst)
  (cond
    [(equal? x y) subst]
    [(eq? subst #f) #f]
    [(var? x) (unify-variable x y subst)]
    [(var? y) (unify-variable y x subst)]
    [(or (not (pair? x)) (not (pair? y))) #f]
    [else (unify (cdr x) (cdr y)
                 (unify (car x) (car y) subst))]))

(define (unify-variable var val subst)
  (if (equal? var val)
      subst
      (let ([binding (bound? var subst)])
        (if binding
            (unify (cdr binding) val subst)
            (let ([binding (and (var? val) (bound? val subst))])
              (if binding
                  (unify var (cdr binding) subst)
                  (if (occurs-in? var val subst)
                      #f
                      (extend-subst var val subst))))))))

(define (occurs-in? var x subst)
  (if (equal? var x)
      #t
      (let ([binding (bound? x subst)])
        (if binding
            (occurs-in? var (cdr binding) subst)
            (if (pair? x)
                (or (occurs-in? var (car x) subst)
                    (occurs-in? var (cdr x) subst))
                #f)))))

(define bound? assq)

(define (extend-subst var val subst)
  (cons (cons var val) subst))

(define (must-deref orig-term subst error-tag)
  (let loop ([term orig-term])
    (if (var? term)
        (let ([binding (bound? term subst)])
          (if binding
              (loop (cdr binding))
              (error error-tag "insufficiently instantiated variable, given ~a" orig-term)))
        term)))

(define (deref orig-term subst)
  (let loop ([term orig-term])
    (if (var? term)
        (let ([binding (bound? term subst)])
          (if binding
              (loop (cdr binding))
              term))
        term)))

(define (simplify-term orig-term subst)
  (let ([term (deref orig-term subst)])
    (if (pair? term)
        (cons (simplify-term (car term) subst)
              (simplify-term (cdr term) subst))
        term)))

(define (collect-vars term already-seen)
  (cond
    [(eq? '? term)
     already-seen]
    [(var? term)
     (if (member term already-seen)
         already-seen
         (cons term already-seen))]
    [(pair? term)
     (let ([vars2 (collect-vars (car term) already-seen)])
       (collect-vars (cdr term) vars2))]
    [else
     already-seen]))

(define (copy-clause-cps term var-map k)
  (cond
    [(eq? '? term) (k (gensym '?) var-map)]
    [(var? term)
     (let ([binding (assq term var-map)])
       (if binding
           (k (cdr binding) var-map)
           (let ([new-var (gensym term)])
             (k new-var (cons (cons term new-var) var-map)))))]
    [(pair? term)
     (copy-clause-cps (car term)
                      var-map
                      (lambda (new-car-term var-map2)
                        (copy-clause-cps (cdr term)
                                         var-map2
                                         (lambda (new-cdr-term var-map3)
                                           (k (cons new-car-term new-cdr-term) var-map3)))))]
    [else (k term var-map)]))

(define (copy-clause term)
  (copy-clause-cps term '() (lambda (new-term var-map2) new-term)))

(define goal-lst-reg #f)
(define goal-reg #f)
(define clauses-reg #f)
(define lenv-reg #f)
(define sk-reg #f)
(define fk-reg #f)

(define (try-each)
  (cond
    [(null? clauses-reg)
     (invoke-fk)]
    [else (let ([new-clause (copy-clause (car clauses-reg))])
            (let ([new-lenv (unify goal-reg (car new-clause) lenv-reg)])
              (cond
                [new-lenv
                 (prove-goal-lst (cdr new-clause)
                                 new-lenv
                                 sk-reg
                                 (choice-point goal-reg (cdr clauses-reg) lenv-reg sk-reg fk-reg))]
                [else
                 (set! clauses-reg (cdr clauses-reg))
                 (try-each)])))]))

(define (prove-goal)
  (let ([clauses (get-clauses (car goal-reg))])
    (set! clauses-reg clauses)
    (try-each)))

(define (prove-goal-lst goal-lst lenv sk fk)
  (cond
    [(null? goal-lst)
     (set! sk-reg sk)
     (set! lenv-reg lenv)
     (set! fk-reg fk)
     (invoke-sk)]
    [else
     (set! goal-reg (car goal-lst))
     (set! lenv-reg lenv)
     (set! sk-reg (goal-sk (cdr goal-lst) sk))
     (set! fk-reg fk)
     (prove-goal)]))

(define (top-level-solve goal-lst)
  (prove-goal-lst goal-lst '() (top-sk (reverse (collect-vars goal-lst '()))) (top-fk)))

(struct top-fk ())
(struct choice-point (goal clauses lenv sk fk) #:transparent #:mutable)

(define (invoke-fk)
  (match fk-reg
    [(top-fk)
     #f]
    [(choice-point goal clauses lenv sk fk)
     (set! goal-reg goal)
     (set! clauses-reg clauses)
     (set! lenv-reg lenv)
     (set! sk-reg sk)
     (set! fk-reg fk)
     (try-each)]))

(struct top-sk (user-vars) #:transparent)
(struct goal-sk (goals sk) #:transparent)

(define (invoke-sk)
  (match sk-reg
    [(goal-sk goals sk)
     (prove-goal-lst goals lenv-reg sk fk-reg)]
    [(top-sk user-vars)
     (printf "solved: ~n")
     (for-each (lambda (var)
                 (printf "~a = ~a~n" var (simplify-term var lenv-reg)))
               user-vars)
     (invoke-fk)]))

(define-syntax <-
  (syntax-rules ()
    [(_ head body ...)
     (add-clause (car 'head) (list 'head 'body ...))]))

(define-syntax ?-
  (syntax-rules ()
    [(_ g0 g ...) (top-level-solve '(g0 g ...))]))

'(begin
   (<- (f 1 ?a) (g ?a))
   (<- (f 2 ?b) (h ?b))
   (<- (g a))
   (<- (g c))
   (<- (h dog))
   (<- (h cat))
   (?- (f ?x ?y)))

'(begin
   (<- (append (?x . ?y) ?z (?x . ?w)) (append ?y ?z ?w))
   (<- (append () ?x ?x))
   (?- (append ?a ?b (1 2 3 4 5))))

