#lang racket

(define *database* (make-hash))

(define (get-clauses name arity)
  (hash-ref *database* (cons name arity) '()))

(define (add-clause name arity new-clause)
  (let* ([key (cons name arity)]
         [existing-clauses (hash-ref *database* key '())])
    (hash-set! *database* key (append existing-clauses (list new-clause)))))

(define (add-clause/front name arity new-clause)
  (let* ([key (cons name arity)]
         [existing-clauses (hash-ref *database* key '())])
    (hash-set! *database* key (cons new-clause existing-clauses))))

(define (add-primitive name arity proc)
  (hash-set! *database* (cons name arity) proc))

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

(define (try-each goal clauses lenv sk fk)
  (cond
    [(null? (cdr clauses))
     (try-goal goal
               (car clauses)
               lenv
               sk
               fk
               fk)]
    [else
     (try-goal goal
               (car clauses)
               lenv
               sk
               (lambda () (try-each goal (cdr clauses) lenv sk fk))
               fk)]))

(define (try-goal goal clause lenv sk fk cutk)
  (let ([new-clause (copy-clause clause)])
    (let ([new-lenv (unify goal (car new-clause) lenv)])
      (if new-lenv
          (prove-goal-lst (cdr new-clause)
                          new-lenv
                          sk
                          fk
                          cutk)
          (fk)))))

(define (prove-goal goal lenv sk fk)
  (let ([clauses (get-clauses (car goal) (length (cdr goal)))])
    (cond
      [(null? clauses)
       (error 'prove-goal "predicate ~a/~a not defined" (car goal) (length (cdr goal)))]
      [(procedure? clauses)
       (apply clauses lenv sk fk (cdr goal))]
      [else
       (try-each goal clauses lenv sk fk)])))

(define (prove-goal-lst goal-lst lenv sk fk cutk)
  (cond
    [(null? goal-lst) (sk lenv fk)]
    [(eq? '! (car goal-lst))
     (prove-goal-lst (cdr goal-lst) lenv sk cutk cutk)]
    [(null? (cdr goal-lst))
     (prove-goal (car goal-lst) lenv sk fk)]
    [else
     (prove-goal (car goal-lst)
                 lenv
                 (lambda (lenv2 fk2)
                   (prove-goal-lst (cdr goal-lst) lenv2 sk fk2 cutk))
                 fk)]))

(define (more-answers?)
  (printf "?")
  (let ([response (read-line)])
    (cond
      [(string=? ";" response) #t]
      [(string=? "." response) #f]
      [else (more-answers?)])))

(define (top-level-solve goal-lst)
  (let/ec exit
    (let* ([succeeded-at-least-once? #f]
           [top-fk (lambda ()
                     (if succeeded-at-least-once?
                         (printf "Yes.~n")
                         (printf "No.~n"))
                     (exit))])
      (prove-goal-lst goal-lst
                      '()
                      (lambda (lenv fk)
                        (set! succeeded-at-least-once? #t)
                        ;(printf "solved: ~n")
                        (for-each (lambda (var)
                                    (printf "~a = ~a~n" var (simplify-term var lenv)))
                                  (reverse (collect-vars goal-lst '())))
                        (cond
                          [(eq? fk top-fk)
                           (top-fk)]
                          [(more-answers?)
                           (fk)]
                          [else
                           (top-fk)]))
                      top-fk
                      top-fk))))

(define-syntax <-
  (syntax-rules ()
    [(_ head body ...)
     (add-clause (car 'head) (length (cdr 'head)) (list 'head 'body ...))]))

(define-syntax ?-
  (syntax-rules ()
    [(_ g0 g ...) (top-level-solve '(g0 g ...))]))

(add-primitive 'call 1
               (lambda (lenv sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'call/1)])
                   (prove-goal new-goal lenv sk fk))))

(add-primitive 'not 1
               (lambda (lenv sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'not/1)])
                   (prove-goal new-goal
                               lenv
                               (lambda (lenv2 fk2)
                                 (fk))
                               (lambda ()
                                 (sk lenv fk))))))

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

(<- (= ?a ?a))
(<- (fail) (= 1 0))

(<- (append (?x . ?y) ?z (?x . ?w)) (append ?y ?z ?w))
(<- (append () ?x ?x))

;(<- (once ?g) (call ?g) !)
(<- (p 1))
(<- (p 2))
(<- (p 3))

(add-primitive 'once 1
               (lambda (lenv sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'call/1)])
                   (prove-goal new-goal
                               lenv
                               ; this implements the 'cut' in once
                               (lambda (lenv2 fk2)
                                 (sk lenv2 fk))
                               fk))))

(add-primitive 'write 1
               (lambda (lenv sk fk term)
                 (printf "~a" (simplify-term term lenv))
                 (sk lenv fk)))

(add-primitive 'nl 0
               (lambda (lenv sk fk)
                 (newline)
                 (sk lenv fk)))

; very similar to copy-clause, but derefences bound variables, and then procedures to copy the value
; the variable is unbound, then a new variable is created
(define (deref-copy term lenv)
  (define (copy-clause-cps term var-map k)
    (cond
      [(eq? '? term) (k (gensym '?) var-map)]
      [(var? term)
       (let ([val-binding (assq term lenv)])
         (if val-binding
             (copy-clause-cps (cdr val-binding)
                              var-map
                              k)
             (let ([vm-binding (assq term var-map)])
               (if vm-binding
                   (k (cdr vm-binding) var-map)
                   (let ([new-var (gensym term)])
                     (k new-var (cons (cons term new-var) var-map)))))))]
      [(pair? term)
       (copy-clause-cps (car term)
                        var-map
                        (lambda (new-car-term var-map2)
                          (copy-clause-cps (cdr term)
                                           var-map2
                                           (lambda (new-cdr-term var-map3)
                                             (k (cons new-car-term new-cdr-term) var-map3)))))]
      [else (k term var-map)]))
  (copy-clause-cps term '() (lambda (new-term var-map2) new-term)))

(add-primitive 'copy 2
               (lambda (lenv sk fk src-term new-term)
                 (let ([new-lenv (unify (deref-copy src-term lenv) new-term lenv)])
                   (if new-lenv
                       (sk new-lenv fk)
                       (fk)))))

(define assertz-impl
  (lambda (lenv sk fk term)
    (let* ([new-term (deref-copy term lenv)]
           [new-clause (if (eq? '<- (car new-term))
                           (cdr new-term)
                           (list new-term))]
           [new-head (car new-clause)]
           [functor (car new-head)]
           [arity (length (cdr new-head))])
      (add-clause functor arity new-clause)
      (sk lenv fk))))

(add-primitive 'assert 1
               assertz-impl)

(add-primitive 'asserta 1
               (lambda (lenv sk fk term)
                 (let* ([new-term (deref-copy term lenv)]
                        [new-clause (if (eq? '<- (car new-term))
                                        (cdr new-term)
                                        (list new-term))]
                        [new-head (car new-clause)]
                        [functor (car new-head)]
                        [arity (length (cdr new-head))])
                   (add-clause/front functor arity new-clause)
                   (sk lenv fk))))

(define (reuse-cons first rest orig-pair)
  (if (and (eq? first (car orig-pair))
           (eq? rest (cdr orig-pair)))
      orig-pair
      (cons first rest)))

(add-primitive 'assertz 1
               assertz-impl)

(define (remove-first-match head clause-lst lenv)
  (cond
    [(null? clause-lst)
     (values '() lenv)]
    [(unify head (car (car clause-lst)) lenv)
     =>
     (lambda (new-lenv)
       (values (cdr clause-lst) new-lenv))]
    [else
     (let-values ([(new-cdr new-lenv) (remove-first-match head (cdr clause-lst) lenv)])
       (values (reuse-cons (car clause-lst) new-cdr clause-lst) new-lenv))]))

(define retract-impl
  (lambda (lenv sk fk head)
    (let* ([functor (car head)]
           [arity (length (cdr head))]
           [clause-lst (get-clauses functor arity)])
      (let-values ([(new-clause-lst new-lenv)
                    (remove-first-match head clause-lst lenv)])
        (cond
          [(eq? new-clause-lst clause-lst)
           (fk)]
          [else
           (hash-set! *database* (cons functor arity) new-clause-lst)
           (sk new-lenv
               (lambda ()
                 (retract-impl lenv sk fk head)))])))))

(add-primitive 'retract 1
               retract-impl)


(<- (member ?x (?x . ?l)))
(<- (member ?x (?y . ?l)) (member ?x ?l))


