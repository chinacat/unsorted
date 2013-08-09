#lang racket

; new0 -- initial version of 'new' TinyProlog with the specialized copy and unify-head implementation
;
; TO DO:
;         1. [DONE] Add support of anonymous variables
;         2. [DONE] Change the runtime representation of variables to be structs instead of symbols
;         3. Optimize make-copy-term, 
;              - to avoid copying 'constant' parts of the term
;              - simplify/optimize copying of (<term> . null)
;         4. Turn variables which are 'set', but never referenced into anonymous variables

(provide <-
         ?-
         benchmark
         show-db
         show-db/verbose)

; unification, and generating specialized unifiers and copiers

(struct var (name) #:transparent)

(define (var-src? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define (unify x y subst)
  (cond
    [(equal? x y) subst]
    [(var? x) (unify-variable x y subst)]
    [(var? y) (unify-variable y x subst)]
    [(and (pair? x) (pair? y))
     (let ([s (unify (car x) (car y) subst)])
       (and s (unify (cdr x) (cdr y) s)))]
    [else #f]))

(define (unify-variable var val subst)
  (if (equal? var val)
      subst
      (let ([binding (bound? var subst)])
        (if binding
            (unify (cdr binding) val subst)
            (let ([binding (and (var? val) (bound? val subst))])
              (if binding
                  (unify var (cdr binding) subst)
                  (extend-subst var val subst)))))))

(define (deref term subst)
  (if (var? term)
      (let ([binding (bound? term subst)])
        (if binding
            (deref (cdr binding) subst)
            term))
      term))

(define bound? assq)

(define (extend-subst var val subst)
  (cons (cons var val) subst))


(struct anon-var () #:transparent)
(struct set-var (name idx) #:transparent)
(struct ref-var (name idx) #:transparent)

(define (pre-cps term as idx k)
  (cond
    [(eq? '? term)
     (k (anon-var) as idx)]
    [(var-src? term)
     (let ([seen? (assq term as)])
       (if seen?
           (k (ref-var term (cdr seen?)) as idx)
           (k (set-var term idx) (cons (cons term idx) as) (+ idx 1))))]
    [(pair? term)
     (pre-cps (car term)
              as
              idx
              (lambda (new-car as2 idx2)
                (pre-cps (cdr term)
                         as2
                         idx2
                         (lambda (new-cdr as3 idx3)
                           (k (cons new-car new-cdr) as3 idx3)))))]
    [else
     (k term as idx)]))

(define (pre term)
  (pre-cps term '() 0
           (lambda (new-term as idx)
             (values new-term idx))))

(define (make-copy-term term)
  (cond
    [(pair? term)
     (let ([car-copier (make-copy-term (car term))]
           [cdr-copier (make-copy-term (cdr term))])
       (lambda (frame)
         (cons (car-copier frame) (cdr-copier frame))))]
    [(anon-var? term)
     (lambda (frame)
       (var (gensym '?)))]
    [(set-var? term)
     (let ([name (set-var-name term)]
           [idx (set-var-idx term)])
       (lambda (frame)
         (let ([new-var (var (gensym name))])
           (vector-set! frame idx new-var)
           new-var)))]
    [(ref-var? term)
     (let ([idx (ref-var-idx term)])
       (lambda (frame)
         (vector-ref frame idx)))]
    [else
     (lambda (frame)
       term)]))

(define (make-unify-head head)
  (cond
    [(null? head)
     (lambda (arg frame subst)
       (let ([arg (deref arg subst)])
         (cond
           [(null? arg) subst]
           [(var? arg) (extend-subst arg '() subst)]
           [else #f])))]
    [(anon-var? head)
     (lambda (arg frame subst)
       subst)]
    [(set-var? head)
     (let ([idx (set-var-idx head)])
       (lambda (arg frame subst)
         (vector-set! frame idx (deref arg subst))
         subst))]
    [(ref-var? head)
     (let ([idx (ref-var-idx head)])
       (lambda (arg frame subst)
         (unify (vector-ref frame idx) arg subst)))]
    [(not (pair? head))
     (let ([constant head])
       (lambda (arg frame subst)
         (let ([arg (deref arg subst)])
           (cond
             [(equal? constant arg) subst]
             [(var? arg) (extend-subst arg constant subst)]
             [else #f]))))]
    [(pair? head)
     (let ([unify-car (make-unify-head (car head))]
           [unify-cdr (make-unify-head (cdr head))]
           [head-copy (make-copy-term head)])
       (lambda (arg frame subst)
         (let ([arg (deref arg subst)])
           (cond
             [(pair? arg)
              (let ([s (unify-car (car arg) frame subst)])
                (and s (unify-cdr (cdr arg) frame s)))]
             [(var? arg) (extend-subst arg (head-copy frame) subst)]
             [else #f]))))]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))


; clause and database representation

(struct primitive (fun) #:transparent)
(struct clause (head body frame-size source) #:transparent)

(define *database* (make-hash))

(define (get-clauses name arity)
  (hash-ref *database* (cons name arity) '()))

(define (intern-clause new-clause-source)
  (let-values ([(pre-clause frame-size) (pre new-clause-source)])
    (clause (make-unify-head (car pre-clause))
            (map make-copy-term (cdr pre-clause))
            frame-size
            new-clause-source)))

(define (add-clause name arity new-clause-source)
  (let* ([key (cons name arity)]
         [existing-clauses (hash-ref *database* key '())])
    (let ([new-clause (intern-clause new-clause-source)])
      (hash-set! *database* key (append existing-clauses (list new-clause))))))

(define (add-primitive name arity proc)
  (hash-set! *database* (cons name arity) (primitive proc)))

(define (show-db)
  (hash-for-each *database*
                 (lambda (pred clauses)
                   (printf "PREDICATE: ~a~n" pred)
                   (for-each (lambda (c)
                               (printf "CLAUSE: ~a~n" (cons '<- (clause-source c))))
                             clauses)
                   (printf "~n"))))

(define (show-db/verbose)
  (hash-for-each *database*
                 (lambda (pred clauses)
                   (printf "PREDICATE: ~a~n" pred)
                   (for-each (lambda (c)
                               (printf "CLAUSE: ~a ~a ~a ~a~n"
                                       (clause-head c)
                                       (clause-body c)
                                       (clause-frame-size c)
                                       (cons '<- (clause-source c))))
                             clauses)
                   (printf "~n"))))

(define-syntax <-
  (syntax-rules ()
    [(_ head body ...)
     (add-clause (car 'head) (length (cdr 'head)) (list 'head 'body ...))]))

; interpreter core functions

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
  (let ([head (clause-head clause)]
        [body (clause-body clause)]
        [frame (make-vector (clause-frame-size clause))])
    (let ([new-lenv (head goal frame lenv)])
      (if new-lenv
          (prove-goal-lst body
                          frame
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

(define (prove-goal-lst goal-lst frame lenv sk fk cutk)
  (if (null? goal-lst)
      (sk lenv fk)
      (let ([goal ((car goal-lst) frame)]
            [others (cdr goal-lst)])
        (cond
          [(eq? '! goal)
           (prove-goal-lst others frame lenv sk cutk cutk)]
          [(null? others)
           (prove-goal goal lenv sk fk)]
          [else
           (prove-goal goal
                       lenv
                       (lambda (lenv2 fk2)
                         (prove-goal-lst others frame lenv2 sk fk2 cutk))
                       fk)]))))

; top-level-solve and helpers

(define (simplify-term orig-term subst)
  (let ([term (deref orig-term subst)])
    (cond
      [(pair? term)
       (cons (simplify-term (car term) subst)
             (simplify-term (cdr term) subst))]
      [(var? term)
       (var-name term)]
      [else
       term])))

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

(define (rewrite-vars-cps term env k)
  (cond
    [(eq? '? term)
     (k (var (gensym term)) env)]
    [(var-src? term)
     (let ([binding (assq term env)])
       (if binding
           (cdr binding)
           (let ([new-var (var term)])
             (k new-var (cons (cons term new-var) env)))))]
    [(pair? term)
     (rewrite-vars-cps (car term)
                       env
                       (lambda (new-car env2)
                         (rewrite-vars-cps (cdr term)
                                           env2
                                           (lambda (new-cdr env3)
                                             (k (cons new-car new-cdr) env3)))))]
    [else
     (k term env)]))

(define (rewrite-vars term)
  (rewrite-vars-cps term '() (lambda (new-term env2) new-term)))

(define (more-answers?)
  (printf "?")
  (let ([response (read-line)])
    (cond
      [(string=? ";" response) #t]
      [(string=? "." response) #f]
      [else (more-answers?)])))

(define (top-level-solve goal-lst always-continue?)
  (let/ec exit
    (let* ([goal-lst* (rewrite-vars goal-lst)]
           [new-goal-lst (map (lambda (g)
                                (lambda (frame) g))
                              goal-lst*)]
           [top-frame (make-vector 0)]
           [succeeded-at-least-once? #f]
           [top-fk (lambda ()
                     (if succeeded-at-least-once?
                         (printf "Yes.~n")
                         (printf "No.~n"))
                     (exit))])
      (prove-goal-lst new-goal-lst
                      top-frame
                      '()
                      (lambda (lenv fk)
                        (set! succeeded-at-least-once? #t)
                        ;(printf "solved: ~n")
                        (for-each (lambda (var)
                                    (printf "~a = ~a~n" (var-name var) (simplify-term var lenv)))
                                  (reverse (collect-vars goal-lst* '())))
                        (cond
                          [(eq? fk top-fk)
                           (top-fk)]
                          [(or always-continue? (more-answers?))
                           (fk)]
                          [else
                           (top-fk)]))
                      top-fk
                      top-fk))))

(define-syntax ?-
  (syntax-rules ()
    [(_ g0 g ...) (top-level-solve '(g0 g ...) #f)]))

(define-syntax benchmark
  (syntax-rules ()
    [(_ g0 g ...) (time (top-level-solve '(g0 g ...) #t))]))


