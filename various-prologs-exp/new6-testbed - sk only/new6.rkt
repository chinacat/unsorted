#lang racket

;; experimental version with success continuations only, in the style of the Stickell / Cohen / Norvig
;;   architecture
;;  This is a test to see if SK only has better performance, at least for 'pure' prolog.
;;  This test version does not support cut.

; new0 -- initial version of 'new' TinyProlog with the specialized copy and unify-head implementation
; new1 -- use structs instead of symbols to represent variables
; new2 -- add support of anonymous variables
; new3 -- small change to make-copy-term for the (<term> . null) case
; new4 -- version with destructive unification
; new5 -- eliminate some of the overhead for predicate calls, e.g. the (cons name arity) code
; new6 -- "optimize" shallow backtracking (seems to have little/no impact on performance, but
;         but objectively this version does less work on shallow vs. deep backtracking
;
; TO DO:
;         1. [DONE] Add support of anonymous variables
;         2. [DONE] Change the runtime representation of variables to be structs instead of symbols
;         3. Optimize make-copy-term, 
;              - to avoid copying 'constant' parts of the term
;              - [DONE] simplify copying of (<term> . null); no noticable perf. improvement, however
;         4. Turn variables which are 'set', but never referenced into anonymous variables

;(provide <-
;         ?-
;         benchmark
;         show-db
;         show-db/verbose)

(provide (all-defined-out))

; unification, and generating specialized unifiers and copiers

(define-struct unbound ())

(define *unbound* (make-unbound))

(struct var (name val) #:transparent #:mutable)

(define (var-src? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define *trail* '())

(define (reset-trail old)
  (cond
    [(null? *trail*)
     (void)]
    [(eq? *trail* old)
     (void)]
    [else (set-var-val! (car *trail*) *unbound*)
          (set! *trail* (cdr *trail*))
          (reset-trail old)]))

(define (bound? x) (not (eq? *unbound* (var-val x))))

(define (deref exp)
  (if (and (var? exp) (bound? exp))
      (deref (var-val exp))
      exp))

(define (set-binding! var val)
  (unless (eq? var val)
    (set! *trail* (cons var *trail*))
    (set-var-val! var val))
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
     (if (null? (cdr term))
         (let ([car-copier (make-copy-term (car term))])
           (lambda (frame)
             (cons (car-copier frame) '())))
         (let ([car-copier (make-copy-term (car term))]
               [cdr-copier (make-copy-term (cdr term))])
           (lambda (frame)
             (cons (car-copier frame) (cdr-copier frame)))))]
    [(anon-var? term)
     (lambda (frame)
       (var (gensym '?) *unbound*))]
    [(set-var? term)
     (let ([name (set-var-name term)]
           [idx (set-var-idx term)])
       (lambda (frame)
         (let ([new-var (var (gensym name) *unbound*)])
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
     (lambda (arg frame)
       (let ([arg (deref arg)])
         (cond
           [(null? arg) #t]
           [(var? arg) (set-binding! arg '())]
           [else #f])))]
    [(anon-var? head)
     (lambda (arg frame)
       #t)]
    [(set-var? head)
     (let ([idx (set-var-idx head)])
       (lambda (arg frame)
         (vector-set! frame idx (deref arg))
         #t))]
    [(ref-var? head)
     (let ([idx (ref-var-idx head)])
       (lambda (arg frame)
         (unify! (vector-ref frame idx) arg)))]
    [(not (pair? head))
     (let ([constant head])
       (lambda (arg frame)
         (let ([arg (deref arg)])
           (cond
             [(equal? constant arg) #t]
             [(var? arg) (set-binding! arg constant)]
             [else #f]))))]
    [(pair? head)
     (let ([unify-car (make-unify-head (car head))]
           [unify-cdr (make-unify-head (cdr head))]
           [head-copy (make-copy-term head)])
       (lambda (arg frame)
         (let ([arg (deref arg)])
           (cond
             [(pair? arg)
              (and (unify-car (car arg) frame)
                   (unify-cdr (cdr arg) frame))]
             [(var? arg) (set-binding! arg (head-copy frame))]
             [else #f]))))]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))


; clause and database representation

(struct primitive (fun) #:transparent)
(struct clause (head body frame-size source) #:transparent)

(define *database* (make-hasheq))

(define (get-clauses name)
  (hash-ref *database* name '()))

(define (rewrite-goal goal)
  (let* ([arity (length (cdr goal))])
    (cons (string->symbol (string-append (symbol->string (car goal))
                                         "/"
                                         (number->string arity)))
          (cdr goal))))

(define (intern-clause new-clause-source)
  (let-values ([(pre-clause frame-size) (pre (map rewrite-goal new-clause-source))])
    (clause (make-unify-head (car pre-clause))
            (map make-copy-term (cdr pre-clause))
            frame-size
            new-clause-source)))

(define (add-clause functor arity new-clause-source)
  (let ([name (string->symbol (string-append (symbol->string functor)
                                             "/"
                                             (number->string arity)))])
    (let* ([existing-clauses (hash-ref *database* name '())])
      (let ([new-clause (intern-clause new-clause-source)])
        (hash-set! *database*
                   name
                   (append existing-clauses (list new-clause)))))))

(define (add-primitive name arity proc)
  (hash-set! *database*
             (string->symbol (string-append (symbol->string name)
                                            "/"
                                            (number->string arity)))
             (primitive proc)))

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
    [(_ (functor arg ...) body ...)
     (add-clause 'functor (length '(arg ...)) (list '(functor arg ...) 'body ...))]))

; interpreter core functions

(define (try-each goal clauses sk)
  (let ([clause (car clauses)]
        [other-clauses (cdr clauses)])
    (let ([head (clause-head clause)]
          [body (clause-body clause)]
          [frame (make-vector (clause-frame-size clause))])
      (let ([old-trail *trail*])
        (when (head goal frame)
          (prove-goal-lst body
                          frame
                          sk))
        (when (pair? other-clauses)
          (reset-trail old-trail)
          (try-each goal other-clauses sk))))))

(define (prove-goal goal sk)
  (let ([clauses (get-clauses (car goal))])
    (cond
      [(null? clauses)
       (error 'prove-goal "predicate ~a/~a not defined" (car goal) (length (cdr goal)))]
      [(procedure? clauses)
       (apply clauses sk (cdr goal))]
      [else
       (try-each goal clauses sk)])))

(define (prove-goal-lst goal-lst frame sk)
  (if (null? goal-lst)
      (sk)
      (let ([goal ((car goal-lst) frame)]
            [others (cdr goal-lst)])
        (cond
          [(null? others)
           (prove-goal goal sk)]
          [else
           (prove-goal goal
                       (lambda ()
                         (prove-goal-lst others frame sk)))]))))

; top-level-solve and helpers

(define (simplify-term orig-term)
  (let ([term (deref orig-term)])
    (cond
      [(pair? term)
       (cons (simplify-term (car term))
             (simplify-term (cdr term)))]
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
     (k (var (gensym term) *unbound*) env)]
    [(var-src? term)
     (let ([binding (assq term env)])
       (if binding
           (cdr binding)
           (let ([new-var (var term *unbound*)])
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
    (let* ([goal-lst* (rewrite-vars (map rewrite-goal goal-lst))]
           [new-goal-lst (map (lambda (g)
                                (lambda (frame) g))
                              goal-lst*)]
           [top-frame (make-vector 0)]
           [succeeded-at-least-once? #f])
      (prove-goal-lst new-goal-lst
                      top-frame
                      (lambda ()
                        (set! succeeded-at-least-once? #t)
                        (for-each (lambda (var)
                                    (printf "~a = ~a~n" (var-name var) (simplify-term var)))
                                  (reverse (collect-vars goal-lst* '())))
                        (unless (or always-continue? (more-answers?))
                          (reset-trail '())
                          (if succeeded-at-least-once?
                              (printf "Yes.~n")
                              (printf "No.~n"))
                          (exit)))))))

(define-syntax ?-
  (syntax-rules ()
    [(_ g0 g ...) (top-level-solve '(g0 g ...) #f)]))

(define-syntax benchmark
  (syntax-rules ()
    [(_ g0 g ...)
     (time (top-level-solve '(g0 g ...) #t))]))


