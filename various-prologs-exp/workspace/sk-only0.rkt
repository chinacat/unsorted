#lang racket

;; this version doesn't support cut -- boo
;; -- the implementation of 'once/1' at the end of this file is sort-of a prototype for 
;; implementing cut in this interpreter
;;
;; but, it follows the Cohen / Stickell / Norvig model, which uses SK only, and returns on failure
;; I want to fork the "new" interpreter to use this model, and then measure its performance on zebra
;;
;; without really intending to do so, this version happens to have little / no distinction between
;; shallow and deep backtracking -- though it is based on my shallow-backtracking interpreter

(define *database* (make-hash))

(define (get-clauses name arity)
  (hash-ref *database* (cons name arity) '()))

(define (add-clause name arity new-clause)
  (let* ([key (cons name arity)]
         [existing-clauses (hash-ref *database* key '())])
    (hash-set! *database* key (append existing-clauses (list new-clause)))))

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

(define (try-each goal clauses lenv sk)
  (let iter ([clauses clauses])
    (let ([new-clause (copy-clause (car clauses))]
          [other-clauses (cdr clauses)])
      (let ([new-lenv (unify goal (car new-clause) lenv)])
        (when new-lenv
          (prove-goal-lst (cdr new-clause)
                          new-lenv
                          sk))
        (when (pair? other-clauses)
          (iter other-clauses))))))

(define (prove-goal goal lenv sk)
  (let ([clauses (get-clauses (car goal) (length (cdr goal)))])
    (cond
      [(null? clauses)
       (error 'prove-goal "predicate ~a/~a not defined" (car goal) (length (cdr goal)))]
      [(procedure? clauses)
       (apply clauses lenv sk (cdr goal))]
      [else
       (try-each goal clauses lenv sk)])))

(define (prove-goal-lst goal-lst lenv sk)
  (cond
    [(null? goal-lst) (sk lenv)]
    [(null? (cdr goal-lst))
     (prove-goal (car goal-lst) lenv sk)]
    [else
     (prove-goal (car goal-lst)
                 lenv
                 (lambda (lenv2)
                   (prove-goal-lst (cdr goal-lst) lenv2 sk)))]))

(define (top-level-solve goal-lst)
  (prove-goal-lst goal-lst
                  '()
                  (lambda (lenv)
                    (printf "solved: ~n")
                    (for-each (lambda (var)
                                (printf "~a = ~a~n" var (simplify-term var lenv)))
                              (reverse (collect-vars goal-lst '())))))
  #f)

(define-syntax <-
  (syntax-rules ()
    [(_ head body ...)
     (add-clause (car 'head) (length (cdr 'head)) (list 'head 'body ...))]))

(define-syntax ?-
  (syntax-rules ()
    [(_ g0 g ...) (top-level-solve '(g0 g ...))]))

(add-primitive 'pp 1
               (lambda (lenv sk term)
                 (printf "~a~n" (simplify-term term lenv))
                 (sk lenv)))

(add-primitive 'once 1
               (lambda (lenv sk goal)
                 (let/ec exit
                   (let ([new-goal (must-deref goal lenv 'once/1)])
                   (prove-goal new-goal
                               lenv
                               ; this implements the 'cut' in once
                               (lambda (lenv2)
                                 (sk lenv2)
                                 (exit)))))))




