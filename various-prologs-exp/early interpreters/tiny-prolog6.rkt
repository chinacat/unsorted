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

(define (try-each goal clauses lenv fg cs sk fk)
  (cond
    [(null? (cdr clauses))
     (try-goal goal
               (car clauses)
               lenv
               fg
               cs
               sk
               fk
               fk)]
    [else
     (try-goal goal
               (car clauses)
               lenv
               fg
               cs
               sk
               (lambda () (try-each goal (cdr clauses) lenv fg cs sk fk))
               fk)]))

(define (try-goal goal clause lenv fg cs sk fk cutk)
  (let ([new-clause (copy-clause clause)])
    (let ([new-lenv (unify goal (car new-clause) lenv)])
      (if new-lenv
          (awaken-fg new-lenv
                     lenv
                     fg
                     cs
                     (lambda (lenv2 fg2 cs2 fk2)
                       (prove-goal-lst (cdr new-clause)
                                       lenv2
                                       fg2
                                       cs2
                                       sk
                                       fk2
                                       cutk))
                     fk)
          (fk)))))

(define (prove-goal goal lenv fg cs sk fk)
  (let ([clauses (get-clauses (car goal) (length (cdr goal)))])
    (cond
      [(null? clauses)
       (error 'prove-goal "predicate ~a/~a not defined" (car goal) (length (cdr goal)))]
      [(procedure? clauses)
       (apply clauses lenv fg cs sk fk (cdr goal))]
      [else
       (try-each goal clauses lenv fg cs sk fk)])))

(define (prove-goal-lst goal-lst lenv fg cs sk fk cutk)
  (cond
    [(null? goal-lst) (sk lenv fg cs fk)]
    [(eq? '! (car goal-lst))
     (prove-goal-lst (cdr goal-lst) lenv fg cs sk cutk cutk)]
    [(null? (cdr goal-lst))
     (prove-goal (car goal-lst) lenv fg cs sk fk)]
    [else
     (prove-goal (car goal-lst)
                 lenv
                 fg
                 cs
                 (lambda (lenv2 fg2 cs2 fk2)
                   (prove-goal-lst (cdr goal-lst) lenv2 fg2 cs2 sk fk2 cutk))
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
                      '()
                      '()
                      (lambda (lenv fg cs fk)
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
               (lambda (lenv fg cs sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'call/1)])
                   (prove-goal new-goal lenv fg cs sk fk))))

(add-primitive 'not 1
               (lambda (lenv fg cs sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'not/1)])
                   (prove-goal new-goal
                               lenv
                               fg
                               cs
                               (lambda (lenv2 fg2 cs2 fk2)
                                 (fk))
                               (lambda ()
                                 (sk lenv fg cs fk))))))

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

; VERY IMPORTANT: when I turn this into a built-in, I need to ensure 
; that the built-in version awakens frozen goals
(<- (= ?a ?a))
(<- (fail) (= 1 0))

(<- (append (?x . ?y) ?z (?x . ?w)) (append ?y ?z ?w))
(<- (append () ?x ?x))

;(<- (once ?g) (call ?g) !)
(<- (p 1))
(<- (p 2))
(<- (p 3))

(add-primitive 'once 1
               (lambda (lenv fg cs sk fk goal)
                 (let ([new-goal (must-deref goal lenv 'call/1)])
                   (prove-goal new-goal
                               lenv
                               fg
                               cs
                               ; this implements the 'cut' in once
                               (lambda (lenv2 fg2 cs2 fk2)
                                 (sk lenv2 fg2 cs2 fk))
                               fk))))

(add-primitive 'write 1
               (lambda (lenv fg cs sk fk term)
                 (printf "~a" (simplify-term term lenv))
                 (sk lenv fg cs fk)))

(add-primitive 'nl 0
               (lambda (lenv fg cs sk fk)
                 (newline)
                 (sk lenv fg cs fk)))

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
               (lambda (lenv fg cs sk fk src-term new-term)
                 (let ([new-lenv (unify (deref-copy src-term lenv) new-term lenv)])
                   (if new-lenv
                       (sk new-lenv fg cs fk)
                       (fk)))))

(define assertz-impl
  (lambda (lenv fg cs sk fk term)
    (let* ([new-term (deref-copy term lenv)]
           [new-clause (if (eq? '<- (car new-term))
                           (cdr new-term)
                           (list new-term))]
           [new-head (car new-clause)]
           [functor (car new-head)]
           [arity (length (cdr new-head))])
      (add-clause functor arity new-clause)
      (sk lenv fg cs fk))))

(add-primitive 'assert 1
               assertz-impl)

(add-primitive 'asserta 1
               (lambda (lenv fg cs sk fk term)
                 (let* ([new-term (deref-copy term lenv)]
                        [new-clause (if (eq? '<- (car new-term))
                                        (cdr new-term)
                                        (list new-term))]
                        [new-head (car new-clause)]
                        [functor (car new-head)]
                        [arity (length (cdr new-head))])
                   (add-clause/front functor arity new-clause)
                   (sk lenv fg cs fk))))

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
  (lambda (lenv fg cs sk fk head)
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
               fg
               cs
               (lambda ()
                 (retract-impl lenv fg cs sk fk head)))])))))

(add-primitive 'retract 1
               retract-impl)


(<- (member ?x (?x . ?l)))
(<- (member ?x (?y . ?l)) (member ?x ?l))

; keep for now, but unused -- what I really need is the list of names
(define (prefix-bindings new-lenv old-lenv)
  (if (eq? new-lenv old-lenv)
      '()
      (cons (car new-lenv)
            (prefix-bindings (cdr new-lenv) old-lenv))))

(define (prefix-bindings/names new-lenv old-lenv)
  (if (eq? new-lenv old-lenv)
      '()
      (cons (caar new-lenv)
            (prefix-bindings/names (cdr new-lenv) old-lenv))))

;(define (can-awaken? var lenv)
;  (not (eq? var (deref var lenv))))

(define (select-frozen-goals touched-vars lst)
  (if (null? lst)
      (values '() '())
      (let-values ([(rst-awake rst-freeze)
                    (select-frozen-goals touched-vars (cdr lst))])
        (if (member (caar lst) touched-vars)
            (values (cons (cdar lst) rst-awake)
                    rst-freeze)
            (values rst-awake
                    (cons (car lst) rst-freeze))))))

; Notes:
; - prefix-bindings is not a sufficient condition to detect goals that need to be awakened
; - iterating through the list of frozen goals and calling deref on each delayed
;   variable would be correct semantically, but not efficient at all
(define (awaken-fg new-lenv old-lenv fg cs sk fk)
  (let-values ([(goals new-fg) (select-frozen-goals (prefix-bindings/names new-lenv old-lenv) fg)])
    (if (null? goals)
        (sk new-lenv fg cs fk)
        (prove-goal-lst goals
                        new-lenv
                        new-fg
                        cs
                        sk
                        fk
                        fk))))

; should the 're-freeze' below freeze with the original var, or with val (the deref'd var)???
(add-primitive 'freeze 2
               (lambda (lenv fg cs sk fk var goal)
                 (let ([val (deref var lenv)])
                   (if (var? val)
                       (sk lenv (cons (cons val `(freeze ,val ,goal)) fg) cs fk)
                       (let ([new-goal (must-deref goal lenv 'freeze/2)])
                         (prove-goal new-goal lenv fg cs sk fk))))))

(add-primitive 'delay 2
               (lambda (lenv fg cs sk fk var goal)
                 (let ([val (deref var lenv)])
                   (if (not (eq? var val))
                       (let ([new-goal (must-deref goal lenv 'delay/2)])
                         (prove-goal new-goal lenv fg cs sk fk))
                       (sk lenv (cons (cons var goal) fg) cs fk)))))

'(begin (define fg (list (cons '?a '(not (= ?a ?b)))
                         (cons '?b '(not (= ?a ?b)))
                         (cons '?c '(write ?c))
                         (cons '?d '(write ?d))))
        (select-frozen-goals '(?a ?c) fg))

(<- (pp ?t) (write ?t) (nl))

; freeze test cases
; (?- (= ?a 3) (freeze ?a (pp ?a)))
; (?- (freeze ?a (pp (out ?a))) (pp (out FOO)) (= ?a 3))
; (?- (freeze ?a (pp (out ?a))) (pp (out FOO)) (= ?a ?b))
; this should probably awaken (pp (out ?a)) but doesn't
; (?- (freeze ?a (pp (out ?a))) (pp (out FOO)) (= ?a ?b) (pp (out BAR)) (= ?b 3))
; this DEFINITELY should awaken (pp (out ?a)) but doesn't
; (?- (freeze ?a (pp (out ?a))) (pp (out FOO)) (= ?a ?b) (pp (out BAR)) (= ?a 3))
; (?- (freeze ?a (pp (out ?a))) (member ?a (1 2 3 4 5)))


