#lang scheme

; log_interp0: beginnings of a Prolog interpreter... based on Norvig's PAIP book.
; log_interp1: switch from "batch" to "incremental" backtracking (part 1)
; log_interp2: add ability to "fail" and retrieve additional solutions
; log_interp3: remove the tracing messages from log_interp2
; log_interp_cps0: initial changes to facilitate transformation to CPS; this is really a "pre-CPS" version
;                   Also changed fail to #f and no-bindings to '()
;                        -- rather than '() and '((#t . #t)) as needed in a Lisp where '() is the false value
;                   Added (minimal) support of anonymous variables,
;                         aligned with the Norvig PAIP interpreter (section 11.3)
; log_interp_cps1.ss: first real CPS version, using procedural CPS representation
; log_interp_cps2.ss: add support of cut

(require (only-in mzlib/compat
                  getprop
                  putprop))

(define fail #f)
(define no-bindings '())

(define (variable? x)
  (and (symbol? x)
       (char=? (string-ref (symbol->string x) 0) #\?)))

(define (get-binding var bindings)
  (assq var bindings))

(define (binding-val binding)
  (cdr binding))

;(define (extend-bindings var val bindings)
;  (cons (cons var val)
;        (if (eq? bindings no-bindings)
;            '()
;            bindings)))

(define (extend-bindings var val bindings)
  (cons (cons var val) bindings))

(define *occurs-check* (make-parameter #t))

(define (unify x y [bindings no-bindings])
  (cond
    [(eq? bindings fail) fail]
    [(eq? x y) bindings]
    [(variable? x) (unify-variable x y bindings)]
    [(variable? y) (unify-variable y x bindings)]
    [(and (pair? x) (pair? y))
     (unify (cdr x)
            (cdr y)
            (unify (car x) (car y) bindings))]
    [(equal? x y) bindings]
    [else fail]))

(define (unify-variable var x bindings)
  (cond
    [(get-binding var bindings)
     => (lambda (binding) (unify (binding-val binding) x bindings))]
    [(variable? x)
     (cond
       [(get-binding x bindings)
        => (lambda (binding) (unify var (binding-val binding) bindings))]
       [else (extend-bindings var x bindings)])]
    [(and (*occurs-check*) (occurs-check var x bindings))
     fail]
    [else
     (extend-bindings var x bindings)]))

(define (occurs-check var x bindings)
  (cond
    [(eq? var x) #t]
    [(and (variable? x) (get-binding x bindings))
     => (lambda (binding) (occurs-check var (binding-val binding) bindings))]
    [(pair? x)
     (or (occurs-check var (car x) bindings)
         (occurs-check var (cdr x) bindings))]
    [else #f]))

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

(define (clause-head clause)
  (car clause))

(define (clause-body clause)
  (cdr clause))

(define (get-clauses pred)
  (getprop pred 'clauses '()))

(define (predicate relation)
  (car relation))

(define *db-predicates* '())

(define (add-clause clause)
  (let ([pred (predicate (clause-head clause))])
    (unless (and (symbol? pred) (not (variable? pred)))
      (error '<- "invalid predicate name (symbol required), given ~a" pred))
    (unless (memq pred *db-predicates*)
      (set! *db-predicates* (cons pred *db-predicates*)))
    (putprop pred 'clauses
             (append (get-clauses pred) (list clause)))
    pred))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

(define-syntax <-
  (syntax-rules ()
    [(_ . clause)
     (add-clause (replace-?-variables 'clause))]))

(define (clear-db)
  (for-each clear-predicate *db-predicates*))

(define (clear-predicate predicate)
  (putprop predicate 'clauses '()))

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

; TO CPS
(define (search-choices goal clauses bindings other-goals cut-k)
  (define (inner lst k)
    (if (null? lst)
        (k fail)
        (let ([new-clause (rename-variables (car lst))])
          (prove-all (append (clause-body new-clause) other-goals)
                     (unify goal (clause-head new-clause) bindings)
                     cut-k
                     (lambda (test)
                       (if (eq? fail test)
                           (inner (cdr lst) k)
                           (k test)))))))
  (inner clauses cut-k))

; TO CPS
(define (prove goal bindings other-goals cut-k k)
  (if (eq? goal '!)
      (begin (printf "[TRACE] found cut~n")
             (prove-all other-goals bindings cut-k cut-k))
      (let ([clauses (get-clauses (predicate goal))])
        (if (procedure? clauses)
            (clauses (cdr goal) bindings other-goals cut-k k)
            (search-choices goal clauses bindings other-goals k)))))

; TO CPS
(define (prove-all goals bindings cut-k k)
  (printf "[TRACE] (prove-all goals bindings cut-k k)~n")
  (printf "[TRACE] goals = ")
  (pretty-print goals)
  (printf "[TRACE]~n")
  (printf "[TRACE] ")
  (if (eq? cut-k k)
      (printf "cut-k = k~n")
      (printf "cut-k != k~n"))
  (printf "[TRACE]~n")
  (cond
    [(eq? bindings fail)
     (k fail)]
    [(null? goals)
     (k bindings)]
    [else
     (prove (car goals) bindings (cdr goals) cut-k k)]))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

; TO CPS
;; this also serves as a prototype for primitives in CPS form
(define (show-prolog-vars vars bindings other-goals cut-k k)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~a" var (subst-bindings bindings var)))
                vars))
  (if (continue?)
      (k fail)
      (prove-all other-goals bindings cut-k k)))

(putprop 'show-prolog-vars 'clauses show-prolog-vars)

; TO-CPS
(define (top-level-prove goals)
  (let ([k (lambda (_)
             (printf "~nNo.")
             (void))])
    (prove-all `(,@goals (show-prolog-vars ,@(variables-in goals)))
               no-bindings
               k
               k)))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove (replace-?-variables 'goals))]))

(<- (likes Kim Robin))
(<- (likes Sandy Lee))
(<- (likes Sandy Kim))
(<- (likes Robin cats))
(<- (likes Sandy ?x) (likes ?x cats))
(<- (likes Kim ?x) (likes ?x Lee) (likes ?x Kim))
(<- (likes ?x ?x))

'(?- (likes Sandy ?who))

;(<- (goop 1))
;(?- (goop 1))
;(?- (goop ?a))

; helper predicates used for the zebra puzzle:

(<- (member ?item (?item . ?rest)))
(<- (member ?item (?x . ?rest)) (member ?item ?rest))

(<- (nextto ?x ?y ?list) (iright ?x ?y ?list))
(<- (nextto ?x ?y ?list) (iright ?y ?x ?list))

(<- (iright ?left ?right (?left ?right . ?rest)))
(<- (iright ?left ?right (?x . ?rest))
    (iright ?left ?right ?rest))

(<- (= ?x ?x))

; the zebra puzzle predicate

(<- (zebra ?h ?w ?z)
    ; 1
    (= ?h ((house norwegian ? ? ? ?)
           ?
           (house ? ? ? milk ?)
           ?
           ?))
    (member (house englishman ? ? ? red) ?h)
    (member (house spaniard dog ? ? ?) ?h)
    (member (house ? ? ? coffee green) ?h)
    (member (house ukranian ? ? tea ?) ?h)
    ; 6
    (iright (house ? ? ? ? ivory)
            (house ? ? ? ? green)
            ?h)
    (member (house ? snails winston ? ?) ?h)
    (member (house ? ? kools ? yellow) ?h)
    (nextto (house ? ? chesterfield ? ?)
            (house ? fox ? ? ?)
            ?h)
    (nextto (house ? ? kools ? ?)
            (house ? horse ? ? ?)
            ?h)
    ; 11
    (member (house ? ? luckystrike orange-juice ?) ?h)
    (member (house japanese ? parliaments ? ?) ?h)
    (nextto (house norwegian ? ? ? ?)
            (house ? ? ? ? blue)
            ?h)
    ; 14 -- the questions
    (member (house ?w ? ? water ?) ?h)
    (member (house ?z zebra ? ? ?) ?h)
    ; end
    )

(define (run-zebra)
  (?- (zebra ?houses ?water-drinker ?zebra-owner)))

(<- (p) (q) (r) ! (s) (t))
(<- (p) (s))
(<- (q))
(<- (r))
(<- (s))
(<- (t))






