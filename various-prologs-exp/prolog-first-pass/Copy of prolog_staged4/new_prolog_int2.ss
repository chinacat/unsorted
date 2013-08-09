#lang scheme

; stage 0: naive, unstaged interpreter
; stage 0a: turn off occurs check; cuts time by about half

(require (only-in mzlib/compat
                  getprop
                  putprop))

(provide <- ?- benchmark)

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

;(define (unifier x y)
;  (subst-bindings (unify x y) x))

;(define (clause-head clause)
;  (car clause))

;(define (clause-body clause)
;  (cdr clause))

(define (get-clauses pred)
  (getprop pred 'clauses '()))

(define (predicate relation)
  (car relation))

(define *db-predicates* '())

(define (add-clause clause)
  (let ([pred (predicate (clause-head clause))])
    (unless (and (symbol? pred) (not (var-text? pred)))
      (error '<- "invalid predicate name (symbol required), given ~a" pred))
    (unless (memq pred *db-predicates*)
      (set! *db-predicates* (cons pred *db-predicates*)))
    (putprop pred 'clauses
             (append (get-clauses pred) (list (analyze-clause clause))))
    (void)))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

(define (clear-db)
  (for-each clear-predicate *db-predicates*))

(define (clear-predicate predicate)
  (putprop predicate 'clauses '()))

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

(define (new-activation-frame num-vars)
  (build-vector num-vars
                (lambda (i)
                  (make-variable '? (new-counter)))))

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

(define (prove-goals goal-list new-frame success-cont cut-cont failure-cont)
  (cond
    [(null? goal-list)
     (success-cont failure-cont)]
    [(eq? '! (car goal-list))
     (if (pair? (cdr goal-list))
         (prove-goals (cdr goal-list) new-frame success-cont cut-cont cut-cont)
         (success-cont cut-cont))]
    [(null? (cdr goal-list))
     (search-choices (instantiate (car goal-list) new-frame)
                     success-cont
                     failure-cont)]
    [else (search-choices (instantiate (car goal-list) new-frame)
                          (lambda (fc2)
                            (prove-goals (cdr goal-list) new-frame success-cont cut-cont fc2))
                          failure-cont)]))

(define (search-choices goal success-cont failure-cont)
  (let ([goal-args (cdr goal)]
        [clauses (get-clauses (predicate goal))])
    (cond
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
     (add-clause (preprocess-clause (replace-?-variables 'clause)))]))

(define (analyze-clause clause)
  (let ([args (cdr (clause-head clause))]
        [body (clause-body clause)]
        [num-vars (clause-num-vars clause)])
    (lambda (goal-args success-cont cut-cont failure-cont)
      (let ([new-frame (new-activation-frame num-vars)])
        (let ([result (unify! goal-args (instantiate args new-frame))])
          (if result
              (prove-goals body
                           new-frame
                           success-cont
                           cut-cont
                           failure-cont)
              (failure-cont)))))))



