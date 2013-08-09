#lang racket

; new imperative (destructive unification) version
;
; v0 - currently this is a copy of the purely functional version, vars represented as symbols


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
       (lambda (arg frame subst)
         (let ([arg (deref arg subst)])
           (cond
             [(pair? arg)
              (and (unify-car (car arg) frame)
                   (unify-cdr (cdr arg) frame))]
             [(var? arg) (set-binding! arg (head-copy frame))]
             [else #f]))))]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))






