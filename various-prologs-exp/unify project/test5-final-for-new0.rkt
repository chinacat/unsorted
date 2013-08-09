#lang racket

(define (var? term)
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


(struct set-var (name idx) #:transparent)
(struct ref-var (name idx) #:transparent)

(define (pre-cps term as idx k)
  (cond
    [(var? term)
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

(define (make-term-copy term)
  (cond
    [(pair? term)
     (let ([car-copier (make-term-copy (car term))]
           [cdr-copier (make-term-copy (cdr term))])
       (lambda (frame)
         (cons (car-copier frame) (cdr-copier frame))))]
    [(set-var? term)
     (let ([name (set-var-name term)]
           [idx (set-var-idx term)])
       (lambda (frame)
         (let ([new-var (gensym name)])
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
           [head-copy (make-term-copy head)])
       (lambda (arg frame subst)
         (let ([arg (deref arg subst)])
           (cond
             [(pair? arg)
              (let ([s (unify-car (car arg) frame subst)])
                (and s (unify-cdr (cdr arg) frame s)))]
             [(var? arg) (extend-subst arg (head-copy frame) subst)]
             [else #f]))))]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))


