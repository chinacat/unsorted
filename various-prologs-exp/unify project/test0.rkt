#lang racket

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
                  (extend-subst var val subst)))))))

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

;;; NOT COMPLETE
(define (make-unify y)
  (cond
    [(set-var? y)
     (lambda (x subst frame)
       (cond
         [(eq? x y)
          subst]
         [(var? x)
          (let ([binding (bound? x subst)])
            (if binding
                (begin (vector-set! frame (set-var-idx y) (cdr binding))
                       subst)
                (begin (vector-set! frame (set-var-idx y) x)
                       subst)))]
         [else
          (vector-set! frame (set-var-idx y) x)
          (extend-subst (gensym (set-var-name y)) x subst)]))]
    [else
     #f]))

; can improve by checking (statically) if a sub-term includes any variables,
;   if not, can treat the term as a constant
; could also optimize the case of (<term>), since the cdr is a '()
; once I am checking for constant terms, in the first cond clause, the
;   else clause can be an error reporting clause, for a malformed term.
;   (though it's probably a 'can-never-happen' clause, since the constant term
;    checking logic will follow the same pattern as the existing cond form below)
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








