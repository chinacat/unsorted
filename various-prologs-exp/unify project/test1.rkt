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

(define bound? assq)

(define (extend-subst var val subst)
  (cons (cons var val) subst))


(struct set-var (name idx) #:transparent)
(struct ref-var (name idx) #:transparent)

; this should check for invalid datum types, e.g. vectors, structs
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


;; v0, where both head and arg are terms
;(define (unify-head head arg subst)
;  (cond
;    [(equal? head arg) subst]
;    [(var? head) (unify-variable head arg subst)]
;    [(var? arg) (unify-variable arg head subst)]
;    [(pair? head)
;     (if (pair? arg)
;         (let ([s (unify (car head) (car arg) subst)])
;           (and s (unify (cdr head) (cdr arg) s)))
;         #f)]
;    [else #f]))


; v1, where both head and arg are terms
; restructure to make static vs. dynamic parts explicit
; not eq? test of pairs is important in the general unify, 
; but for head matching, the arg will never be eq? and so 
; that test is omitted
(define (unify-head head arg subst)
  (cond
    [(null? head)
     (cond
       [(null? arg) subst]
       [(var? arg) (unify-variable arg '() subst)]
       [else #f])]
    [(var? head)
     (cond
       [(eq? head arg) subst]
       [else (unify-variable head arg subst)])]
    [(not (pair? head))
     (cond
       [(equal? head arg) subst]
       [(var? arg) (unify-variable arg head subst)]
       [else #f])]
    [(pair? head)
     (cond
       [(pair? arg)
         (let ([s (unify-head (car head) (car arg) subst)])
           (and s (unify-head (cdr head) (cdr arg) s)))]
       [(var? arg) (unify-variable arg head subst)]
       [else #f])]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))







