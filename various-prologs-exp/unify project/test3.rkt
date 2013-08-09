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

; lazy person's option -- need to 'uncurry' make-copy-term here instead
(define (copy-term template frame)
  ((make-term-copy template) frame))


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


;; v1, where both head and arg are terms
;; restructure to make static vs. dynamic parts explicit
;; not eq? test of pairs is important in the general unify, 
;; but for head matching, the arg will never be eq? and so 
;; that test is omitted
;(define (unify-head head arg subst)
;  (cond
;    [(null? head)
;     (cond
;       [(null? arg) subst]
;       [(var? arg) (unify-variable arg '() subst)]
;       [else #f])]
;    [(var? head)
;     (cond
;       [(eq? head arg) subst]
;       [else (unify-variable head arg subst)])]
;    [(not (pair? head))
;     (cond
;       [(equal? head arg) subst]
;       [(var? arg) (unify-variable arg head subst)]
;       [else #f])]
;    [(pair? head)
;     (cond
;       [(pair? arg)
;         (let ([s (unify-head (car head) (car arg) subst)])
;           (and s (unify-head (cdr head) (cdr arg) s)))]
;       [(var? arg) (unify-variable arg head subst)]
;       [else #f])]
;    [else (error 'unify-head "unexpected head datum, given ~a" head)]))

; v3 -- head is now a template (the result of pre)
; updated compared to v2, to deref arg, so that more static tests can be used
(define (unify-head head arg frame subst)
  (cond
    [(null? head)
     (let ([arg (deref arg subst)])
       (cond
         [(null? arg) subst]
         [(var? arg) (extend-subst arg '() subst)]
         [else #f]))]
    [(set-var? head)
     (let ([idx (set-var-idx head)])
       (vector-set! frame idx (deref arg subst))
       subst)]
    [(ref-var? head)
     (let ([idx (ref-var-idx head)])
       (unify (vector-ref frame idx) arg subst))]
    [(not (pair? head))
     (let ([arg (deref arg subst)])
       (cond
         [(equal? head arg) subst]
         [(var? arg) (extend-subst arg head subst)]
         [else #f]))]
    [(pair? head)
     (let ([arg (deref arg subst)])
       (cond
         [(pair? arg)
          (let ([s (unify-head (car head) (car arg) frame subst)])
            (and s (unify-head (cdr head) (cdr arg) frame s)))]
         [(var? arg) (extend-subst arg (copy-term head frame) subst)]
         [else #f]))]
    [else (error 'unify-head "unexpected head datum, given ~a" head)]))

;; specialized version, where term cannot be a variable
;;;; should do some testing, e.g. in context of zebra to check that this really
;;;; is faster than the more general unify-variable
;(define (unify-var-to-term var term subst)
;  (let ([var (deref var subst)])
;    (if (var? var)
;        (extend-subst var term subst)
;        (unify var term subst))))



'(unify-head (list 'q (list 'p (set-var '?x 0) (set-var '?y 1)) (list 'p (ref-var '?y 1) (ref-var '?x 0)))
             '(q ?z ?z)
             (make-vector 2)
             '())

;; should enhance this test case to include ?x and/or ?y elsewhere in the term, to validate 'ref' functionality
'(pre '(?a (1 ?x 2 ?y 3) ?b))
'(unify-head (list (set-var '?a 0) (list 1 (set-var '?x 1) 2 (set-var '?y 2) 3) (set-var '?b 3))
             '(55 ?z 66)
             (make-vector 4)
             '())

'(pre '(?a ?b ?c ?b ?a))
'(unify-head (list (set-var '?a 0) (set-var '?b 1) (set-var '?c 2) (ref-var '?b 1) (ref-var '?a 0))
             '(1 (2 ?a) 3 (?z 5) 1)
             (make-vector 3)
             '())

