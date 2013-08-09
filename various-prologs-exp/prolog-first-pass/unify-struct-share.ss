#lang scheme

(define (molecule exp level) (cons exp level))
(define (molecule-exp mol) (car mol))
(define (molecule-level mol) (cdr mol))

(define (var? x) (and (symbol? x)
                      (char=? (string-ref (symbol->string x) 0) #\?)))

; definitions of bound? and lookup should be refactored, to eliminate the extra call to assoc

; quick-and-dirty definition, need to open-code the lookup, rather than call
; molecule, and then immediately discard the new cons cell
(define (bound? x level subst)
  (assoc (molecule x level) subst))

; quick-and-dirty definition, need to open-code the lookup, rather than call
; molecule, and then immediately discard the new cons cell
(define (lookup var level subst)
  (cdr (assoc (molecule var level) subst)))

(define (extend-subst var var-level val val-level subst)
  (cons (cons (molecule var var-level) (molecule val val-level)) subst))

;(define (occurs-in? var x subst)
;  (cond
;    [(equal? var x) #t]
;    [(bound? x subst)
;     (occurs-in? var (lookup x subst))]
;    [(pair? x) (or (occurs-in? var (car x) subst)
;                   (occurs-in? var (cdr x) subst))]
;    [else #f]))

(define (unify-variable var var-level val val-level subst)
  (cond
    [(and (equal? var val) (= var-level val-level))
     subst]
    [(bound? var var-level subst)
     (let ([mol (lookup var var-level subst)])
       (unify (molecule-exp mol) (molecule-level mol)  val val-level subst))]
    [(and (var? val) (bound? val val-level subst))
     (let ([mol (lookup val val-level subst)])
       (unify var var-level (molecule-exp mol) (molecule-level mol) subst))]
    ;[(occurs-in? var val subst)
    ; #f]
    [else
     (extend-subst var var-level val val-level subst)]))

(define (unify x xi y yj [subst '()])
  (cond
    ; at this point x and y may by vars or structures (which may include vars),
    ; so need to compare the levels as well
    [(and (equal? x y) (= xi yj))
     subst]
    [(eq? subst #f)
     #f]
    [(var? x)
     (unify-variable x xi y yj subst)]
    [(var? y)
     (unify-variable y yj x xi subst)]
    [(and (pair? x) (pair? y))
     (unify (cdr x) xi (cdr y) yj
            (unify (car x) xi (car y) yj subst))]
    ; at this point, x and y are neither vars nor structures (which may include vars)
    [(equal? x y)
     subst]
    [else
     #f]))

'(unify '(?a 3 ?b) 1 '(1 ?b 3) 2)
'(unify '(?a 3 ?b) 1 '(1 ?b 3) 1)
'(unify '(?a 3 1) 1 '(?c ?b ?c) 2)
'(unify '(?a 3 1) 1 '(?c ?b ?c) 1)





