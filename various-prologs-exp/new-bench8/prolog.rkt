#lang racket

;; TO DO:
;  - Experiment with the 'fast2' style dispatch w/ shallow backtracking
;    (passing the 'remaining clauses' to each clause-proc)
;    This would reduce the code generated at each call site
;   As long this doesn't slow things down, I would switch
;; Code change has been made (in new-bench8), but need to benchmark
;; 
;   - another possibility is to simplify the generated code for a clause to
;     remove support for 'shallow' backtracking.
;;
;  - functionality: support of cut, assert/retact, more primitives

(provide (all-defined-out))

; database-related definitions

(define *database* (make-hasheq))

(define (add-clause pred-name compiled-form source-form)
  (let ([existing-clauses (hash-ref *database* pred-name '())])
    (if (procedure? existing-clauses)
        (hash-set! *database* pred-name (list compiled-form))
        (hash-set! *database* pred-name (append existing-clauses (list compiled-form))))))

(define (add-primitive pred-name proc)
  (hash-set! *database* pred-name proc))

(define (get-clause pred-name)
  (hash-ref *database* pred-name
            (lambda ()
              (error 'get-clause "predicate ~a not defined" pred-name))))


; unification, and generating specialized unifiers and copiers

(define-struct unbound ())

(define *unbound* (make-unbound))

;(struct var (name val) #:transparent #:mutable)
(define next-id 0)

(define-syntax var
  (syntax-rules ()
    [(_ name val)
     (vector name #f val)]))
(define-syntax var?
  (syntax-rules ()
    [(_ term)
     (vector? term)]))
(define-syntax set-var-val!
  (syntax-rules ()
    [(_ var val)
     (vector-set! var 2 val)]))
(define-syntax var-val
  (syntax-rules ()
    [(_ var)
     (vector-ref var 2)]))
(define (var-mark-top-level! var)
  (vector-set! var 1 #t))

(define-syntax var-name
  (syntax-rules ()
    [(_ var)
     (let ([label (vector-ref var 1)])
       (cond
         [(eq? label #t)
          (vector-ref var 0)]
         [(eq? label #f)
          (let ([new-name (string->symbol (string-append (symbol->string (vector-ref var 0))
                                                         "_"
                                                         (number->string next-id)))])
            (set! next-id (+ 1 next-id))
            (vector-set! var 1 new-name)
            new-name)]
         [else
          label]))]))

(define (var-src? term)
  (and (symbol? term)
       (char=? #\? (string-ref (symbol->string term) 0))))

(define *trail* '())

(define (reset-trail old)
  (let iter ([t *trail*])
    (cond
      [(eq? t old)
       (set! *trail* old)]
      [else (set-var-val! (car t) *unbound*)
            (iter (cdr t))])))

(define (bound? x)
  (if (eq? *unbound* (var-val x))
      #f
      #t))

(define (deref exp)
  (if (and (var? exp) (bound? exp))
      (deref (var-val exp))
      exp))

(define (set-binding! var val)
  (set! *trail* (cons var *trail*))
  (set-var-val! var val)
  #t)

(define (unify! x y)
  (let ([x (deref x)]
        [y (deref y)])
    (cond
      [(eq? x y)
       #t]
      [(var? x)
       (set-binding! x y)]
      [(var? y)
       (set-binding! y x)]
      [(and (pair? x) (pair? y))
       (and (unify! (car x) (car y)) (unify! (cdr x) (cdr y)))]
      [(equal? x y)
       #t]
      [else
       #f])))

(define-for-syntax (annotate-term stx)
  (define (already-seen? var as)
    (cond
      [(null? as)
       #f]
      [(eq? (syntax-e var) (syntax-e (caar as)))
       (car as)]
      [else
       (already-seen? var (cdr as))]))
  (define (cps term as idx k)
    (syntax-case term ()
      [(lft . rgt)
       (cps #'lft
            as
            idx
            (lambda (new-lft as2 idx2)
              (cps #'rgt
                   as2
                   idx2
                   (lambda (new-rgt as3 idx3)
                     (k #`(#,new-lft . #,new-rgt) as3 idx3)))))]
      [id
       (identifier? #'id)
       (cond
         [(eq? '? (syntax-e #'id))
          (k #'($anon-var$) as idx)]
         [(char=? #\? (string-ref (symbol->string (syntax-e #'id)) 0))
          (let ([seen? (already-seen? #'id as)])
            (if seen?
                (k #`($ref-var$ id #,(cdr seen?)) as idx)
                (k #`($set-var$ id #,idx)
                   (cons (cons #'id idx) as)
                   (+ idx 1))))]
         [else
          (k #'id as idx)])]
      [any
       (k #'any as idx)]))
  (cps stx '() 0
       (lambda (new-term as idx)
         (values new-term (map car as)))))

(define-syntax (gen-copy stx)
  (syntax-case stx ($anon-var$ $ref-var$ $set-var$)
    [(_ ($anon-var$))
     #'(var '? *unbound*)]
    [(_ ($set-var$ name idx))
     #'(let ([new-var (var 'name *unbound*)])
         (set! name new-var)
         new-var)]
    [(_ ($ref-var$ name idx))
     #'name]
    [(_ (lft . rgt))
     #'(cons (gen-copy lft) (gen-copy rgt))]
    [(_ const)
     #''const]))

(define-syntax (gen-unify stx)
  (with-syntax ([reg (car (generate-temporaries #'(r)))])
    (syntax-case stx ($anon-var$ $ref-var$ $set-var$)
      [(_ arg ())
       #'(let ([reg (deref arg)])
           (cond
             [(null? reg) #t]
             [(var? reg) (set-binding! reg '())]
             [else #f]))]
      [(_ arg ($anon-var$))
       #'#t]
      [(_ arg ($set-var$ name idx))
       #'(begin (set! name (deref arg))
                #t)]
      [(_ arg ($ref-var$ name idx))
       #'(unify! name arg)]
      [(_ arg (lft . rgt))
       #'(let ([reg (deref arg)])
           (cond
             [(pair? reg)
              (and (gen-unify (car reg) lft)
                   (gen-unify (cdr reg) rgt))]
             [(var? reg) (set-binding! reg (gen-copy (lft . rgt)))]
             [else #f]))]
      [(_ arg constant)
       #'(let ([reg (deref arg)])
           (cond
             [(equal? 'constant reg) #t]
             [(var? reg) (set-binding! arg 'constant)]
             [else #f]))])))

(define-for-syntax (goal->predicate-name goal)
  (syntax-case goal ()
    [(functor arg ...)
     (string->symbol (string-append (symbol->string (syntax-e #'functor))
                                    "/"
                                    (number->string (length (syntax->list #'(arg ...))))))]))

(define-syntax (gen-test-head stx)
  (syntax-case stx ()
    [(_ ((pat formal) ...))
     #'(and (gen-unify formal pat) ...)]))

(define (executable-clauses name)
  (let ([clauses (get-clause name)])
    (if (procedure? clauses)
        (list clauses)
        clauses)))

(define-syntax (gen-call stx)
  (syntax-case stx ()
    [(_ sk fk (functor arg ...))
     (let ([pred-name (goal->predicate-name #'(functor arg ...))])
       (with-syntax ([(temp ...) (generate-temporaries #'(arg ...))])
         #`(let ([clauses (executable-clauses '#,pred-name)])
             ((car clauses) (cdr clauses) sk fk (gen-copy arg) ...))))]))

(define-syntax (gen-goal-seq stx)
  (syntax-case stx ()
    [(_ sk fk ())
     #'(sk fk)]
    [(_ sk fk (g))
     #'(gen-call sk fk g)]
    [(_ sk fk (g0 g ...))
     #'(gen-call (lambda (fk2) (gen-goal-seq sk fk2 (g ...)))
                 fk
                 g0)]))

(define-for-syntax (analyze-head-pats pats formals vars)
  (define (collect-simple-pats pats formals acc-pats acc-formals acc-complex-formals)
    (if (null? pats)
        (values (reverse acc-pats) (reverse acc-complex-formals) (reverse acc-formals))
        (syntax-case (car pats) ($set-var$)
          [($set-var$ name idx)
           (collect-simple-pats (cdr pats)
                                (cdr formals)
                                acc-pats
                                (cons #'name acc-formals)
                                acc-complex-formals)]
          [_
           (collect-simple-pats (cdr pats)
                                (cdr formals)
                                (cons (car pats) acc-pats)
                                (cons (car formals) acc-formals)
                                (cons (car formals) acc-complex-formals))])))
  (let-values ([(complex-pats complex-formals new-formals)
                (collect-simple-pats pats formals '() '() '())])
    (values complex-pats
            complex-formals
            new-formals
            (filter (lambda (v) (not (syntax-var-already-seen? v new-formals)))
                    vars))))

(define-syntax (<- stx)
  (syntax-case stx ()
    [(_ term goal ...)
     (let-values ([(new-clause raw-vars) (annotate-term #'(term goal ...))]
                  [(pred-name) (goal->predicate-name #'term)])
       (syntax-case new-clause ()
         [((functor pat ...) g ...)
          (let ([raw-formals (generate-temporaries #'(pat ...))])
            (let-values ([(complex-pats complex-formals new-formals bound-vars)
                          (analyze-head-pats (syntax->list #'(pat ...))
                                             raw-formals
                                             raw-vars)])
              (with-syntax ([(p ...) complex-pats]
                            [(cf ...) complex-formals]
                            [(f ...) new-formals]
                            [(v ...) bound-vars])
                #`(add-clause '#,pred-name
                              (lambda (others sk fk f ...)
                                (let ([v #f] ...
                                      [old-trail *trail*])
                                  (cond
                                    [(gen-test-head ((p cf) ...))
                                     (gen-goal-seq sk
                                                   (if (pair? others)
                                                       (lambda ()
                                                         (reset-trail old-trail)
                                                         ((car others) (cdr others) sk fk f ...))
                                                       fk)
                                                   (g ...))]
                                    [(pair? others)
                                     (reset-trail old-trail)
                                     ((car others) (cdr others) sk fk f ...)]
                                    [else
                                     (fk)])))
                              '(term goal ...)))))]))]))

(define (top-fk)
  (reset-trail '())
  (printf "No.~n"))

(define (top-sk fk)
  (if (eq? fk top-fk)
      (printf "Yes.~n")
      (fk)))

(define-for-syntax (src-var? term)
  (if (symbol? term)
      (if (eq? '? term)
          #f
          (char=? #\? (string-ref (symbol->string term) 0)))
      #f))

(define-for-syntax (syntax-var-already-seen? var as)
  (cond
    [(null? as)
     #f]
    [(eq? (syntax-e var) (syntax-e (car as)))
     as]
    [else
     (syntax-var-already-seen? var (cdr as))]))

(define-for-syntax (collect-src-vars term)
  (define (walk term already-seen)
    (syntax-case term ()
      [(lft . rgt)
       (let ([vars2 (walk #'lft already-seen)])
         (walk #'rgt vars2))]
      [id
       (identifier? #'id)
       (cond
         [(src-var? (syntax-e #'id))
          (if (syntax-var-already-seen? #'id already-seen)
              already-seen
              (cons #'id already-seen))]
         [else
          already-seen])]
      [any
       already-seen]))
  (walk term '()))

(define (simplify-term orig-term)
  (let ([term (deref orig-term)])
    (cond
      [(pair? term)
       (cons (simplify-term (car term))
             (simplify-term (cdr term)))]
      [(var? term)
       (var-name term)]
      [else
       term])))

(define (more-answers?)
  (printf "?")
  (let ([response (read-line)])
    (cond
      [(string=? ";" response) #t]
      [(string=? "." response) #f]
      [else (more-answers?)])))

(add-primitive '*interactions*/1
               (lambda (others sk fk vars)
                 (for-each var-mark-top-level! vars)
                 (for-each (lambda (var)
                             (printf "~a = ~a~n" (var-name var) (simplify-term var)))
                           vars)
                 (cond
                   [(eq? fk top-fk)
                    (sk fk)]
                   [(more-answers?)
                    (fk)]
                   [else
                    (sk top-fk)])))

(add-primitive '*always*/1
               (lambda (others sk fk vars)
                 (for-each var-mark-top-level! vars)
                 (for-each (lambda (var)
                             (printf "~a = ~a~n" (var-name var) (simplify-term var)))
                           vars)
                 (cond
                   [(eq? fk top-fk)
                    (sk fk)]
                   [else
                    (fk)])))

(define-syntax (?- stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let ([src-vars (collect-src-vars #'(term0 term ...))])
       (let-values ([(new-term-lst vars)
                     (annotate-term #`(term0 term ... (*interactions* #,src-vars)))])
         (with-syntax ([(g ...) new-term-lst]
                       [(v ...) vars])
           #`(let ([v #f] ...)
               (gen-goal-seq top-sk top-fk (g ...))))))]))

;; cpu-time : (() -> any) -> integer
(define (cpu-time thunk)
  (let-values (([result cpu real gc] (time-apply thunk null)))
    cpu))

;; (() -> any) -> (vectorof integer)
(define (benchmark-time* thunk count)
  (collect-garbage)
  (collect-garbage)
  (collect-garbage)
  (let ([timings (sort (for/list ([i (in-range count)])
                         (begin0 (cpu-time thunk)
                                 (collect-garbage)
                                 (collect-garbage)
                                 (collect-garbage)))
                       <)])
    (values timings
            (exact->inexact (/ (for/sum ([i timings]) i) (length timings))))))

(define-syntax (benchmark stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let ([src-vars (collect-src-vars #'(term0 term ...))])
       (let-values ([(new-term-lst vars)
                     (annotate-term #`(term0 term ...))])
         (with-syntax ([(g ...) new-term-lst]
                       [(v ...) vars])
           #`(benchmark-time* (lambda ()
                                (let ([v #f] ...)
                                  (gen-goal-seq top-sk top-fk (g ...))))
                              10000))))]))




