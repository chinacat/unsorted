#lang racket

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

(define (var name val)
  (vector name #f val))
(define var? vector?)
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

;(define (set-binding! var val)
;  (unless (eq? var val)
;    (set! *trail* (cons var *trail*))
;    (set-var-val! var val))
;  #t)

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
          (let ([seen? (assq (syntax-e #'id) as)])
            (if seen?
                (k #`($ref-var$ id #,(cdr seen?)) as idx)
                (k #`($set-var$ id #,idx)
                   (cons (cons (syntax-e #'id) idx) as)
                   (+ idx 1))))]
         [else
          (k #'id as idx)])]
      [any
       (k #'any as idx)]))
  (cps stx '() 0
       (lambda (new-term as idx)
         (values new-term idx))))

(define-syntax (gen-copy stx)
  (syntax-case stx ($anon-var$ $ref-var$ $set-var$)
    [(_ frame ($anon-var$))
     #'(var '? *unbound*)]
    [(_ frame ($set-var$ name idx))
     #'(let ([new-var (var 'name *unbound*)])
         (vector-set! frame idx new-var)
         new-var)]
    [(_ frame ($ref-var$ name idx))
     #'(vector-ref frame idx)]
    [(_ frame (lft . rgt))
     #'(cons (gen-copy frame lft) (gen-copy frame rgt))]
    [(_ frame const)
     #''const]))

(define-syntax (gen-unify stx)
  (syntax-case stx ($anon-var$ $ref-var$ $set-var$)
    [(_ arg frame ())
     #'(let ([arg (deref arg)])
         (cond
           [(null? arg) #t]
           [(var? arg) (set-binding! arg '())]
           [else #f]))]
    [(_ arg frame ($anon-var$))
     #'#t]
    [(_ arg frame ($set-var$ name idx))
     #'(begin (vector-set! frame idx (deref arg))
              #t)]
    [(_ arg frame ($ref-var$ name idx))
     #'(unify! (vector-ref frame idx) arg)]
    [(_ arg frame (lft . rgt))
     #'(let ([arg (deref arg)])
         (cond
           [(pair? arg)
            (let ([arg-car (car arg)]
                  [arg-cdr (cdr arg)])
              (and (gen-unify arg-car frame lft)
                   (gen-unify arg-cdr frame rgt)))]
           [(var? arg) (set-binding! arg (gen-copy frame (lft . rgt)))]
           [else #f]))]
    [(_ arg frame constant)
     #'(let ([arg (deref arg)])
         (cond
           [(equal? 'constant arg) #t]
           [(var? arg) (set-binding! arg 'constant)]
           [else #f]))]))

(define-for-syntax (goal->predicate-name goal)
  (syntax-case goal ()
    [(functor arg ...)
     (string->symbol (string-append (symbol->string (syntax-e #'functor))
                                    "/"
                                    (number->string (length (syntax->list #'(arg ...))))))]))

(define-syntax (gen-test-head stx)
  (syntax-case stx ()
    [(_ frame ((pat formal) ...))
     #'(and (gen-unify formal frame pat) ...)]))

(define-syntax (gen-call stx)
  (syntax-case stx ()
    [(_ sk fk frame (functor arg ...))
     (let ([pred-name (goal->predicate-name #'(functor arg ...))])
       (with-syntax ([(temp ...) (generate-temporaries #'(arg ...))])
         #`(let ([clauses (get-clause '#,pred-name)]
                 [temp (gen-copy frame arg)] ...
                 [old-trail *trail*])
             (if (procedure? clauses)
                 (clauses sk fk temp ...)
                 (let iter ([clauses clauses])
                   (if (null? (cdr clauses))
                       ((car clauses) sk fk temp ...)
                       ((car clauses) sk
                                      (lambda ()
                                        (reset-trail old-trail)
                                        (iter (cdr clauses)))
                                      temp ...)))))))]))

(define-syntax (gen-goal-seq stx)
  (syntax-case stx ()
    [(_ sk fk frame ())
     #'(sk fk)]
    [(_ sk fk frame (g))
     #'(gen-call sk fk frame g)]
    [(_ sk fk frame (g0 g ...))
     #'(let ([sk2 (lambda (fk2) (gen-goal-seq sk fk2 frame (g ...)))])
         (gen-call sk2 fk frame g0))]))

(define-syntax (<- stx)
  (syntax-case stx ()
    [(_ term goal ...)
     (let-values ([(new-clause frame-size) (annotate-term #'(term goal ...))]
                  [(pred-name) (goal->predicate-name #'term)])
       (syntax-case new-clause ()
         [((functor pat ...) g ...)
          (with-syntax ([(formal ...) (generate-temporaries #'(pat ...))])
            #`(add-clause '#,pred-name
                          (lambda (sk fk formal ...)
                            (let ([frame (make-vector #,frame-size)])
                              (if (gen-test-head frame ((pat formal) ...))
                                  (gen-goal-seq sk fk frame (g ...))
                                  (fk))))
                          'term))]))]))

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
          (if (memq (syntax-e #'id) already-seen)
              already-seen
              (cons (syntax-e #'id) already-seen))]
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
               (lambda (sk fk vars)
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
               (lambda (sk fk vars)
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
       (let-values ([(new-term-lst frame-size)
                     (annotate-term #`(term0 term ... (*interactions* #,src-vars)))])
         (with-syntax ([(g ...) new-term-lst])
           #`(let ([frame (make-vector #,frame-size)])
               (gen-goal-seq top-sk top-fk frame (g ...))))))]))

;; cpu-time : (() -> any) -> integer
(define (cpu-time thunk)
  (let-values (([result cpu real gc] (time-apply thunk null)))
    cpu))

;; (() -> any) -> (vectorof integer)
(define (benchmark-time* thunk count)
  (collect-garbage)
  (collect-garbage)
  (collect-garbage)
  (sort (for/list ([i (in-range count)])
          (begin0 (cpu-time thunk)
                  (collect-garbage)
                  (collect-garbage)
                  (collect-garbage)))
        <))

;(define-syntax (benchmark stx)
;  (syntax-case stx ()
;    [(_ term0 term ...)
;     (let-values ([(new-term-lst frame-size) (annotate-term #`(term0 term ...))])
;       (with-syntax ([(g ...) new-term-lst])
;         #`(benchmark-time* (lambda ()
;                              (let ([frame (make-vector #,frame-size)])
;                                (gen-goal-seq top-sk top-fk frame (g ...))))
;                            20)))]))

;(define-syntax (benchmark stx)
;  (syntax-case stx ()
;    [(_ term0 term ...)
;     (let-values ([(new-term-lst frame-size) (annotate-term #`(term0 term ...))])
;       (with-syntax ([(g ...) new-term-lst])
;         #`(let ([frame (make-vector #,frame-size)])
;             (gen-goal-seq top-sk top-fk frame (g ...)))))]))

(define-syntax (benchmark stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let ([src-vars (collect-src-vars #'(term0 term ...))])
       (let-values ([(new-term-lst frame-size)
                     (annotate-term #`(term0 term ...))])
         (with-syntax ([(g ...) new-term-lst])
           #`(benchmark-time* (lambda ()
                                (let ([frame (make-vector #,frame-size)])
                                  (gen-goal-seq top-sk top-fk frame (g ...))))
                              20))))]))




