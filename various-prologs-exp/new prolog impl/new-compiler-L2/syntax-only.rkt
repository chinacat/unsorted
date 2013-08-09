#lang racket

(provide (all-defined-out))

; database-related definitions

(define *database* (make-hasheq))

(define (add-clause pred-name compiled-form source-form)
  (hash-set! *database* pred-name compiled-form))

(define (get-clause pred-name)
  (hash-ref *database* pred-name
            (lambda ()
              (error 'get-clause "predicate ~a not defined" pred-name))))


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
     #'(var (gensym '?) *unbound*)]
    [(_ frame ($set-var$ name idx))
     #'(let ([new-var (var (gensym 'name) *unbound*)])
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
    [(_ sk frame (functor arg ...))
     (let ([pred-name (goal->predicate-name #'(functor arg ...))])
       #`((get-clause '#,pred-name)
          sk
          (gen-copy frame arg)
          ...))]))

(define-syntax (gen-goal-seq stx)
  (syntax-case stx ()
    [(_ sk frame ())
     #'(sk)]
    [(_ sk frame (g))
     #'(gen-call sk frame g)]
    [(_ sk frame (g0 g ...))
     #'(gen-call (lambda () (gen-goal-seq sk frame (g ...)))
                 frame
                 g0)]))

(define-syntax (<- stx)
  (syntax-case stx ()
    [(_ term goal ...)
     (let-values ([(new-clause frame-size) (annotate-term #'(term goal ...))]
                  [(pred-name) (goal->predicate-name #'term)])
       (syntax-case new-clause ()
         [((functor pat ...) g ...)
          (with-syntax ([(formal ...) (generate-temporaries #'(pat ...))])
            #`(add-clause '#,pred-name
                          (lambda (sk formal ...)
                            (let ([frame (make-vector #,frame-size)])
                              (if (gen-test-head frame ((pat formal) ...))
                                  (gen-goal-seq sk frame (g ...))
                                  #f)))
                          'term))]))]))

(define-syntax (?- stx)
  (syntax-case stx ()
    [(_ term0 term ...)
     (let-values ([(new-term-lst frame-size) (annotate-term #'(term0 term ...))])
       (with-syntax ([(g ...) new-term-lst])
         #`(let ([frame (make-vector #,frame-size)])
             (gen-goal-seq (lambda () #t) frame (g ...)))))]))

(<- (= ?x ?x))
(?- (= (p (a ?x ?y) (a ?y ?x)) (p ?q ?q)))
(?- (= (p (b ?x ?y) (a ?y ?x)) (p ?q ?q)))

(<- (a ?b ?c) (b ?b) (c ?c))
(<- (b 2))
(<- (c 3))
(?- (a ?i ?j))
(?- (a 2 4))





