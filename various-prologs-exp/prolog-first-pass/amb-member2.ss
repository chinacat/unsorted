#lang scheme

(define-struct unbound ())

(define *unbound* (make-unbound))

(define-struct variable (name n [val #:auto])
  ;#:transparent
  #:mutable
  #:auto-value *unbound*)

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

(define new-counter
  (let ([counter 0])
    (lambda ()
      (let ([result counter])
        (set! counter (+ counter 1))
        result))))

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

(define-struct choices (k old-trail alts)
  #:mutable)

(define amb-prompt-tag (make-continuation-prompt-tag))

(define stack '())

(define (amb-fail)
  (if (null? stack)
      (abort-current-continuation amb-prompt-tag)
      (let* ([frame (car stack)]
             [thunks (choices-alts frame)])
        (reset-trail (choices-old-trail frame))
        (let ([first (car thunks)]
              [rest (cdr thunks)])
          (if (null? rest)
              (set! stack (cdr stack))
              (set-choices-alts! frame rest))
          ((choices-k frame) (first))))))

(define (amb* . thunks)
  (cond
    [(null? thunks)
     (amb-fail)]
    [(null? (cdr thunks))
     ((car thunks))]
    [else
     (call/cc (lambda (k)
                (let ([first (car thunks)]
                      [rest (cdr thunks)])
                  (let ([new-frame (make-choices k *trail* rest)])
                    (set! stack (cons new-frame stack))
                    (first))))
              amb-prompt-tag)]))

(define-syntax amb
  (syntax-rules ()
    [(_)
     (amb-fail)]
    [(_ arg0 arg ...)
     (amb* (lambda () arg0) (lambda () arg) ...)]))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (printf " Type ; to see more or . to stop~n")
          (continue?)]))

(define (residualize-variable term)
  (if (variable-n term)
      (string->symbol (string-append (symbol->string (variable-name term))
                                     (number->string (variable-n term))))
      (variable-name term)))

(define (simplify-term term)
  (cond
    [(pair? term)
     (cons (simplify-term (car term)) (simplify-term (cdr term)))]
    ;[(predicate? term)
    ; (predicate-name term)]
    [(variable? term)
     (if (bound? term)
         (simplify-term (deref term))
         (residualize-variable term))]
    [else
     term]))

(define (show-prolog-vars vars)
  (if (null? vars)
      (printf "~nYes.")
      (for-each (lambda (var)
                  (printf "~n~a = ~s" (residualize-variable var) (simplify-term var)))
                vars)))

(define (=/2 ?arg1 ?arg2)
  (unless (unify! ?arg1 ?arg2)
    (amb-fail)))

(define (member/2 ?arg1 ?arg2)
  (amb (let ([?item (make-variable '?item (new-counter))]
             [?rest (make-variable '?rest (new-counter))])
         (unless (and (unify! ?arg1 ?item)
                      (unify! ?arg2 (cons ?item ?rest)))
           (amb-fail)))
       (let ([?x (make-variable '?x (new-counter))]
             [?item (make-variable '?item (new-counter))]
             [?rest (make-variable '?rest (new-counter))])
         (unless (and (unify! ?arg1 ?item)
                      (unify! ?arg2 (cons ?x ?rest)))
           (amb-fail))
         (member/2 ?item ?rest))))

(define-syntax execute-query
  (syntax-rules ()
    [(_ goal ...)
     (call-with-continuation-prompt
      (lambda ()
        goal ...
        ; in the real code, this would be here!
        ;(show-prolog-vars '())
        (if (continue?)
            (amb-fail)
            (abort-current-continuation amb-prompt-tag)))
      amb-prompt-tag
      (lambda ()
        (set! stack '())
        (printf "~nNo.")))]))

(define-syntax execute-query/auto
  (syntax-rules ()
    [(_ goal ...)
     (call-with-continuation-prompt
      (lambda ()
        goal ...
        ; in the real code, this would be here!
        ;(show-prolog-vars '())
        (amb-fail))
      amb-prompt-tag
      (lambda ()
        (set! stack '())
        (printf "~nNo.")))]))

; demo: ?- member(3, [1,2,3,4,5]).
(define (main0)
  (execute-query (member/2 3 '(1 2 3 4 5))
                 (show-prolog-vars '())))

; demo: ?- member(X, [1,2,3,4,5]).
(define (main1)
  (let ([?x (make-variable '?x #f)])
    (execute-query (member/2 ?x '(1 2 3 4 5))
                   (show-prolog-vars (list ?x)))))

; demo: ?- member(1, Y).
(define (main2)
  (let ([?y (make-variable '?y #f)])
    (execute-query (member/2 1 ?y)
                   (show-prolog-vars (list ?y)))))

; demo: ?- member(X, [1,2,3,4,5]).
(define (main1/alt)
  (let ([?x (make-variable '?x #f)])
    (execute-query/auto (member/2 ?x '(1 2 3 4 5))
                        (show-prolog-vars (list ?x)))))

(define (foo)
  (let ([?x (make-variable '?x #f)])
    (execute-query/auto (member/2 ?x '(1 3 5 6 7 9))
                        (member/2 ?x '(2 5 7 8 9))
                        (show-prolog-vars (list ?x)))))

(define (bag-of-foo ?y)
  (let ([acc '()]
        [original-stack stack])
    (set! stack '())
    (call-with-continuation-prompt
     (lambda ()
       (let ([?x (make-variable '?x #f)])
         (member/2 ?x '(1 3 5 6 7 9))
         (member/2 ?x '(2 5 7 8 9))
         (set! acc (cons (simplify-term ?x) acc))
         (amb-fail)))
     amb-prompt-tag
     (lambda ()
       (set! stack original-stack)
       (unify! ?y (reverse acc))))))

(define (main-bag)
  (let ([?x (make-variable '?x #f)])
    (execute-query (bag-of-foo ?x)
                   (show-prolog-vars (list ?x)))))




