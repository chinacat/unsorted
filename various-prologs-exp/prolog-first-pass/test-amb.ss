#lang scheme

(define-struct choices (k alts)
  #:mutable)

(define stack '())

(define (amb-fail)
  (if (null? stack)
      'done
      (let* ([frame (car stack)]
             [thunks (choices-alts frame)])
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
                  (let ([new-frame (make-choices k rest)])
                    (set! stack (cons new-frame stack))
                    (first)))))]))

(define-syntax amb
  (syntax-rules ()
    [(_)
     (amb-fail)]
    [(_ arg0 arg ...)
     (amb* (lambda () arg0) (lambda () arg) ...)]))



