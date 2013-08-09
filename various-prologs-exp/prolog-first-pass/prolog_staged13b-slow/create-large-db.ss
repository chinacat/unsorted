#lang scheme

(require "prolog.ss")

(define (create-predicate name num)
  (add-clause (list (list name num))))

(define (loop m n)
  (if (< m n)
      (begin (create-predicate (gensym 'abc) m)
             (loop (+ m 1) n))
      (void)))

(loop 0 1000000)





