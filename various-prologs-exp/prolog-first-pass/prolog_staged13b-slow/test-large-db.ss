#lang scheme

(require "prolog.ss")

(define (make-name num)
  (string->symbol (string-append "abc-" (number->string num))))

(define (create-fact num)
  (add-clause (list (list (make-name num) num))))

(define (create-predicate num)
  (add-clause (list (list (make-name num) num) (list (make-name (- num 1)) (- num 1)))))

(define (loop m n)
  (if (< m n)
      (begin (create-predicate m)
             (loop (+ m 1) n))
      (void)))

(let ([size 500000])
  (create-fact 0)
  (loop 0 size)
  (create-predicate size))

(printf "start~n~n")

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))

(benchmark (abc-500000 500000))



