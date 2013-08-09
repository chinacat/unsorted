#lang scheme

(define (write-predicate name num)
  (printf "(<- (~a ~a))~n~n" name num))

(define (loop m n)
  (if (< m n)
      (begin (write-predicate (gensym 'abc) m)
             (loop (+ m 1) n))
      (void)))

(with-output-to-file "large-db.pr.ss"
  (lambda ()
    (printf "#lang scheme~n~n")
    (printf "(require \"prolog.ss\")~n~n")
    (loop 0 5000))
  #:exists 'replace)



