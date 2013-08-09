#lang racket

(require "prolog.rkt")

(provide (all-defined-out))

(define (member sk fk ?item3 temp4)
  (let ([old-trail *trail*])
    (define (temp1)
      (let-values (((?rest) '#f) ((?item) '#f))
        (if (if (begin (set! ?item (deref ?item3)) '#t)
                (let-values (((temp4) (deref temp4)))
                  (if (pair? temp4)
                      (let-values ()
                        (let-values (((arg-car) (car temp4)) ((arg-cdr) (cdr temp4)))
                          (if (unify! ?item arg-car)
                              (begin (set! ?rest (deref arg-cdr)) '#t)
                              '#f)))
                      (if (var? temp4)
                          (let-values ()
                            (#%app
                             set-binding!
                             temp4
                             (#%app
                              cons
                              ?item
                              (let-values (((new-var) (var '?rest *unbound*)))
                                (set! ?rest new-var)
                                new-var))))
                          (let-values () '#f))))
                '#f)
            (sk temp2)
            (temp2))))
    (define (temp2)
      (let-values (((?rest) '#f) ((?x) '#f) ((?item) '#f))
        (reset-trail old-trail)
        (if (if (begin (set! ?item (deref ?item3)) '#t)
                (let-values (((temp4) (deref temp4)))
                  (if (pair? temp4)
                      (let-values ()
                        (let-values (((arg-car) (car temp4)) ((arg-cdr) (cdr temp4)))
                          (if (begin (set! ?x (deref arg-car)) '#t)
                              (begin (set! ?rest (deref arg-cdr)) '#t)
                              '#f)))
                      (if (var? temp4)
                          (let-values ()
                            (#%app
                             set-binding!
                             temp4
                             (#%app
                              cons
                              (let-values (((new-var) (var '?x *unbound*)))
                                (set! ?x new-var)
                                new-var)
                              (let-values (((new-var) (var '?rest *unbound*)))
                                (set! ?rest new-var)
                                new-var))))
                          (let-values () '#f))))
                '#f)
            (member sk fk ?item ?rest)
            (fk))))
    (temp1)))

(define (nextto sk fk ?x7 ?y8 ?list9)
  (let ((old-trail *trail*))
    (letrec ((temp5
              (lambda ()
                (iright sk temp6 ?x7 ?y8 ?list9)))
             (temp6
              (lambda ()
                (reset-trail old-trail)
                (iright sk fk ?y8 ?x7 ?list9))))
      (temp5))))

(define (iright sk fk ?left12 ?right13 temp14)
  (let ((old-trail *trail*))
    (letrec ((temp10
              (lambda ()
                (let ((?rest #f) (?right #f) (?left #f))
                  (if (gen-test-head
                       ((($set-var$ ?left 0) ?left12)
                        (($set-var$ ?right 1) ?right13)
                        ((($ref-var$ ?left 0) ($ref-var$ ?right 1) $set-var$ ?rest 2) temp14)))
                      (gen-goal-seq sk temp11 ())
                      (temp11)))))
             (temp11
              (lambda ()
                (let ((?rest #f) (?x #f) (?right #f) (?left #f))
                  (reset-trail old-trail)
                  (if (gen-test-head
                       ((($set-var$ ?left 0) ?left12)
                        (($set-var$ ?right 1) ?right13)
                        ((($set-var$ ?x 2) $set-var$ ?rest 3) temp14)))
                      (gen-goal-seq
                       sk
                       fk
                       ((iright ($ref-var$ ?left 0) ($ref-var$ ?right 1) ($ref-var$ ?rest 3))))
                      (fk))))))
      (temp10))))

(define (= sk fk ?x16 ?x17)
  (set-binding! ?x16 ?x17)
  (sk fk))

(define-values
  (zebra)
  (lambda (sk fk ?h19 ?w20 ?z21)
    (let ((old-trail *trail*))
      (letrec ((temp18
                (lambda ()
                  (let ((?z #f) (?w #f) (?h #f))
                    (reset-trail old-trail)
                    (if (gen-test-head
                         ((($set-var$ ?h 0) ?h19) (($set-var$ ?w 1) ?w20) (($set-var$ ?z 2) ?z21)))
                        (gen-goal-seq
                         sk
                         fk
                         ((=
                           ($ref-var$ ?h 0)
                           ((house norwegian ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$))
                            ($anon-var$)
                            (house ($anon-var$) ($anon-var$) ($anon-var$) milk ($anon-var$))
                            ($anon-var$)
                            ($anon-var$)))
                          (member (house englishman ($anon-var$) ($anon-var$) ($anon-var$) red) ($ref-var$ ?h 0))
                          (member (house spaniard dog ($anon-var$) ($anon-var$) ($anon-var$)) ($ref-var$ ?h 0))
                          (member (house ($anon-var$) ($anon-var$) ($anon-var$) coffee green) ($ref-var$ ?h 0))
                          (member (house ukranian ($anon-var$) ($anon-var$) tea ($anon-var$)) ($ref-var$ ?h 0))
                          (iright
                           (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) ivory)
                           (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) green)
                           ($ref-var$ ?h 0))
                          (member (house ($anon-var$) snails winston ($anon-var$) ($anon-var$)) ($ref-var$ ?h 0))
                          (member (house ($anon-var$) ($anon-var$) kools ($anon-var$) yellow) ($ref-var$ ?h 0))
                          (nextto
                           (house ($anon-var$) ($anon-var$) chesterfield ($anon-var$) ($anon-var$))
                           (house ($anon-var$) fox ($anon-var$) ($anon-var$) ($anon-var$))
                           ($ref-var$ ?h 0))
                          (nextto
                           (house ($anon-var$) ($anon-var$) kools ($anon-var$) ($anon-var$))
                           (house ($anon-var$) horse ($anon-var$) ($anon-var$) ($anon-var$))
                           ($ref-var$ ?h 0))
                          (member
                           (house ($anon-var$) ($anon-var$) luckystrike orange-juice ($anon-var$))
                           ($ref-var$ ?h 0))
                          (member
                           (house japanese ($anon-var$) parliaments ($anon-var$) ($anon-var$))
                           ($ref-var$ ?h 0))
                          (nextto
                           (house norwegian ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$))
                           (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) blue)
                           ($ref-var$ ?h 0))
                          (member
                           (house ($ref-var$ ?w 1) ($anon-var$) ($anon-var$) water ($anon-var$))
                           ($ref-var$ ?h 0))
                          (member
                           (house ($ref-var$ ?z 2) zebra ($anon-var$) ($anon-var$) ($anon-var$))
                           ($ref-var$ ?h 0))))
                        (fk))))))
        (temp18)))))





