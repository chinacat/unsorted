#lang racket

(require "prolog.rkt")

(provide (all-defined-out))

(define-values
  (member)
  (lambda (sk fk ?item3 temp4)
    (let ((old-trail *trail*))
      (letrec ((temp1
                (lambda ()
                  (let ((?rest #f) (?item #f))
                    (reset-trail old-trail)
                    (if (gen-test-head
                         ((($set-var$ ?item 0) ?item3) ((($ref-var$ ?item 0) $set-var$ ?rest 1) temp4)))
                        (gen-goal-seq sk temp2 ())
                        (temp2)))))
               (temp2
                (lambda ()
                  (let ((?rest #f) (?x #f) (?item #f))
                    (reset-trail old-trail)
                    (if (gen-test-head
                         ((($set-var$ ?item 0) ?item3) ((($set-var$ ?x 1) $set-var$ ?rest 2) temp4)))
                        (gen-goal-seq sk fk ((member ($ref-var$ ?item 0) ($ref-var$ ?rest 2))))
                        (fk))))))
        (temp1)))))

(define-values
  (nextto)
  (lambda (sk fk ?x7 ?y8 ?list9)
    (let ((old-trail *trail*))
      (letrec ((temp5
                (lambda ()
                  (let ((?list #f) (?y #f) (?x #f))
                    (reset-trail old-trail)
                    (if (gen-test-head
                         ((($set-var$ ?x 0) ?x7) (($set-var$ ?y 1) ?y8) (($set-var$ ?list 2) ?list9)))
                        (gen-goal-seq sk temp6 ((iright ($ref-var$ ?x 0) ($ref-var$ ?y 1) ($ref-var$ ?list 2))))
                        (temp6)))))
               (temp6
                (lambda ()
                  (let ((?list #f) (?y #f) (?x #f))
                    (reset-trail old-trail)
                    (if (gen-test-head
                         ((($set-var$ ?x 0) ?x7) (($set-var$ ?y 1) ?y8) (($set-var$ ?list 2) ?list9)))
                        (gen-goal-seq sk fk ((iright ($ref-var$ ?y 1) ($ref-var$ ?x 0) ($ref-var$ ?list 2))))
                        (fk))))))
        (temp5)))))

(define-values
  (iright)
  (lambda (sk fk ?left12 ?right13 temp14)
    (let ((old-trail *trail*))
      (letrec ((temp10
                (lambda ()
                  (let ((?rest #f) (?right #f) (?left #f))
                    (reset-trail old-trail)
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
        (temp10)))))

(define-values
  (=)
  (lambda (sk fk ?x16 ?x17)
    (let ((old-trail *trail*))
      (letrec ((temp15
                (lambda ()
                  (let ((?x #f))
                    (reset-trail old-trail)
                    (if (gen-test-head ((($set-var$ ?x 0) ?x16) (($ref-var$ ?x 0) ?x17)))
                        (gen-goal-seq sk fk ())
                        (fk))))))
        (temp15)))))

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





