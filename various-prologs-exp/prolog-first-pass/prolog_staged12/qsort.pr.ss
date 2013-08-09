#lang scheme

(require "prolog.ss")

(<- (main) (qsort (27 74 17 33 94 18 46 83 65 2
                      32 53 28 85 99 47 28 82 6 11
                      55 29 39 81 90 37 10 0 66 51
                      7 21 85 27 31 63 75 4 95 99
                      11 28 61 74 18 92 40 53 59 8)
                  ?x
                  ()))

(<- (qsort (?x . ?l) ?r ?r0)
    (partition ?l ?x ?l1 ?l2)
    (qsort ?l2 ?r1 ?r0)
    (qsort ?l1 ?r (?x . ?r1)))
(<- (qsort () ?r ?r))

(<- (partition (?x . ?l) ?y (?x . ?l1) ?l2)
    (=< ?x ?y) !
    (partition ?l ?y ?l1 ?l2))
(<- (partition (?x . ?l) ?y ?l1 (?x . ?l2))
    (partition ?l ?y ?l1 ?l2))
(<- (partition () ? () ()))

(time (with-input-from-string ";\n"
                              (lambda ()
                                (?- (main)))))

