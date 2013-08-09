#lang scheme

(require "prolog.rkt")

(<- (main) (serialize "able was i ere i saw elba" ?x))

(<- (serialize ?l ?r)
    (pairlists ?l ?r ?a)
    (arrange ?a ?t)
    (numbered ?t 1 ?n))

(<- (pairlists (?x . ?l) (?y . ?r) ((pair ?x ?y) . ?a))
    (pairlists ?l ?r ?a))
(<- (pairlists () () ()))

(<- (arrange (?x . ?l) (tree ?t1 ?x ?t2))
    (split ?l ?x ?l1 ?l2)
    (arrange ?l1 ?t1)
    (arrange ?l2 ?t2))
(<- (arrange () void))

(<- (split (?x . ?l) ?x ?l1 ?l2)
    !
    (split ?l ?x ?l1 ?l2))
(<- (split (?x . ?l) ?y (?x . ?l1) ?l2)
    (before ?x ?y) !
    (split ?l ?y ?l1 ?l2))
(<- (split (?x . ?l) ?y ?l1 (?x . ?l2))
    (before ?y ?x) !
    (split ?l ?y ?l1 ?l2))
(<- (split () ? () ()))

(<- (before (pair ?x1 ?y1) (pair ?x2 ?y2))
    (< ?x1 ?x2))

(<- (numbered (tree ?t1 (pair ?x ?n1) ?t2) ?n0 ?n)
    (numbered ?t1 ?n0 ?n1)
    (is ?n2 (+ ?n1 1))
    (numbered ?t2 ?n2 ?n))
(<- (numbered void ?n ?n))


(benchmark (main))



