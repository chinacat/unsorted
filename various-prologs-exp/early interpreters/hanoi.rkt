#lang racket

(require miprolog/prolog)

; program due to L. Pereira, 1975
(<- (hanoi 1 ?a ?b ?c)
    !
    (write |Move disk |)
    (write ?a)
    (write | to |)
    (write ?b)
    (nl))
(<- (hanoi ?n ?a ?b ?c)
    (is ?m (- ?n 1))
    (hanoi ?m ?a ?c ?b)
    (hanoi 1 ?a ?b ?c)
    (hanoi ?m ?c ?b ?a))

; (?- (hanoi 3 a c b))


