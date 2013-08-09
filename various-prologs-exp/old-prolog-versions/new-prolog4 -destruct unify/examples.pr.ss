#lang s-exp "prolog.ss"

(<- (likes Kim Robin))
(<- (likes Sandy Lee))
(<- (likes Sandy Kim))
(<- (likes Robin cats))
(<- (likes Sandy ?x) (likes ?x cats))
(<- (likes Kim ?x) (likes ?x Lee) (likes ?x Kim))
(<- (likes ?x ?x))

;(?- (likes Sandy ?who))



(<- (nextto ?x ?y (?x ?y . ?)))
(<- (nextto ?x ?y (? . ?z)) (nextto ?x ?y ?z))

