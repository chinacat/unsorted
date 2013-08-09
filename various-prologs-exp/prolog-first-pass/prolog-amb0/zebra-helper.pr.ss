#lang s-exp "prolog.ss"

; helper predicates used for the zebra puzzle:

; now member is a primitive
 (<- (member ?item (?item . ?rest)))
 (<- (member ?item (?x . ?rest)) (member ?item ?rest))

(<- (nextto ?x ?y ?list) (iright ?x ?y ?list))
(<- (nextto ?x ?y ?list) (iright ?y ?x ?list))

(<- (iright ?left ?right (?left ?right . ?rest)))
(<- (iright ?left ?right (?x . ?rest))
    (iright ?left ?right ?rest))

; now = is a primitive
 (<- (= ?x ?x))


