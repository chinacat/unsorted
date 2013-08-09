#lang racket

(require "new4.rkt")

; zebra

(<- (member ?item (?item . ?rest)))
(<- (member ?item (?x . ?rest)) (member ?item ?rest))

(<- (nextto ?x ?y ?list) (iright ?x ?y ?list))
(<- (nextto ?x ?y ?list) (iright ?y ?x ?list))

(<- (iright ?left ?right (?left ?right . ?rest)))
(<- (iright ?left ?right (?x . ?rest))
    (iright ?left ?right ?rest))

(<- (= ?x ?x))

; the zebra puzzle predicate

(<- (zebra ?h ?w ?z)
    ; 1
    (= ?h ((house norwegian ?1 ?2 ?3 ?4)
           ?5
           (house ?6 ?7 ?8 milk ?9)
           ?10
           ?11))
    (member (house englishman ?12 ?13 ?14 red) ?h)
    (member (house spaniard dog ?15 ?16 ?17) ?h)
    (member (house ?18 ?19 ?20 coffee green) ?h)
    (member (house ukranian ?21 ?22 tea ?23) ?h)
    ; 6
    (iright (house ?24 ?25 ?26 ?27 ivory)
            (house ?28 ?29 ?30 ?31 green)
            ?h)
    (member (house ?32 snails winston ?33 ?34) ?h)
    (member (house ?35 ?36 kools ?37 yellow) ?h)
    (nextto (house ?38 ?39 chesterfield ?40 ?41)
            (house ?42 fox ?43 ?44 ?45)
            ?h)
    (nextto (house ?46 ?47 kools ?48 ?49)
            (house ?50 horse ?51 ?52 ?53)
            ?h)
    ; 11
    (member (house ?54 ?55 luckystrike orange-juice ?56) ?h)
    (member (house japanese ?57 parliaments ?58 ?59) ?h)
    (nextto (house norwegian ?60 ?61 ?62 ?63)
            (house ?64 ?65 ?66 ?67 blue)
            ?h)
    ; 14 -- the questions
    (member (house ?w ?68 ?69 water ?70) ?h)
    (member (house ?z zebra ?71 ?72 ?73) ?h)
    ; end
    )

(?- (zebra ?houses ?water-drinker ?zebra-owner))

