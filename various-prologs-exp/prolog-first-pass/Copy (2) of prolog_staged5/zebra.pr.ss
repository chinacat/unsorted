#lang scheme

(require "prolog.ss")

(require "zebra-helper.pr.ss")

; the zebra puzzle predicate

(<- (zebra ?h ?w ?z)
    ; 1
    (= ?h ((house norwegian ? ? ? ?)
           ?
           (house ? ? ? milk ?)
           ?
           ?))
    (member (house englishman ? ? ? red) ?h)
    (member (house spaniard dog ? ? ?) ?h)
    (member (house ? ? ? coffee green) ?h)
    (member (house ukranian ? ? tea ?) ?h)
    ; 6
    (iright (house ? ? ? ? ivory)
            (house ? ? ? ? green)
            ?h)
    (member (house ? snails winston ? ?) ?h)
    (member (house ? ? kools ? yellow) ?h)
    (nextto (house ? ? chesterfield ? ?)
            (house ? fox ? ? ?)
            ?h)
    (nextto (house ? ? kools ? ?)
            (house ? horse ? ? ?)
            ?h)
    ; 11
    (member (house ? ? luckystrike orange-juice ?) ?h)
    (member (house japanese ? parliaments ? ?) ?h)
    (nextto (house norwegian ? ? ? ?)
            (house ? ? ? ? blue)
            ?h)
    ; 14 -- the questions
    (member (house ?w ? ? water ?) ?h)
    (member (house ?z zebra ? ? ?) ?h)
    ; end
    )

(benchmark (zebra ?houses ?water-drinker ?zebra-owner))

