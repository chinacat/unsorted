#lang racket

(require "prolog.rkt")

(provide (all-defined-out))

; zebra

(defpred member 2
  [(member ?item (?item . ?rest))]
  [(member ?item (?x . ?rest)) (member ?item ?rest)])

(defpred nextto 3
  [(nextto ?x ?y ?list) (iright ?x ?y ?list)]
  [(nextto ?x ?y ?list) (iright ?y ?x ?list)])

(defpred iright 3
  [(iright ?left ?right (?left ?right . ?rest))]
  [(iright ?left ?right (?x . ?rest))
   (iright ?left ?right ?rest)])

(defpred = 2
  [(= ?x ?x)])

; the zebra puzzle predicate

(defpred zebra 3
  [(zebra ?h ?w ?z)
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
   ])

;(benchmark (zebra ?houses ?water-drinker ?zebra-owner))

(define expanded-member/2
  (syntax->datum
   (expand
    #'(defpred member 2
        [(member ?item (?item . ?rest))]
        [(member ?item (?x . ?rest)) (member ?item ?rest)]))))

(define expanded-nextto/3
  (syntax->datum
   (expand-syntax-to-top-form
    #'(defpred nextto 3
        [(nextto ?x ?y ?list) (iright ?x ?y ?list)]
        [(nextto ?x ?y ?list) (iright ?y ?x ?list)]))))

(define expanded-iright/3
  (syntax->datum
   (expand-syntax-to-top-form
    #'(defpred iright 3
        [(iright ?left ?right (?left ?right . ?rest))]
        [(iright ?left ?right (?x . ?rest))
         (iright ?left ?right ?rest)]))))

(define expanded-=/2
  (syntax->datum
   (expand-syntax-to-top-form
    #'(defpred = 2
        [(= ?x ?x)]))))

(define expanded-zebra/3
  (syntax->datum
   (expand-syntax-to-top-form
    #'(defpred zebra 3
        [(zebra ?h ?w ?z)
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
         ]))))

