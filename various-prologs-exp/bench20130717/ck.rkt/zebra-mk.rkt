#lang racket

(require "tester.scm")
(require "ck.scm")
(require "fd.scm")
(require "tree-unify.scm")
(require "miniKanren.scm")

;; in comments, the code in 'MiProlog' syntax for the zebra puzzle
;
;; zebra
;
;(<- (member ?item (?item . ?rest)))
;(<- (member ?item (?x . ?rest)) (member ?item ?rest))

; use the 'built-in' membero MK relation

;(<- (nextto ?x ?y ?list) (iright ?x ?y ?list))
;(<- (nextto ?x ?y ?list) (iright ?y ?x ?list))

(define (nextto x y lst)
  (conde
   [(iright x y lst)]
   [(iright y x lst)]))

;(<- (iright ?left ?right (?left ?right . ?rest)))
;(<- (iright ?left ?right (?x . ?rest))
;    (iright ?left ?right ?rest))

(define (iright left right lst)
  (conde
   [(caro lst left) (fresh (d) (cdro lst d) (caro d right))]
   [(fresh (d) (cdro lst d) (iright left right d))]))

;(<- (= ?x ?x))

;; use the 'built-in' == MK relation

;; the zebra puzzle predicate

(define (?) (var '?))

(define (zebra h w z)
  (conde
   [
    ;(<- (zebra ?h ?w ?z)
    ;    ; 1
    ;    (= ?h ((house norwegian ? ? ? ?)
    ;           ?
    ;           (house ? ? ? milk ?)
    ;           ?
    ;           ?))
    (== h `((house norwegian ,(?) ,(?) ,(?) ,(?))
            ,(?)
            (house ,(?) ,(?) ,(?) milk ,(?))
            ,(?)
            ,(?)))
    ;    (member (house englishman ? ? ? red) ?h)
    (membero `(house englishman ,(?) ,(?) ,(?) red) h)
    ;    (member (house spaniard dog ? ? ?) ?h)
    (membero `(house spaniard dog ,(?) ,(?) ,(?)) h)
    ;    (member (house ? ? ? coffee green) ?h)
    (membero `(house ,(?) ,(?) ,(?) coffee green) h)
    ;    (member (house ukranian ? ? tea ?) ?h)
    (membero `(house ukranian ,(?) ,(?) tea ,(?)) h)
    ;    ; 6
    ;    (iright (house ? ? ? ? ivory)
    ;            (house ? ? ? ? green)
    ;            ?h)
    (iright `(house ,(?) ,(?) ,(?) ,(?) ivory)
            `(house ,(?) ,(?) ,(?) ,(?) green)
            h)
    ;    (member (house ? snails winston ? ?) ?h)
    (membero `(house ,(?) snails winston ,(?) ,(?)) h)
    ;    (member (house ? ? kools ? yellow) ?h)
    (membero `(house ,(?) ,(?) kools ,(?) yellow) h)
    ;    (nextto (house ? ? chesterfield ? ?)
    ;            (house ? fox ? ? ?)
    ;            ?h)
    (nextto `(house ,(?) ,(?) chesterfield ,(?) ,(?))
            `(house ,(?) fox ,(?) ,(?) ,(?))
            h)
    ;    (nextto (house ? ? kools ? ?)
    ;            (house ? horse ? ? ?)
    ;            ?h)
    (nextto `(house ,(?) ,(?) kools ,(?) ,(?))
            `(house ,(?) horse ,(?) ,(?) ,(?))
            h)
    ;    ; 11
    ;    (member (house ? ? luckystrike orange-juice ?) ?h)
    (membero `(house ,(?) ,(?) luckystrike orange-juice ,(?)) h)
    ;    (member (house japanese ? parliaments ? ?) ?h)
    (membero `(house japanese ,(?) parliaments ,(?) ,(?)) h)
    ;    (nextto (house norwegian ? ? ? ?)
    ;            (house ? ? ? ? blue)
    ;            ?h)
    (nextto `(house norwegian ,(?) ,(?) ,(?) ,(?))
            `(house ,(?) ,(?) ,(?) ,(?) blue)
            h)
    ;    ; 14 -- the questions
    ;    (member (house ?w ? ? water ?) ?h)
    (membero `(house ,w ,(?) ,(?) water ,(?)) h)
    ;    (member (house ?z zebra ? ? ?) ?h)
    (membero `(house ,z zebra ,(?) ,(?) ,(?)) h)
    ;    ; end
    ;    )
    ]))


;(?- (zebra ?houses ?water-drinker ?zebra-owner))
(define (main q)
  (fresh (houses water-drinker zebra-owner)
         (zebra houses water-drinker zebra-owner)
         (== q `(,houses ,water-drinker ,zebra-owner))))

;; cpu-time : (() -> any) -> integer
(define (cpu-time thunk)
  (let-values (([result cpu real gc] (time-apply thunk null)))
    cpu))

;; (() -> any) -> (vectorof integer)
(define (benchmark-time* thunk count)
  (collect-garbage)
  (collect-garbage)
  (collect-garbage)
  (sort (for/list ([i (in-range count)])
          (begin0 (cpu-time thunk)
                  (collect-garbage)
                  (collect-garbage)
                  (collect-garbage)))
        <))

(define (b)
  (benchmark-time* (lambda () (run* (answer) (main answer)))
                   20))

(b)







