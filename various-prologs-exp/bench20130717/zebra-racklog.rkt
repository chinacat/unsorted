#lang racket

(require racklog)

(define ? _)

; zebra

;(<- (member ?item (?item . ?rest)))
;(<- (member ?item (?x . ?rest)) (member ?item ?rest))
;; use the built-in %member

;(<- (nextto ?x ?y ?list) (iright ?x ?y ?list))
;(<- (nextto ?x ?y ?list) (iright ?y ?x ?list))

(define (%nextto x y lst)
  (%or (%iright x y lst)
       (%iright y x lst)))

;(<- (iright ?left ?right (?left ?right . ?rest)))
;(<- (iright ?left ?right (?x . ?rest))
;    (iright ?left ?right ?rest))

;(define %iright
;  (%rel (left right other rest)
;        [(left right `(,left ,right . ,rest))]
;        [(left right `(,other . ,rest))
;         (%iright left right rest)]))

(define (%iright left right lst)
  (%or (%let (rst) (%= lst `(,left ,right . ,rst)))
       (%let (y rst)
             (%and (%= lst `(,y . ,rst))
                   (%iright left right rst)))))

;(<- (= ?x ?x))
;; use the built-in %=

(define (%zebra ?h ?w ?z)
  ;; the zebra puzzle predicate
  ;(<- (zebra ?h ?w ?z)
  (%and
   ;    ; 1
   ;    (= ?h ((house norwegian ? ? ? ?)
   ;           ?
   ;           (house ? ? ? milk ?)
   ;           ?
   ;           ?))
   (%= ?h `((house norwegian ,(?) ,(?) ,(?) ,(?))
            ,(?)
            (house ,(?) ,(?) ,(?) milk ,(?))
            ,(?)
            ,(?)))
   ;    (member (house englishman ? ? ? red) ?h)
   (%member `(house englishman ,(?) ,(?) ,(?) red) ?h)
   ;    (member (house spaniard dog ? ? ?) ?h)
   (%member `(house spaniard dog ,(?) ,(?) ,(?)) ?h)
   ;    (member (house ? ? ? coffee green) ?h)
   (%member `(house ,(?) ,(?) ,(?) coffee green) ?h)
   ;    (member (house ukranian ? ? tea ?) ?h)
   (%member `(house ukranian ,(?) ,(?) tea ,(?)) ?h)
   ;    ; 6
   ;    (iright (house ? ? ? ? ivory)
   ;            (house ? ? ? ? green)
   ;            ?h)
   (%iright `(house ,(?) ,(?) ,(?) ,(?) ivory)
            `(house ,(?) ,(?) ,(?) ,(?) green)
            ?h)
   ;    (member (house ? snails winston ? ?) ?h)
   (%member `(house ,(?) snails winston ,(?) ,(?)) ?h)
   ;    (member (house ? ? kools ? yellow) ?h)
   (%member `(house ,(?) ,(?) kools ,(?) yellow) ?h)
   ;    (nextto (house ? ? chesterfield ? ?)
   ;            (house ? fox ? ? ?)
   ;            ?h)
   (%nextto `(house ,(?) ,(?) chesterfield ,(?) ,(?))
            `(house ,(?) fox ,(?) ,(?) ,(?))
            ?h)
   ;    (nextto (house ? ? kools ? ?)
   ;            (house ? horse ? ? ?)
   ;            ?h)
   (%nextto `(house ,(?) ,(?) kools ,(?) ,(?))
            `(house ,(?) horse ,(?) ,(?) ,(?))
            ?h)
   ;    ; 11
   ;    (member (house ? ? luckystrike orange-juice ?) ?h)
   (%member `(house ,(?) ,(?) luckystrike orange-juice ,(?)) ?h)
   ;    (member (house japanese ? parliaments ? ?) ?h)
   (%member `(house japanese ,(?) parliaments ,(?) ,(?)) ?h)
   ;    (nextto (house norwegian ? ? ? ?)
   ;            (house ? ? ? ? blue)
   ;            ?h)
   (%nextto `(house norwegian ,(?) ,(?) ,(?) ,(?))
            `(house ,(?) ,(?) ,(?) ,(?) blue)
            ?h)
   ;    ; 14 -- the questions
   ;    (member (house ?w ? ? water ?) ?h)
   (%member `(house ,?w ,(?) ,(?) water ,(?)) ?h)
   ;    (member (house ?z zebra ? ? ?) ?h)
   (%member `(house ,?z zebra ,(?) ,(?) ,(?)) ?h)
   ;    ; end
   ;    )
   ))

(define (%main)
  (%which (?houses ?water-drinker ?zebra-owner)
          (%zebra ?houses ?water-drinker ?zebra-owner)))

(define (%all thunk)
  (let ([answer (thunk)])
    (if answer
        (cons answer (%all %more))
        '())))

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
  (benchmark-time* (lambda () (%main))
                   20))

;(b)





