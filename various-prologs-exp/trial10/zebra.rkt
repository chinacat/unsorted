#lang racket

(require "prolog.rkt")

(provide (all-defined-out))

; zebra

;(defpred member 2
;  [(member ?item (?item . ?rest))]
;  [(member ?item (?x . ?rest)) (member ?item ?rest)])

(define (member sk fk ?item temp4)
  (let iter ([temp4 (deref temp4)])
    (if (pair? temp4)
        (let ((old-trail *trail*))
          (letrec ([temp1
                    (lambda ()
                      (if (unify! ?item (car temp4))
                          (sk temp2)
                          (temp2)))]
                   [temp2
                    (lambda ()
                      (reset-trail old-trail)
                      (iter (deref (cdr temp4))))])
            (temp1)))
        (fk))))

;(defpred nextto 3
;  [(nextto ?x ?y ?list) (iright ?x ?y ?list)]
;  [(nextto ?x ?y ?list) (iright ?y ?x ?list)])

(define (nextto sk fk ?x3 ?y4 ?list5)
  (letrec ([temp1
            (lambda ()
              (iright sk temp2 ?x3 ?y4 ?list5))]
           [temp2
            (lambda ()
              (iright sk fk ?y4 ?x3 ?list5))])
    (temp1)))

;(defpred iright 3
;  [(iright ?left ?right (?left ?right . ?rest))]
;  [(iright ?left ?right (?x . ?rest))
;   (iright ?left ?right ?rest)])

(define (iright sk fk ?left ?right temp)
  (let iter ([temp (deref temp)])
    (if (pair? temp)
        (let ([?rst (deref (cdr temp))])
          (let ([old-trail *trail*])
            (letrec ([temp1 (lambda ()
                              (if (unify! ?left (car temp))
                                  (if (if (pair? ?rst)
                                          (unify! ?right (car ?rst))
                                          #f)
                                      (sk temp2)
                                      (temp2))
                                  (temp2)))]
                     [temp2 (lambda ()
                              (reset-trail old-trail)
                              (iter ?rst))])
              (temp1))))
        (fk))))

;(defpred = 2
;  [(= ?x ?x)])

(define (assign! sk fk ?x2 ?x3)
  (set-binding! ?x2 ?x3)
  (sk fk))

; the zebra puzzle predicate

;(defpred zebra 3
;  [(zebra ?h ?w ?z)
;   ; 1
;   (= ?h ((house norwegian ? ? ? ?)
;          ?
;          (house ? ? ? milk ?)
;          ?
;          ?))
;   (member (house englishman ? ? ? red) ?h)
;   (member (house spaniard dog ? ? ?) ?h)
;   (member (house ? ? ? coffee green) ?h)
;   (member (house ukranian ? ? tea ?) ?h)
;   ; 6
;   (iright (house ? ? ? ? ivory)
;           (house ? ? ? ? green)
;           ?h)
;   (member (house ? snails winston ? ?) ?h)
;   (member (house ? ? kools ? yellow) ?h)
;   (nextto (house ? ? chesterfield ? ?)
;           (house ? fox ? ? ?)
;           ?h)
;   (nextto (house ? ? kools ? ?)
;           (house ? horse ? ? ?)
;           ?h)
;   ; 11
;   (member (house ? ? luckystrike orange-juice ?) ?h)
;   (member (house japanese ? parliaments ? ?) ?h)
;   (nextto (house norwegian ? ? ? ?)
;           (house ? ? ? ? blue)
;           ?h)
;   ; 14 -- the questions
;   (member (house ?w ? ? water ?) ?h)
;   (member (house ?z zebra ? ? ?) ?h)
;   ; end
;   ])

(define (zebra sk fk ?h ?w ?z)
  (gen-goal-seq
   sk
   fk
   ((assign!
     ($ref-var$ ?h 0)
     ((house norwegian ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$))
      ($anon-var$)
      (house ($anon-var$) ($anon-var$) ($anon-var$) milk ($anon-var$))
      ($anon-var$)
      ($anon-var$)))
    (member
     (house englishman ($anon-var$) ($anon-var$) ($anon-var$) red)
     ($ref-var$ ?h 0))
    (member
     (house spaniard dog ($anon-var$) ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0))
    (member
     (house ($anon-var$) ($anon-var$) ($anon-var$) coffee green)
     ($ref-var$ ?h 0))
    (member
     (house ukranian ($anon-var$) ($anon-var$) tea ($anon-var$))
     ($ref-var$ ?h 0))
    (iright
     (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) ivory)
     (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) green)
     ($ref-var$ ?h 0))
    (member
     (house ($anon-var$) snails winston ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0))
    (member
     (house ($anon-var$) ($anon-var$) kools ($anon-var$) yellow)
     ($ref-var$ ?h 0))
    (nextto
     (house ($anon-var$) ($anon-var$) chesterfield ($anon-var$) ($anon-var$))
     (house ($anon-var$) fox ($anon-var$) ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0))
    (nextto
     (house ($anon-var$) ($anon-var$) kools ($anon-var$) ($anon-var$))
     (house ($anon-var$) horse ($anon-var$) ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0))
    (member
     (house ($anon-var$) ($anon-var$) luckystrike orange-juice ($anon-var$))
     ($ref-var$ ?h 0))
    (member
     (house japanese ($anon-var$) parliaments ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0))
    (nextto
     (house norwegian ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$))
     (house ($anon-var$) ($anon-var$) ($anon-var$) ($anon-var$) blue)
     ($ref-var$ ?h 0))
    (member
     (house ($ref-var$ ?w 1) ($anon-var$) ($anon-var$) water ($anon-var$))
     ($ref-var$ ?h 0))
    (member
     (house ($ref-var$ ?z 2) zebra ($anon-var$) ($anon-var$) ($anon-var$))
     ($ref-var$ ?h 0)))))

;(benchmark (zebra ?houses ?water-drinker ?zebra-owner))
;(?- (zebra ?houses ?water-drinker ?zebra-owner))





