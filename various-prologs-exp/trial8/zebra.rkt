#lang racket

(require "prolog.rkt")

(provide (all-defined-out))

; zebra

;(defpred member 2
;  [(member ?item (?item . ?rest))]
;  [(member ?item (?x . ?rest)) (member ?item ?rest)])

(define (member sk fk ?item temp4)
  (let ([temp4 (deref temp4)])
    (if (or (pair? temp4) (var? temp4))
        (let ([?x (if (pair? temp4)
                      (deref (car temp4))
                      (var '?x *unbound*))]
              [?rest (if (pair? temp4)
                         (deref (cdr temp4))
                         (var '?rest *unbound*))])
          (when (var? temp4)
            (set-binding! temp4 (cons ?x ?rest)))
          (let ((old-trail *trail*))
            (letrec ([temp1
                      (lambda ()
                        (if (unify! ?item ?x)
                            (sk temp2)
                            (temp2)))]
                     [temp2
                      (lambda ()
                        (reset-trail old-trail)
                        (member sk fk ?item ?rest))])
              (temp1))))
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

;(define (iright sk fk ?left ?right temp5)
;  (let ((old-trail *trail*))
;    (letrec ([temp1
;              (lambda ()
;                (let ((?rest #f))
;                  (if (gen-test-head
;                       (((($ref-var$ ?left 0)
;                          ($ref-var$ ?right 1)
;                          $set-var$
;                          ?rest
;                          2)
;                         temp5)))
;                      (gen-goal-seq sk temp2 ())
;                      (temp2))))]
;             [temp2
;              (lambda ()
;                (let ((?rest #f))
;                  (reset-trail old-trail)
;                  (if (gen-test-head
;                       (((($anon-var$) $set-var$ ?rest 3) temp5)))
;                      (gen-goal-seq
;                       sk
;                       fk
;                       ((iright
;                         ($ref-var$ ?left 0)
;                         ($ref-var$ ?right 1)
;                         ($ref-var$ ?rest 3))))
;                      (fk))))])
;      (temp1))))

(define (__iright sk fk ?left ?right temp)
  (let ([?x #f] [?rst #f])
    (if (gen-test-head (((($set-var$ ?x 0) $set-var$ ?rst 2) temp)))
        (let ((old-trail *trail*))
          (letrec ([temp1 (lambda ()
                            (if (unify! ?left ?x)
                                (let ([?z #f])
                                  (if (gen-test-head (((($ref-var$ ?right 0) $set-var$ ?z 2) ?rst)))
                                      (sk temp2)
                                      (temp2)))
                                (temp2)))]
                   [temp2 (lambda ()
                            (reset-trail old-trail)
                            (iright sk fk ?left ?right ?rst))])
            (temp1)))
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

(define (iright sk fk ?left ?right temp)
  (let ([temp (deref temp)])
    (if (or (pair? temp) (var? temp))
        (let ([?x (if (pair? temp)
                      (deref (car temp))
                      (var '?x *unbound*))]
              [?rst (if (pair? temp)
                        (deref (cdr temp))
                        (var '?rst *unbound*))])
          (when (var? temp)
            (set-binding! temp (cons ?x ?rst)))
          (let ([old-trail *trail*])
            (letrec ([temp1 (lambda ()
                              (if (unify! ?left ?x)
                                  (if (let ([?rst (deref ?rst)])
                                        (if (pair? ?rst)
                                            (unify! ?right (car ?rst))
                                            (if (var? ?rst)
                                                (set-binding! ?rst (cons ?right (var '? *unbound*)))
                                                #f)))
                                      (sk temp2)
                                      (temp2))
                                  (temp2)))]
                     [temp2 (lambda ()
                              (reset-trail old-trail)
                              (iright sk fk ?left ?right ?rst))])
              (temp1))))
        (fk))))



