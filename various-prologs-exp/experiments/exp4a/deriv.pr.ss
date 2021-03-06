#lang scheme

(require "prolog.rkt")

(<- (d (+ ?u ?v) ?x (+ ?du ?dv)) ! (d ?u ?x ?du) (d ?v ?x ?dv))
(<- (d (- ?u ?v) ?x (- ?du ?dv)) ! (d ?u ?x ?du) (d ?v ?x ?dv))
(<- (d (* ?u ?v) ?x (+ (* ?du ?v) (* ?u ?dv))) ! (d ?u ?x ?du) (d ?v ?x ?dv))
(<- (d (/ ?u ?v) ?x (/ (- (* ?du ?v) (* ?u ?dv)) (^ ?v 2))) !  (d ?u ?x ?du) (d ?v ?x ?dv))
(<- (d (^ ?u ?n) ?x (* ?du (* ?n (^ ?u ?n1)))) ! (integer? ?n) (is ?n1 (- ?n 1)) (d ?u ?x ?du))
(<- (d (- ?u) ?x (- ?du)) ! (d ?u ?x ?du))
(<- (d (exp ?u) ?x (* (exp ?u) ?du)) ! (d ?u ?x ?du))
(<- (d (log ?u) ?x (/ ?du ?u)) ! (d ?u ?x ?du))
(<- (d ?x ?x 1) !)
(<- (d ?c ?x 0))

(<- (deriv-times10) (d (* (* (* (* (* (* (* (* (* x x) x) x) x) x) x) x) x) x) x ?y))

(benchmark (deriv-times10))

