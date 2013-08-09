#lang racket

(require "tester.scm")
(require "ck.scm")
(require "fd.scm")
(require "tree-unify.scm")
(require "miniKanren.scm")

;; current code is broken -- for example, even the most trivial code 
;; fails with a contract violation (cddr expected a pair, received #t)
;(test-check "0.0"
;  (run* (x)
;    (infd x '(1 2)))
;  '(1 2))


