#lang racket

(require "prolog.rkt")
(require "zebra.rkt")

(benchmark (zebra ?h1 ?w1 ?z1)
           (zebra ?h2 ?w2 ?z2)
           (zebra ?h3 ?w3 ?z3)
           (zebra ?h4 ?w4 ?z4)
           (zebra ?h5 ?w5 ?z5)
           (zebra ?h6 ?w6 ?z6)
           (zebra ?h7 ?w7 ?z7)
           (zebra ?h8 ?w8 ?z8)
           (zebra ?h9 ?w9 ?z9)
           (zebra ?h10 ?w10 ?z10)
           (zebra ?h11 ?w11 ?z11)
           (zebra ?h12 ?w12 ?z12)
           (zebra ?h13 ?w13 ?z13)
           (zebra ?h14 ?w14 ?z14)
           (zebra ?h15 ?w15 ?z15)
           (zebra ?h16 ?w16 ?z16))



