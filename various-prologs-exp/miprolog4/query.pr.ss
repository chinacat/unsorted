#lang scheme

(require "prolog.rkt")

(<- (main) (query (?c1 ?d1 ?c2 ?d2)))

(<- (query (?c1 ?d1 ?c2 ?d2))
    (density ?c1 ?d1)
    (density ?c2 ?d2)
    (> ?d1 ?d2)
    (< (* 20 ?d1) (* 21 ?d2)))

(<- (density ?c ?d) (pop ?c ?p) (area ?c ?a) (is ?d (/ (* ?p 100) ?a)))

(<- (pop china 8250))         (<- (area china 3380))
(<- (pop india 5863))         (<- (area india 1139))
(<- (pop ussr 2521))          (<- (area ussr 8708))
(<- (pop usa 2119))           (<- (area usa 3609))
(<- (pop indonesia 1276))     (<- (area indonesia 570))
(<- (pop japan 1097))         (<- (area japan 148))
(<- (pop brazil 1042))        (<- (area brazil 3288))
(<- (pop bangladesh 750))     (<- (area bangladesh 55))
(<- (pop pakistan 682))       (<- (area pakistan 311))
(<- (pop w_germany 620))      (<- (area w_germany 96))
(<- (pop nigeria 613))        (<- (area nigeria 373))
(<- (pop mexico 581))         (<- (area mexico 764))
(<- (pop uk 559))             (<- (area uk 86))
(<- (pop italy 554))          (<- (area italy 116))
(<- (pop france 525))         (<- (area france 213))
(<- (pop philippines 415))    (<- (area philippines 90))
(<- (pop thailand 410))       (<- (area thailand 200))
(<- (pop turkey 383))         (<- (area turkey 296))
(<- (pop egypt 364))          (<- (area egypt 386))
(<- (pop spain 352))          (<- (area spain 190))
(<- (pop poland 335))         (<- (area poland 121))
(<- (pop s_korea 335))        (<- (area s_korea 37))
(<- (pop iran 320))           (<- (area iran 628))
(<- (pop ethiopia 272))       (<- (area ethiopia 350))
(<- (pop argentina 251))      (<- (area argentina 1080))


(benchmark (main))



