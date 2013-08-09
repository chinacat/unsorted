#lang scheme

(define-syntax (foo stx)
  (syntax-case stx ()
    [(_ term)
     (syntax-case #'term ()
       [(s0 s ... . r)
        (equal? (syntax-property #'term 'paren-shape) #\[)
        #'(quote (wrapped (s0 s ... . r)))]
       [any
        #'(quote (normal any))])]))



