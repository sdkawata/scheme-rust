(define (f x)
    (define (g x) (+ x 2))
    (g x))
(display (f 3))