(
    (42 42)
    (1.5 1.5)
    (1. 1.)
    (#t #t)
    (#f #f)
    (#\space #\space)
    ((let ((x 1)) x) 1)
    ((let ((x 1)) (let ((x 2)) x)) 2)
    ((let ((x 1)) (let ((x 2) (y x)) y)) 1)
    ((let
        ((x 2))
        (+ (let ((x 1)) x) x)) 3)
    ((+ 1 2 3) 6)
    ((* 1 2 5) 10)
    ((- 3 2) 1)
    ((- 6 3 2) 1)
    ((= 2 2) #t)
    ((= 2 3) #f)
    ((= 2 2 2) #t)
    ((= 2 2 3) #f)
    ((begin 1 #t (+ 2 3)) 5)
    ((and #f 1) #f)
    ((and 1 2) 2)
    ((or #f #f #f) #f)
    ((or #f 2) 2)
    ((or 1 2 3) 1)
    ((if (= 2 2) 1 2) 1)
    ((if (= 2 3) 1 2) 2)
    (((lambda (x y) (+ x y)) 1 2) 3)
    ((quote (1 2 3)) (1 2 3))
    ('() ())
    ((car '(1 2 3)) 1)
    ((cdr '(1 2 3)) (2 3))
    ((cons 1 '()) (1))
    ((null? '()) #t)
    ((null? 1) #f)
    ((letrec
        ((sum (lambda (l) (if (null? l) 0 (+ (car l) (sum (cdr l)))))))
        (sum '(1 2 3)))
        6)
)