(
    (42 42)
    (#t #t)
    (#f #f)
    ((let ((x 1)) x) 1)
    ((let ((x 1)) (let ((x 2)) x)) 2)
    ((let ((x 1)) (let ((x 2) (y x)) y)) 1)
    ((+ 1 2 3) 6)
    ((= 2 2) #t)
    ((= 2 3) #f)
    ((= 2 2 2) #t)
    ((= 2 2 3) #f)
    ((if (= 2 2) 1 2) 1)
    ((if (= 2 3) 1 2) 2)
    (((lambda (x y) (+ x y)) 1 2) 3)
    ((quote (1 2 3)) (1 2 3))
    ('() ())
    ((car '(1 2 3)) 1)
    ((cdr '(1 2 3)) (2 3))
    ((null? '()) #t)
    ((null? 1) #f)
)