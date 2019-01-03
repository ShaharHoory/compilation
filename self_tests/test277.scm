(define fact (lambda (n)
        (if (zero? n)
        1
        (* n (fact (- n 1))))))


(let ((lst  `(,(fact 10) ,(fact 7) ,(fact 6) ,(fact 20))))
    `(some facts are: ,@lst))