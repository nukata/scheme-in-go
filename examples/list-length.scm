;; cf. R4RS s.6.9
(define list-length
  (lambda (obj)
    (call-with-current-continuation
     (lambda (return)
       (letrec ((r
                 (lambda (obj)
                   (cond ((null? obj) 0)
                         ((pair? obj)
                          (+ (r (cdr obj)) 1))
                         (else (return #f))))))
         (r obj))))))

(display (list-length '(1 2 3 4))) ; => 4
(newline)
(display (list-length '(a b . c))); => #f
(newline)
