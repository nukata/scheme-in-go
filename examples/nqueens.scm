;; N-Queens Solver in Scheme
(define (nqueens n)
  (letrec
      ((cons-range          ; 3 lst => ((3 . lst) (2 . lst) (1 . lst))
        (lambda (n lst)
          (if (= n 0)
              '()
              (cons (cons n lst)
                    (cons-range (- n 1) lst)))))
       (safe-positions?                ; (3 4 1) => #f i.e. conflicted
        (lambda (lst)
          (if (null? (cdr lst))
              #t
              (letrec
                  ((loop
                    (lambda (me high low rest)
                      (if (null? rest)
                          #t
                          (let ((target (car rest)))
                            (and (not (= target me))
                                 (not (= target high))
                                 (not (= target low))
                                 (loop me (+ high 1) (- low 1)
                                       (cdr rest))))))))
                (let ((me (car lst)))
                  (loop me (+ me 1) (- me 1)
                        (cdr lst)))))))
       (loop
        (lambda (lst result)
          (if (null? lst)
              result
              (let ((candidate (car lst)))
                (set! lst (cdr lst))
                (if (safe-positions? candidate)
                    (if (= (length candidate) n)
                        (set! result (cons candidate result))
                        (set! lst (append (cons-range n candidate)
                                          lst))))
                (loop lst
                      result))))))
    (loop (cons-range n '())
          '())))

(display (nqueens 6))
(newline)
;; => ((5 3 1 6 4 2) (4 1 5 2 6 3) (3 6 2 5 1 4) (2 4 6 1 3 5)
