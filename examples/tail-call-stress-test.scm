;; A stress test against tail calls
(define (foo n)
  (if (= 0 (remainder n 5000))
      (display "."))
  (if (= n 0)
      "ok"
    (foo (- n 1))))
(display (foo 5000000))
(newline)
