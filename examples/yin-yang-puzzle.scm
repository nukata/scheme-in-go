;; The yin-yang puzzle 
;; cf. https://en.wikipedia.org/wiki/Call-with-current-continuation

(let* ((yin
        ((lambda (cc) (display "@") cc) (call/cc (lambda (c) c))))
       (yang
        ((lambda (cc) (display "*") cc) (call/cc (lambda (c) c)))))
  (yin yang))

;; => @*@**@***@****@...
