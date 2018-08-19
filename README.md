# Scheme in Go

- [x] Tail Call Optimization

- [x] Call with Current Continuation

- [ ] Invocation Trace in Non-Recursive Eval

## How to run

```
$ go build scheme.go
$ ./scheme examples/fib15.scm
987
$ cat examples/fib15.scm
(define (fib n)
  (if (< n 2)
      1
      (+ (fib (- n 1))
         (fib (- n 2)))))
(display (fib 15))
(newline)
$ ./scheme examples/nqueens.scm
((5 3 1 6 4 2) (4 1 5 2 6 3) (3 6 2 5 1 4) (2 4 6 1 3 5))
$ cat examples/yin-yang-puzzle.scm
;; The yin-yang puzzle 
;; cf. https://en.wikipedia.org/wiki/Call-with-current-continuation

(let* ((yin
        ((lambda (cc) (display "@") cc) (call/cc (lambda (c) c))))
       (yang
        ((lambda (cc) (display "*") cc) (call/cc (lambda (c) c)))))
  (yin yang))

;; => @*@**@***@****@...
$ ./scheme examples/yin-yang-puzzle.scm | head -c 50
@*@**@***@****@*****@******@*******@********@*****$
$ ./scheme
> (dump) ; the global environment and keywords will be displayed.
```
