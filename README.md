# Scheme in Go

- [ ] Tail Call Optimization

- [ ] Call with Current Continuation

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
$ ./scheme
> (dump) ; the global environment and keywords will be displayed.
```
