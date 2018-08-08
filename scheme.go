/*
  Scheme-like Lisp in Go 1.10 by SUZUKI Hisao (H30.8/5 -)

  The Reader type and other potions are derived from
  Nukata Lisp in Go (https://github.com/nukata/lisp-in-go).
*/
package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"os"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
)

const Version = 0.03

type Any = interface{}

// EofToken is a token which represents the end of file.
var EofToken = errors.New("end of file")

// NoneToken is a token which represents nothing.
// (define v e) returns NoneToken.
var NoneToken = errors.New("none")

// EvalError implements an `error` in evaluation.
type EvalError struct {
	Message string
	Trace   []string
}

// NewEvalError constructs a new EvalError.
func NewEvalError(msg string, x Any) *EvalError {
	return &EvalError{msg + ": " + Str(x), nil}
}

// err.Error() returns a textual representation of err.
// It is defined to comply with `error` interface.
func (err *EvalError) Error() string {
	s := "EvalError: " + err.Message
	for _, line := range err.Trace {
		s += "\n\t" + line
	}
	return s
}

//----------------------------------------------------------------------

// Cell represents a cons cell.
// &Cell{car, cdr} works as the "cons" operation.
type Cell struct {
	Car Any
	Cdr Any
}

// Nil represents the empty list ().
var Nil *Cell = nil

// List(a, b, c) builds a list of Cells: (a . (b . (c . ()))).
func List(j ...Any) *Cell {
	var result Any = Nil
	p := &result
	for _, v := range j {
		x := &Cell{v, Nil}
		*p = x
		p = &x.Cdr
	}
	return result.(*Cell)
}

// j.String() returns a textual representation of the list j.
func (j *Cell) String() string {
	return Str(j)
}

// j.Head() is (car j) as *Cell.
func (j *Cell) Head() *Cell {
	return j.Car.(*Cell)
}

// j.Tail() is (cdr j) as *Cell.
func (j *Cell) Tail() *Cell {
	return j.Cdr.(*Cell)
}

//----------------------------------------------------------------------

// Sym represents a symbol or an expression keyword.
// &Sym{name, false} constructs a symbol which is not interned yet.
type Sym struct {
	Name      string
	IsKeyword bool
}

// symbols is the table of interned symbols.
var symbols = make(map[string]*Sym)

// symLock is the exclusive lock for the table.
var symLock sync.RWMutex

// NewSym constructs an interned symbol for name.
func NewSym(name string) *Sym {
	return NewSym2(name, false)
}

// NewSym2 constructs an interned symbol (or an expression keyword
// if iskeyword is true on its first contruction) for name.
func NewSym2(name string, isKeyword bool) *Sym {
	symLock.Lock()
	sym, ok := symbols[name]
	if !ok {
		sym = &Sym{name, isKeyword}
		symbols[name] = sym
	}
	symLock.Unlock()
	return sym
}

// IsInterned returns true if sym is interned.
func (sym *Sym) IsInterned() bool {
	symLock.RLock()
	s, ok := symbols[sym.Name]
	symLock.RUnlock()
	return ok && s == sym
}

// sym.String() returns a textual representation of the Symbol sym.
func (sym *Sym) String() string {
	if sym.IsInterned() {
		return sym.Name
	} else {
		return "#:" + sym.Name
	}
}

// Defined symbols

var BackQuoteSym = NewSym("`")
var CommaAtSym = NewSym(",@")
var CommaSym = NewSym(",")
var DotSym = NewSym(".")
var LeftParenSym = NewSym("(")
var RightParenSym = NewSym(")")
var SingleQuoteSym = NewSym("'")

// Expression keywords

var BeginSym = NewSym2("begin", true)
var DefineSym = NewSym2("define", true)
var IfSym = NewSym2("if", true)
var LambdaSym = NewSym2("lambda", true)
var QuasiquoteSym = NewSym2("quasiquote", true)
var QuoteSym = NewSym2("quote", true)
var SetExclSym = NewSym2("set!", true)
var UnquoteSym = NewSym2("unquote", true)
var UnquoteSplicingSym = NewSym2("unquote-splicing", true)

//----------------------------------------------------------------------

// Env represents an environment, i.e., a list of symbol-value pairs.
type Env struct {
	Symbol *Sym
	Value  Any
	Next   *Env
}

// env.String() returns "{sym1=val1; sym2=val2; ...; symN=valN}".
func (env *Env) String() string {
	ss := make([]string, 0, 10)
	for p := env; p != nil; p = p.Next {
		s := fmt.Sprintf("%v=%v", p.Symbol, p.Value)
		ss = append(ss, s)
	}
	return "{" + strings.Join(ss, "; ") + "}"
}

// env.ShortString() returns a short representation of the env.
func (env *Env) ShortString(items int) string {
	ss := make([]string, 0, 10)
	count := items
	for p := env; p != nil; p = p.Next {
		count--
		if count == 0 {
			ss = append(ss, "...")
			break
		}
		s := fmt.Sprintf("%v", p.Symbol)
		ss = append(ss, s)
	}
	return "{" + strings.Join(ss, " ") + "}"
}

// env.Prepend((sym1...), (val1...)) constructs a new environment
// {sym1=val1; ...; the contents of env}.
// env.Prepend(sym, (val1...)) constructs a new environment
// {sym=(val1...); the contents of env}.
func (env *Env) Prepend(symbols Any, values *Cell) *Env {
	switch s := symbols.(type) {
	case *Sym:
		return &Env{s, values, env}
	case *Cell:
		var result *Env = nil
		p := &result
		v := values
		for s != Nil {
			x := &Env{s.Car.(*Sym), v.Car, nil}
			*p = x
			p = &x.Next
			cdr, ok := s.Cdr.(*Cell)
			if ok {
				s = cdr
				v = v.Tail()
			} else { // (v1 v2 . v3)
				*p = &Env{s.Cdr.(*Sym), v.Cdr, env}
				return result
			}
		}
		*p = env
		return result
	}
	panic("not *Sym nor *Cell")
}

// Get the value for symbol.  It returns NoneToken if not found the symbol.
func (env *Env) GetValueFor(symbol *Sym) Any {
	for p := env; p != nil; p = p.Next {
		if p.Symbol == symbol {
			return p.Value
		}
	}
	return NoneToken
}

// Set the value for symbol.  It returns false if not found the symbol.
func (env *Env) SetValueFor(symbol *Sym, value Any) bool {
	for p := env; p != nil; p = p.Next {
		if p.Symbol == symbol {
			p.Value = value
			return true
		}
	}
	return false
}

//----------------------------------------------------------------------

// Expr represents a function which evaluates expressions to get the result.
type Expr struct {
	Parameters  Any // *Sym or *Cell
	Body        *Cell
	Environment *Env
}

// expr.String() return "#[(s...) e... {s s s ...}]".
func (expr *Expr) String() string {
	return fmt.Sprintf("#[%v %s %s]",
		expr.Parameters,
		strListBody(expr.Body, -1, nil),
		expr.Environment.ShortString(4))
}

// Subr represents an intrinsic subroutine.
type Subr = func(*Cell) Any

//----------------------------------------------------------------------

// Interp represents a core of the interpreter.
type Interp struct {
	Globals map[*Sym]Any
}

// NewInterp constructs an interpreter and sets built-in functions etc. as
// the global values of symbols within the interpreter.
func NewInterp() *Interp {
	interp := &Interp{Globals: make(map[*Sym]Any)}

	interp.Def("car",
		func(x *Cell) Any {
			return x.Head().Car
		})
	interp.Def("cdr",
		func(x *Cell) Any {
			return x.Head().Cdr
		})
	interp.Def("cons",
		func(x *Cell) Any {
			return &Cell{x.Car, x.Tail().Car}
		})
	interp.Def("eq?",
		func(x *Cell) Any {
			return x.Car == x.Cdr
		})
	interp.Def("pair?",
		func(x *Cell) Any {
			a, ok := x.Car.(*Cell)
			return ok && a != nil
		})

	interp.Def("+",
		func(x *Cell) Any {
			return x.Car.(float64) + x.Tail().Car.(float64)
		})
	interp.Def("interaction-environment",
		func(x *Cell) Any {
			var r *Env = nil
			for key, value := range interp.Globals {
				r = &Env{key, value, r}
			}
			return r
		})
	interp.Def("*version*",
		List(Version,
			fmt.Sprintf("%s %s/%s",
				runtime.Version(), runtime.GOOS, runtime.GOARCH),
			"Scheme-like Lisp"))
	return interp
}

func (interp *Interp) Def(name string, value Any) {
	symbol := NewSym(name)
	interp.Globals[symbol] = value
}

const stackTraceMaxLength = 10

func handlePanic(interp *Interp, expression Any) {
	if err := recover(); err != nil {
		ex, ok := err.(*EvalError)
		if !ok {
			ex = &EvalError{fmt.Sprintf("%v", err), nil}
		}
		if ex.Trace == nil {
			ex.Trace = make([]string, 0, stackTraceMaxLength)
		}
		if len(ex.Trace) < stackTraceMaxLength {
			ex.Trace = append(ex.Trace, Str(expression))
		}
		panic(ex)
	}
}

// Eval always panics with an `error` if it panics.
func (interp *Interp) Eval(expression Any, env *Env) Any {
	defer handlePanic(interp, expression)
	switch x := expression.(type) {
	case *Sym:
		r := env.GetValueFor(x)
		if r == NoneToken {
			g, ok := interp.Globals[x]
			if !ok {
				panic(NewEvalError("undefined variable", x))
			}
			r = g
		}
		return r
	case *Cell:
		xcar := x.Car
		switch f := xcar.(type) {
		case *Sym:
			if f.IsKeyword {
				if f == QuoteSym {
					return x.Tail().Car
				} else if f == IfSym { // (if e1 e2 e3)
					e1 := interp.Eval(x.Tail().Car, env)
					b, ok := e1.(bool)
					if ok && !b { // if e1 is #f
						return interp.Eval(x.Tail().Tail().Tail().Car, env)
					} else {
						return interp.Eval(x.Tail().Tail().Car, env)
					}
				} else if f == BeginSym { // (begin e...)
					return interp.EvalBegin(x.Tail(), env)
				} else if f == LambdaSym { // (lambda (v...) e...)
					return &Expr{x.Tail().Car, x.Tail().Tail(), env}
				} else if f == SetExclSym { // (set! v e)
					sym := x.Tail().Car.(*Sym)
					e1 := interp.Eval(x.Tail().Tail().Car, env)
					if env.SetValueFor(sym, e1) {
						return NoneToken
					}
					_, ok := interp.Globals[sym]
					if ok {
						interp.Globals[sym] = e1
						return NoneToken
					}
					panic(NewEvalError("undefined variable to set", x))
				} else if f == DefineSym { // (define v e)
					if env != nil {
						panic(NewEvalError("not top level to define", f))
					}
					e1 := interp.Eval(x.Tail().Tail().Car, env)
					interp.Globals[x.Tail().Car.(*Sym)] = e1
					return NoneToken
				}
				panic(NewEvalError("unknown keyword", f))
			} else {
				xcar = interp.Eval(f, env)
			}
			break
		case *Cell:
			xcar = interp.Eval(f, env)
		}
		return interp.Apply(xcar, interp.EvalList(x.Tail(), env))
	}
	return expression
}

// EvalBegin('((+ 1 2) 3 (+ 4 5)), GlobalEnv) returns 9 (= 4 + 5).
func (interp *Interp) EvalBegin(j *Cell, env *Env) Any {
	var result Any = Nil
	for j != Nil {
		result = interp.Eval(j.Car, env)
		j = j.Tail()
	}
	return result
}

// EvalList('((+ 1 2) 3 (+ 4 5)), GlobalEnv) returns (3 3 9).
func (interp *Interp) EvalList(args *Cell, env *Env) *Cell {
	var result Any = Nil
	p := &result
	for j := args; j != Nil; j = j.Tail() {
		v := interp.Eval(j.Car, env)
		x := &Cell{v, Nil}
		*p = x
		p = &x.Cdr
	}
	return result.(*Cell)
}

func (interp *Interp) Apply(function Any, args *Cell) Any {
	switch f := function.(type) {
	case *Expr:
		env := f.Environment.Prepend(f.Parameters, args)
		return interp.EvalBegin(f.Body, env)
	case Subr:
		return f(args)
	}
	panic(NewEvalError("unknown function", function))
}

//----------------------------------------------------------------------

// Reader represents a reader of expressions.
type Reader struct {
	scanner *bufio.Scanner
	token   Any      // the current token
	tokens  []string // tokens read from the current line
	index   int      // the next index of tokens
	line    string   // the current line
	lineNo  int      // the current line number
	erred   bool     // a flag if an error has happened
}

// NewReader constructs a reader which will read expressions from r.
func NewReader(r io.Reader) *Reader {
	scanner := bufio.NewScanner(r)
	return &Reader{scanner, nil, nil, 0, "", 0, false}
}

// Read reads an expression and returns it and nil.
// If the input runs out, it returns EofToken and nil.
// If an error happens, it returns Nil and the error.
func (rr *Reader) Read() (result Any, err Any) {
	defer func() {
		if e := recover(); e != nil {
			result, err = Nil, e
		}
	}()
	rr.readToken()
	return rr.parseExpression(), nil
}

func (rr *Reader) newSynatxError(msg string, arg Any) *EvalError {
	rr.erred = true
	s := fmt.Sprintf("syntax error: %s -- %d: %s",
		fmt.Sprintf(msg, arg), rr.lineNo, rr.line)
	return &EvalError{s, nil}
}

func (rr *Reader) parseExpression() Any {
	switch rr.token {
	case LeftParenSym: // (a b c)
		rr.readToken()
		return rr.parseListBody()
	case SingleQuoteSym: // 'a => (quote a)
		rr.readToken()
		return &Cell{QuoteSym, &Cell{rr.parseExpression(), Nil}}
	case BackQuoteSym: // `a => (quasiquote a)
		rr.readToken()
		return &Cell{QuasiquoteSym, &Cell{rr.parseExpression(), Nil}}
	case CommaSym: // ,a => (unquote a)
		rr.readToken()
		return &Cell{UnquoteSym, &Cell{rr.parseExpression(), Nil}}
	case CommaAtSym: // ,@a => (unquote-splicing a)
		rr.readToken()
		return &Cell{UnquoteSplicingSym, &Cell{rr.parseExpression(), Nil}}
	case DotSym, RightParenSym:
		panic(rr.newSynatxError("unexpected \"%v\"", rr.token))
	default:
		return rr.token
	}
}

func (rr *Reader) parseListBody() *Cell {
	if rr.token == EofToken {
		panic(rr.newSynatxError("unexpected EOF%s", ""))
	} else if rr.token == RightParenSym {
		return Nil
	} else {
		e1 := rr.parseExpression()
		rr.readToken()
		var e2 Any
		if rr.token == DotSym { // (a . b)
			rr.readToken()
			e2 = rr.parseExpression()
			rr.readToken()
			if rr.token != RightParenSym {
				panic(rr.newSynatxError("\")\" expected: %v", rr.token))
			}
		} else {
			e2 = rr.parseListBody()
		}
		return &Cell{e1, e2}
	}
}

// readToken reads the next token and set it to rr.token.
func (rr *Reader) readToken() {
	// Read the next line if the line ends or an error happened last time.
	for len(rr.tokens) <= rr.index || rr.erred {
		rr.erred = false
		if rr.scanner.Scan() {
			rr.line = rr.scanner.Text()
			rr.lineNo++
		} else {
			if err := rr.scanner.Err(); err != nil {
				panic(err)
			}
			rr.token = EofToken
			return
		}
		mm := tokenPat.FindAllStringSubmatch(rr.line, -1)
		tt := make([]string, 0, len(mm)*3/5) // Estimate 40% will be spaces.
		for _, m := range mm {
			if m[1] != "" {
				tt = append(tt, m[1])
			}
		}
		rr.tokens = tt
		rr.index = 0
	}
	// Read the next token.
	s := rr.tokens[rr.index]
	rr.index++
	if s[0] == '"' {
		n := len(s) - 1
		if n < 1 || s[n] != '"' {
			panic(rr.newSynatxError("bad string: '%s'", s))
		}
		s = s[1:n]
		s = escapePat.ReplaceAllStringFunc(s, func(t string) string {
			r, ok := escapes[t] // r, err := strconv.Unquote("'" + t + "'")
			if !ok {
				r = t // Leave any invalid escape sequence as it is.
			}
			return r
		})
		rr.token = s
		return
	}
	f, err := strconv.ParseFloat(s, 64) // Try to read s as a float64.
	if err == nil {
		rr.token = f
		return
	}
	if s == "#f" {
		rr.token = false
		return
	} else if s == "#t" {
		rr.token = true
		return
	}
	rr.token = NewSym(s)
	return
}

// tokenPat is a regular expression to split a line to tokens.
var tokenPat = regexp.MustCompile(`\s+|;.*$|("(\\.?|.)*?"|,@?|[^()'` +
	"`" + `~"; \t]+|.)`)

// escapePat is a reg. expression to take an escape sequence out of a string.
var escapePat = regexp.MustCompile(`\\(.)`)

// escapes is a mapping from an escape sequence to its string value.
var escapes = map[string]string{
	`\\`: `\`,
	`\"`: `"`,
	`\n`: "\n", `\r`: "\r", `\f`: "\f", `\b`: "\b", `\t`: "\t", `\v`: "\v",
}

//----------------------------------------------------------------------

// Str(x) returns a textual representation of Any x.
func Str(x Any) string {
	return Str2(x, true)
}

// Str2(x, quoteString) returns a textual representation of Any x.
// If quoteString is true, a string will be represented with quotes.
func Str2(x Any, quoteString bool) string {
	return str4(x, quoteString, -1, nil)
}

func str4(a Any, quoteString bool, count int, printed map[*Cell]bool) string {
	switch x := a.(type) {
	case bool:
		if x {
			return "#t"
		} else {
			return "#f"
		}
	case *Cell:
		if x == Nil {
			return "()"
		}
		return "(" + strListBody(x, count, printed) + ")"
	case string:
		if quoteString {
			return strconv.Quote(x)
		} else {
			return x
		}
	}
	return fmt.Sprintf("%v", a)
}

const thresholdOfEllipsisForCircularLists = 4

func strListBody(x *Cell, count int, printed map[*Cell]bool) string {
	if printed == nil {
		printed = make(map[*Cell]bool)
	}
	if count < 0 {
		count = thresholdOfEllipsisForCircularLists
	}
	s := make([]string, 0, 10)
	y := x
	for y != Nil {
		if _, ok := printed[y]; ok {
			count--
			if count < 0 {
				s = append(s, "...") // ellipsis for a circular list
				return strings.Join(s, " ")
			}
		} else {
			printed[y] = true
			count = thresholdOfEllipsisForCircularLists
		}
		s = append(s, str4(y.Car, true, count, printed))
		if cdr, ok := y.Cdr.(*Cell); ok {
			y = cdr
		} else {
			s = append(s, ".")
			s = append(s, str4(y.Cdr, true, count, printed))
			break
		}
	}
	y = x
	for y != Nil {
		delete(printed, y)
		if cdr, ok := y.Cdr.(*Cell); ok {
			y = cdr
		} else {
			break
		}
	}
	return strings.Join(s, " ")
}

//----------------------------------------------------------------------

// SafeEval evaluates an expression in `env` and returns the result and nil.
// If an error happens, it returns Nil and the error.
func (interp *Interp) SafeEval(exp Any, env *Env) (result Any, err Any) {
	defer func() {
		if e := recover(); e != nil {
			result, err = Nil, e
		}
	}()
	return interp.Eval(exp, env), nil
}

// Read-Eval-Print Loop of the interpreter
func (interp *Interp) ReadEvalPrintLoop(env *Env) {
	rr := NewReader(os.Stdin)
	for {
		os.Stdout.WriteString("> ")
		x, err := rr.Read()
		if err == nil {
			if x == EofToken {
				return
			}
			x, err = interp.SafeEval(x, env)
			if err == nil && x != NoneToken {
				fmt.Println(Str(x))
			}
		}
		if err != nil {
			fmt.Println(err)
		}
	}
}

func (interp *Interp) ReadEvalLoop(input io.Reader, env *Env) Any {
	var result Any = Nil
	rr := NewReader(input)
	for {
		x, err := rr.Read()
		if err == nil {
			if x == EofToken {
				return result
			}
			result = interp.Eval(x, env)
		} else {
			panic(err)
		}
	}
}

func main() {
	interp := NewInterp()

	var x = List(7, 8, true, false, 9)
	fmt.Println(x) // => (7 8 #t #f 9)
	x.Tail().Tail().Car = x
	fmt.Println(Str(x)) // => (7 8 (7 8 (7 ...) #f 9) #f 9)

	var __ = NewSym
	a := interp.Eval(__("*version*"), nil)
	fmt.Println(a) // => the value of *version*
	a = interp.Eval(List(__("cdr"), List(QuoteSym, List(1, 2, 3))), nil)
	fmt.Println(a) // => (2 3) i.e. the value of (cdr '(1 2 3))

	input := strings.NewReader("(+ 5 6)")
	a = interp.ReadEvalLoop(input, nil)
	fmt.Println(Str(a)) // => 11 i.e. the value of (+ 5 6)

	interp.ReadEvalPrintLoop(nil)
}
