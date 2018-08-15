/*
  Scheme-like Lisp in Go 1.10 by SUZUKI Hisao (H30.8/5 - H30.8/15)

  The Reader type and other portions are derived from
  Nukata Lisp in Go (https://github.com/nukata/lisp-in-go).
*/
package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"math"
	"os"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
)

const Version = 0.21

type Any = interface{}

// EofToken is a token which represents the end of file.
var EofToken = errors.New("#end-of-file")

// VoidToken is a token which represents nothing.
// (define v e) returns VoidToken.
var VoidToken = errors.New("#void")

// EvalError represents an error in evaluation.
type EvalError struct {
	Message string
	Trace   []string
}

// NewEvalError constructs a new EvalError.
func NewEvalError(msg string, x Any) *EvalError {
	return &EvalError{msg + ": " + Str(x), nil}
}

// err.Error() returns a textual representation of err.
// It is defined to comply with error interface.
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

// j.String() returns a textual representation of the list j.
func (j *Cell) String() string {
	return Str(j)
}

// j.Head() returns (car j) as *Cell.
func (j *Cell) Head() *Cell {
	return j.Car.(*Cell)
}

// j.Tail() returns (cdr j) as *Cell.
func (j *Cell) Tail() *Cell {
	return j.Cdr.(*Cell)
}

// (a b c).FoldL(x, fn) returns fn(fn(fn(x, a), b), c).
func (j *Cell) FoldL(x Any, fn func(Any, Any) Any) Any {
	for j != Nil {
		x = fn(x, j.Car)
		j = j.Tail()
	}
	return x
}

// (a b c d).CompareAll(fn) returns fn(a, b) && fn(b, c) && fn(c, d).
func (j *Cell) CompareAll(fn func(Any, Any) bool) bool {
	x := j.Car
	j = j.Tail()
	for j != Nil {
		y := j.Car
		if !fn(x, y) {
			return false
		}
		x = y
		j = j.Tail()
	}
	return true
}

//----------------------------------------------------------------------

// Sym represents a symbol or a keyword.
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

// NewSym2 constructs an interned symbol (or a keyword
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

// sym.String() returns a textual representation of sym.
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

var ConsSym = NewSym("cons")
var ListSym = NewSym("list")
var AppendSym = NewSym("append")

// Expression keywords

var AndSym = NewSym2("and", true)
var BeginSym = NewSym2("begin", true)
var DefineSym = NewSym2("define", true)
var IfSym = NewSym2("if", true)
var LambdaSym = NewSym2("lambda", true)
var LetSym = NewSym2("let", true)
var LetrecSym = NewSym2("letrec", true)
var QuasiquoteSym = NewSym2("quasiquote", true)
var QuoteSym = NewSym2("quote", true)
var SetExclSym = NewSym2("set!", true)
var UnquoteSym = NewSym2("unquote", true)
var UnquoteSplicingSym = NewSym2("unquote-splicing", true)

//----------------------------------------------------------------------

// Globals represents a global environment.
// An environment will be repsensented as the list
// ((symbol1 . value1) ... (symbolN . valueN) globals)
// where globals is an instance of Globals.
type Globals struct {
	Map   map[*Sym]Any
	Mutex sync.RWMutex
}

// gl.String() returns "#N-symbols" where N is the number of symbols in gl.
func (gl *Globals) String() string {
	return fmt.Sprintf("#%d-symbols", len(gl.Map))
}

// GetVar retrieves the value of sym from env.
func GetVar(sym *Sym, env *Cell) Any {
	j := env
	for j != Nil {
		switch x := j.Car.(type) {
		case *Cell:
			if x.Car == sym {
				return x.Cdr
			}
		case *Globals:
			x.Mutex.RLock()
			v, ok := x.Map[sym]
			x.Mutex.RUnlock()
			if ok {
				return v
			}
		default:
			panic(NewEvalError("invalid environment", env))
		}
		j = j.Tail()
	}
	panic(NewEvalError("undefined variable", sym))
}

// SetVar sets the value of sym in env to value.
func SetVar(sym *Sym, value Any, env *Cell) bool {
	j := env
	for j != Nil {
		switch x := j.Car.(type) {
		case *Cell:
			if x.Car == sym {
				x.Cdr = value
				return true
			}
		case *Globals:
			x.Mutex.Lock()
			_, ok := x.Map[sym]
			if ok {
				x.Map[sym] = value
			}
			x.Mutex.Unlock()
			if ok {
				return true
			}
		default:
			panic(NewEvalError("invalid environment", env))
		}
		j = j.Tail()
	}
	return false
}

// DefineVar defines sym as value in env.
func DefineVar(sym *Sym, value Any, env *Cell) {
	if env != Nil {
		if x, ok := env.Car.(*Globals); ok {
			x.Mutex.Lock()
			x.Map[sym] = value
			x.Mutex.Unlock()
			return
		}
	}
	panic(NewEvalError("not top level to define", sym))
}

//----------------------------------------------------------------------

// Expr represents a function which evaluates expressions to get the result.
type Expr struct {
	Parameters  Any // *Sym or *Cell
	Body        *Cell
	Environment *Cell
}

// expr.String() return "#[(s...)| e...| env]".
func (expr *Expr) String() string {
	return fmt.Sprintf("#[%v| %s| %v]",
		expr.Parameters,
		strListBody(expr.Body, -1, nil),
		expr.Environment)
}

// Subr represents an intrinsic subroutine.
type Subr = func(*Cell) Any

// ApplyType is a singleton type for the apply function.
type ApplyType struct{}

//----------------------------------------------------------------------

const stackTraceMaxLength = 10

func handlePanic(expression Any) {
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

// Eval evaluates expression in env.
// Eval will panic with an EvalError if it panics.
func Eval(expression Any, env *Cell) Any {
	defer handlePanic(expression)
	for {
		switch x := expression.(type) {
		case *Sym:
			return GetVar(x, env)
		case *Cell:
			xcar, xcdr := x.Car, x.Tail()
			switch f := xcar.(type) {
			case *Sym:
				if f.IsKeyword {
					switch f {
					case QuoteSym: // (quote e)
						return xcdr.Car
					case IfSym: // (if cond then [else])
						cond := Eval(xcdr.Car, env)
						b, ok := cond.(bool)
						if ok && !b { // if cond is #f
							xcdddr := xcdr.Tail().Tail()
							if xcdddr == Nil {
								return VoidToken
							} else {
								expression = xcdddr.Car
							}
						} else {
							expression = xcdr.Tail().Car
						}
					case BeginSym: // (begin e...)
						expression = EvalBegin(xcdr, env)
					case LambdaSym: // (lambda (v...) e...)
						return &Expr{xcdr.Car, xcdr.Tail(), env}
					case SetExclSym: // (set! sym val)
						sym := xcdr.Car.(*Sym)
						val := Eval(xcdr.Tail().Car, env)
						if SetVar(sym, val, env) {
							return VoidToken
						}
						panic(NewEvalError("undefined variable to set", sym))
					case DefineSym: // (define v e)
						EvalDefine(xcdr.Car, xcdr.Tail(), env)
						return VoidToken
					case LetSym: // (let ((v e)...) e...)
						bindings, body := xcdr.Head(), xcdr.Tail()
						expression, env = EvalLet(bindings, body, env)
					case LetrecSym: // (letrec ((v e)...) e...)
						bindings, body := xcdr.Head(), xcdr.Tail()
						expression, env = EvalLetrec(bindings, body, env)
					case AndSym: // (and e...)
						expression = EvalAnd(xcdr, env)
					case QuasiquoteSym: // (quasiquote e)
						expression = QqExpand(xcdr.Car)
					default:
						panic(NewEvalError("unknown keyword", f))
					}
					continue // go to next loop
				} else {
					xcar = Eval(f, env)
				}
			case *Cell:
				xcar = Eval(f, env)
			}
			// Evaluate each of xcdr and apply xcar to them.
			args := EvalList(xcdr, env)
		APPLY:
			for {
				switch fn := xcar.(type) {
				case *Expr:
					expression, env = ApplyExpr(fn, args)
					break APPLY
				case Subr:
					return fn(args)
				case *ApplyType: // (apply fun arg)
					xcar, args = args.Car, args.Tail().Head()
				default:
					panic(NewEvalError("unknown function", fn))
				}
			}
		default:
			return x // numbers, strings etc.
		}
	}
}

// EvalBegin('(e1 ... eN), env) evaluates e1 ... e(N-1) and returns eN.
func EvalBegin(j *Cell, env *Cell) Any {
	if j == Nil {
		return VoidToken
	}
	for {
		x := j.Car
		j = j.Tail()
		if j == Nil {
			return x // eN will be evaluated at the caller Eval.
		}
		Eval(x, env)
	}
}

// EvalAnd('(1 2 (+ 3 4)), env) returns (+ 3 4).
func EvalAnd(j *Cell, env *Cell) Any {
	if j == Nil {
		return true
	}
	for {
		x := j.Car
		j = j.Tail()
		if j == Nil {
			return x
		}
		result := Eval(x, env)
		b, ok := result.(bool)
		if ok && !b {
			return false
		}
	}
}

// EvalDefine(sym, body, env) defines sym as (car body) in env.
// EvalDefine('(sym (param...)), body, env) defines sym as
// (lambda (param ...) . body) in env.
func EvalDefine(sym Any, body *Cell, env *Cell) {
	var symbol *Sym
	var value Any
	switch s := sym.(type) {
	case *Sym:
		symbol = s
		value = Eval(body.Car, env)
	case *Cell:
		symbol = s.Car.(*Sym)
		params := s.Cdr
		value = &Expr{params, body, env}
	default:
		panic(NewEvalError("invalid variable to define", sym))
	}
	DefineVar(symbol, value, env)
}

// EvalLet('((v a)...), (e...), env) evaluates ((lambda (v...) e...) a...).
func EvalLet(bindings *Cell, body *Cell, env *Cell) (Any, *Cell) {
	var syms *Cell = Nil
	var vals *Cell = Nil
	for j := bindings; j != Nil; j = j.Tail() {
		jcar := j.Head()
		syms = &Cell{jcar.Car, syms}
		vals = &Cell{jcar.Tail().Car, vals}
	}
	expr := &Expr{syms, body, env}
	return ApplyExpr(expr, EvalList(vals, env))
}

// EvalLetrec('((v a)...), (e...), env) evaluates
// ((lambda (v...) (set! v a)... e...) <void>...).
func EvalLetrec(bindings *Cell, body *Cell, env *Cell) (Any, *Cell) {
	var syms *Cell = Nil
	var voids *Cell = Nil
	for j := bindings; j != Nil; j = j.Tail() {
		jcar := j.Head()
		syms = &Cell{jcar.Car, syms}
		voids = &Cell{VoidToken, voids}
		set := &Cell{SetExclSym, &Cell{jcar.Car, &Cell{jcar.Tail().Car, Nil}}}
		body = &Cell{set, body}
	}
	expr := &Expr{syms, body, env}
	return ApplyExpr(expr, voids)
}

// EvalList('((+ 1 2) 3 (+ 4 5)), env) returns (3 3 9).
func EvalList(args *Cell, env *Cell) *Cell {
	var result Any = Nil
	p := &result
	for j := args; j != Nil; j = j.Tail() {
		v := Eval(j.Car, env)
		x := &Cell{v, Nil}
		*p = x
		p = &x.Cdr
	}
	return result.(*Cell)
}

// PairList((sym1...), (val1...), env) returns ((sym1 . val1)... . env).
// PairList(sym, (val1...), env) returns ((sym . (val1...)) . env).
func PairList(symbols Any, values *Cell, env *Cell) *Cell {
	switch s := symbols.(type) {
	case *Sym:
		return &Cell{&Cell{s, values}, env}
	case *Cell:
		var result Any = Nil
		p := &result
		v := values
		for s != Nil {
			x := &Cell{&Cell{s.Car.(*Sym), v.Car}, Nil}
			*p = x
			p = &x.Cdr
			scdr, ok := s.Cdr.(*Cell)
			if ok {
				s = scdr
				v = v.Tail()
			} else { // symbols = (v1 .. vN . vRest)
				*p = &Cell{&Cell{s.Cdr.(*Sym), v.Cdr}, env}
				return result.(*Cell)
			}
		}
		*p = env
		return result.(*Cell)
	}
	panic(NewEvalError("invalid symbol(s)", symbols))
}

// ApplyExpr evaluates fn with args and returns the tail expression and env.
func ApplyExpr(fn *Expr, args *Cell) (Any, *Cell) {
	env := PairList(fn.Parameters, args, fn.Environment)
	return EvalBegin(fn.Body, env), env
}

//----------------------------------------------------------------------
// Quasi-Quotation

// QqExpand expands x of any quasi-quote `x into the equivalent S-expression.
func QqExpand(x Any) Any {
	return qqExpand0(x, 0) // Begin with the nesting level 0.
}

// QqQuote quotes x so that the result evaluates to x.
func QqQuote(x Any) Any {
	if x == Nil {
		return Nil
	}
	switch x.(type) {
	case *Sym, *Cell:
		return &Cell{QuoteSym, &Cell{x, Nil}}
	default:
		return x
	}
}

func qqExpand0(x Any, level int) Any {
	if j, ok := x.(*Cell); ok {
		if j == Nil {
			return Nil
		}
		if j.Car == UnquoteSym { // ,a
			if level == 0 {
				return j.Tail().Car // ,a => a
			}
		}
		t := qqExpand1(j, level)
		if t.Cdr == Nil {
			if k, ok := t.Car.(*Cell); ok {
				if k.Car == ListSym || k.Car == ConsSym {
					return k
				}
			}
		}
		return &Cell{AppendSym, t}
	} else {
		return QqQuote(x)
	}
}

// qqExpand1 expands x of `x so that the result can be used as an argument of
// append.  Example 1: (,a b) => ((list a 'b))
//          Example 2: (,a ,@(cons 2 3)) => ((cons a (cons 2 3)))
func qqExpand1(x Any, level int) *Cell {
	if j, ok := x.(*Cell); ok {
		if j == Nil {
			return &Cell{Nil, Nil}
		}
		switch j.Car {
		case UnquoteSym: // ,a
			if level == 0 {
				return j.Tail() // ,a => (a)
			}
			level--
		case QuasiquoteSym: // `a
			level++
		}
		h := qqExpand2(j.Car, level)
		t := qqExpand1(j.Cdr, level) // != Nil
		if t.Car == Nil && t.Cdr == Nil {
			return &Cell{h, Nil}
		} else if hc, ok := h.(*Cell); ok {
			if hc.Car == ListSym {
				if tcar, ok := t.Car.(*Cell); ok {
					if tcar.Car == ListSym {
						hh := qqConcat(hc, tcar.Cdr)
						return &Cell{hh, t.Cdr}
					}
				}
				if hcdr, ok := hc.Cdr.(*Cell); ok {
					hh := qqConsCons(hcdr, t.Car)
					return &Cell{hh, t.Cdr}
				}
			}
		}
		return &Cell{h, t}
	} else {
		return &Cell{QqQuote(x), Nil}
	}
}

// (1 2), (3 4) => (1 2 3 4)
func qqConcat(x *Cell, y Any) Any {
	if x == Nil {
		return y
	} else {
		return &Cell{x.Car, qqConcat(x.Tail(), y)}
	}
}

// (1 2 3), "a" => (cons 1 (cons 2 (cons 3 "a")))
func qqConsCons(x *Cell, y Any) Any {
	if x == Nil {
		return y
	} else {
		return &Cell{ConsSym, &Cell{x.Car,
			&Cell{qqConsCons(x.Tail(), y), Nil}}}
	}
}

// qqExpand2 expands x.car (= y) of `x so that the result can be used as an
// argument of append.
// Examples: ,a => (list a); ,@(foo 1 2) => (foo 1 2); b => (list 'b)
func qqExpand2(y Any, level int) Any {
	if j, ok := y.(*Cell); ok {
		if j == Nil {
			return &Cell{ListSym, &Cell{Nil, Nil}} // (list nil)
		}
		switch j.Car {
		case UnquoteSym: // ,a
			if level == 0 {
				return &Cell{ListSym, j.Cdr} // ,a => (list a)
			}
			level--
		case UnquoteSplicingSym: // ,@a
			if level == 0 {
				return j.Tail().Car // ,@a => a
			}
			level--
		case QuasiquoteSym: // `a
			level++
		}
	}
	return &Cell{ListSym, &Cell{qqExpand0(y, level), Nil}}
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
// If the input runs out, it will return EofToken and nil.
// If an error happens, it will return Nil and the error.
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

// MakeGlobalEnv constructs an environment which contains built-in values.
func MakeGlobalEnv() *Cell {
	gl := &Globals{Map: make(map[*Sym]Any)}
	result := &Cell{gl, Nil}
	__, m := NewSym, gl.Map

	m[__("car")] = func(x *Cell) Any {
		return x.Head().Car
	}
	m[__("cdr")] = func(x *Cell) Any {
		return x.Head().Cdr
	}
	m[__("cons")] = func(x *Cell) Any {
		obj1, obj2 := x.Car, x.Tail().Car
		return &Cell{obj1, obj2}
	}
	m[__("pair?")] = func(x *Cell) Any {
		a, ok := x.Car.(*Cell)
		return ok && a != nil
	}

	eqv := func(x *Cell) Any {
		obj1, obj2 := x.Car, x.Tail().Car
		return obj1 == obj2
	}
	m[__("eq?")] = eqv
	m[__("eqv?")] = eqv

	m[__("null?")] = func(x *Cell) Any {
		return x.Car == Nil
	}

	m[__("not")] = func(x *Cell) Any {
		a, ok := x.Car.(bool)
		return ok && !a
	}

	m[__("set-car!")] = func(x *Cell) Any {
		pair, obj := x.Head(), x.Tail().Car
		pair.Car = obj
		return VoidToken
	}
	m[__("set-cdr!")] = func(x *Cell) Any {
		pair, obj := x.Head(), x.Tail().Car
		pair.Cdr = obj
		return VoidToken
	}
	m[__("list")] = func(x *Cell) Any {
		return x
	}
	m[__("append")] = appendNLists
	m[__("length")] = func(x *Cell) Any {
		return x.Head().FoldL(0.0, func(a, b Any) Any {
			return a.(float64) + 1.0
		})
	}

	m[__("+")] = func(x *Cell) Any {
		return x.FoldL(0.0, func(a, b Any) Any {
			return a.(float64) + b.(float64)
		})
	}
	m[__("*")] = func(x *Cell) Any {
		return x.FoldL(1.0, func(a, b Any) Any {
			return a.(float64) * b.(float64)
		})
	}
	m[__("-")] = func(x *Cell) Any {
		a1 := x.Car.(float64)
		if x.Cdr == Nil {
			return -a1
		} else {
			return x.Tail().FoldL(a1, func(a, b Any) Any {
				return a.(float64) - b.(float64)
			})
		}
	}
	m[__("/")] = func(x *Cell) Any {
		a1 := x.Car.(float64)
		if x.Cdr == Nil {
			return 1 / a1
		} else {
			return x.Tail().FoldL(a1, func(a, b Any) Any {
				return a.(float64) / b.(float64)
			})
		}
	}

	m[__("remainder")] = func(x *Cell) Any {
		return math.Mod(x.Car.(float64), x.Tail().Car.(float64))
	}

	m[__("=")] = func(x *Cell) Any {
		return x.CompareAll(func(a, b Any) bool {
			return a.(float64) == b.(float64)
		})
	}
	m[__("<")] = func(x *Cell) Any {
		return x.CompareAll(func(a, b Any) bool {
			return a.(float64) < b.(float64)
		})
	}
	m[__(">")] = func(x *Cell) Any {
		return x.CompareAll(func(a, b Any) bool {
			return a.(float64) > b.(float64)
		})
	}
	m[__("<=")] = func(x *Cell) Any {
		return x.CompareAll(func(a, b Any) bool {
			return a.(float64) <= b.(float64)
		})
	}
	m[__(">=")] = func(x *Cell) Any {
		return x.CompareAll(func(a, b Any) bool {
			return a.(float64) >= b.(float64)
		})
	}

	m[__("write")] = func(x *Cell) Any {
		fmt.Print(Str2(x.Car, true))
		return VoidToken
	}
	m[__("display")] = func(x *Cell) Any {
		fmt.Print(Str2(x.Car, false))
		return VoidToken
	}
	m[__("newline")] = func(x *Cell) Any {
		fmt.Println()
		return VoidToken
	}

	m[__("apply")] = &ApplyType{}
	m[__("eval")] = func(x *Cell) Any {
		return Eval(x.Car, x.Tail().Head())
	}

	m[__("interaction-environment")] = func(x *Cell) Any {
		return result
	}
	m[__("dump")] = func(x *Cell) Any {
		j := Nil
		symLock.RLock()
		for _, sym := range symbols {
			if sym.IsKeyword {
				j = &Cell{sym, j}
			}
		}
		symLock.RUnlock()
		gl.Mutex.RLock()
		for sym, val := range gl.Map {
			j = &Cell{&Cell{sym, val}, j}
		}
		gl.Mutex.RUnlock()
		return j
	}
	m[__("*version*")] = &Cell{Version,
		&Cell{fmt.Sprintf("%s %s/%s",
			runtime.Version(), runtime.GOOS, runtime.GOARCH),
			&Cell{"Scheme-like Lisp", Nil}}}

	return result
}

func appendNLists(x *Cell) Any {
	car, tail := x.Car, x.Tail()
	if tail == Nil {
		return car
	} else {
		return append2Lists(car.(*Cell), appendNLists(tail))
	}
}

func append2Lists(list *Cell, obj Any) Any {
	var result Any = Nil
	p := &result
	for j := list; j != Nil; j = j.Tail() {
		x := &Cell{j.Car, Nil}
		*p = x
		p = &x.Cdr
	}
	*p = obj
	return result
}

//----------------------------------------------------------------------

// SafeEval evaluates exp in env and returns the result and nil.
// If an error happens, it returns Nil and the error.
func SafeEval(exp Any, env *Cell) (result Any, err Any) {
	defer func() {
		if e := recover(); e != nil {
			result, err = Nil, e
		}
	}()
	return Eval(exp, env), nil
}

// Read-Eval-Print Loop of the interpreter
func ReadEvalPrintLoop(env *Cell) {
	rr := NewReader(os.Stdin)
	for {
		os.Stdout.WriteString("> ")
		x, err := rr.Read()
		if err == nil {
			if x == EofToken {
				return
			}
			x, err = SafeEval(x, env)
			if err == nil && x != VoidToken {
				fmt.Println(Str(x))
			}
		}
		if err != nil {
			fmt.Println(err)
		}
	}
}

// Non-Interactive Read-Eval Loop of the interpreter
func ReadEvalLoop(input io.Reader, env *Cell) (result Any, err Any) {
	result = Nil
	rr := NewReader(input)
	for {
		x, err := rr.Read()
		if err == nil {
			if x == EofToken {
				return result, nil
			}
			result, err = SafeEval(x, env)
		}
		if err != nil {
			return nil, err
		}
	}
}

// Main runs each element of args as a name of Scheme script file.
// It ignores args[0].
// If it does not have args[1] or some element is "-", it begins REPL.
func Main(args []string) int {
	env := MakeGlobalEnv()
	if len(args) < 2 {
		args = []string{args[0], "-"}
	}
	var result Any = VoidToken
	for i, fileName := range args {
		if i == 0 {
			continue
		} else if fileName == "-" {
			ReadEvalPrintLoop(env)
			fmt.Println("Goodbye")
			result = VoidToken
		} else {
			var err Any
			file, err := os.Open(fileName)
			if err == nil {
				result, err = ReadEvalLoop(file, env)
				file.Close()
			}
			if err != nil {
				fmt.Println(err)
				return 1
			}
		}
	}
	if result != VoidToken {
		fmt.Println(Str(result))
	}
	return 0
}

func main() {
	os.Exit(Main(os.Args))
}
