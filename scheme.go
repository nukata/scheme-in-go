/*
  Scheme in [Go 1.10] by SUZUKI Hisao (H30.8/5 - H30.8/19)

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

const Version = 0.40

type Any = interface{}

// EofToken is a token which represents the end of file.
var EofToken = errors.New("#end-of-file")

// VoidToken is a token which represents nothing.
// (define v e) returns VoidToken.
var VoidToken = errors.New("#void")

// EvalError represents an error in evaluation.
type EvalError struct {
	Message string
}

// NewEvalError constructs a new EvalError.
func NewEvalError(msg string, x Any) *EvalError {
	return &EvalError{msg + ": " + Str(x)}
}

// err.Error() returns a textual representation of err.
func (err *EvalError) Error() string {
	s := "EvalError: " + err.Message
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

// List(a, b, c) builds a list of Cells (a . (b . (c . ()))).
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

// (a b c d).Reverse() returns (d c b a).
func (j *Cell) Reverse() *Cell {
	result := Nil
	for j != Nil {
		result = &Cell{j.Car, result}
		j = j.Tail()
	}
	return result
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

// Expression keywords

var And_ = NewSym2("and", true)
var Arrow_ = NewSym2("=>", true)
var Begin_ = NewSym2("begin", true)
var Case_ = NewSym2("case", true)
var Cond_ = NewSym2("cond", true)
var Define_ = NewSym2("define", true)

//var Delay_ = NewSym2("delay", true)
//var Do_ = NewSym2("do", true)
var Else_ = NewSym2("else", true)
var If_ = NewSym2("if", true)
var Lambda_ = NewSym2("lambda", true)
var Let_ = NewSym2("let", true)
var Letrec_ = NewSym2("letrec", true)
var LetStar_ = NewSym2("let*", true)
var Or_ = NewSym2("or", true)
var Quasiquote_ = NewSym2("quasiquote", true)
var Quote_ = NewSym2("quote", true)
var SetQ_ = NewSym2("set!", true)
var Unquote_ = NewSym2("unquote", true)
var Unquote_splicing_ = NewSym2("unquote-splicing", true)

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

// expr.String() returns "#[(s...)| e...| env]".
func (expr *Expr) String() string {
	return fmt.Sprintf("#[%v| %s| %v]",
		expr.Parameters,
		strListBody(expr.Body, -1, nil),
		expr.Environment)
}

// Subr represents an intrinsic subroutine.
type Subr = func(*Cell) Any

// FSubr represents an intrinsic special-form subroutine.
type FSubr = func(args, env, cont *Cell) (result Any, env2, cont2 *Cell)

// ApplyType is a singleton type for the apply function.
type ApplyType struct{}

// CallCCType is a singleton type for the call/cc function.
type CallCCType struct{}

// EvalType is a singleton type for the eval function.
type EvalType struct{}

var Apply_ = &ApplyType{}
var Eval_ = &EvalType{}
var CallCC_ = &CallCCType{}

// Cont represents a continuation as a unary function.
type Cont struct {
	Continuation *Cell
}

// cont.String() returns a textual representation of cont.
func (cont *Cont) String() string {
	s := make([]string, 0, 10)
	for j := cont.Continuation; j != Nil; j = j.Tail() {
		s = append(s, fmt.Sprintf("%T", j.Car))
	}
	return "#<" + strings.Join(s, ";") + ">"
}

// NewCont copies a continuation k.
func NewCont(k *Cell) *Cell {
	var result Any = Nil
	p := &result
	for j := k; j != Nil; j = j.Tail() {
		var v Any
		switch x := j.Car.(type) {
		case *ApplyCont:
			v = &ApplyCont{x.Fun, x.Args, x.Evaluated, x.Env}
		case *IfCont:
			v = x // IfCont is immutable
		case *BeginCont:
			v = &BeginCont{x.Rest, x.Env}
		case *SetQCont:
			v = x // SetExclCont is immutable
		case *DefineCont:
			v = x // DefineCont is immutable
		default:
			panic(NewEvalError("unknown continuation", x))
		}
		c := &Cell{v, Nil}
		*p = c
		p = &c.Cdr
	}
	return result.(*Cell)
}

// Continuation of (fn arg1 ... argN)
type ApplyCont struct {
	Fun       Any
	Args      *Cell
	Evaluated *Cell
	Env       *Cell
}

// Continuation of (if cond then else)
type IfCont struct {
	Rest *Cell // (then else)
	Env  *Cell
}

// Continuation of (begin e1 e2 ... eN)
type BeginCont struct {
	Rest *Cell // (e2 ... eN)
	Env  *Cell
}

// Continuation of (set! variable e)
type SetQCont struct {
	Variable *Sym
	Env      *Cell
}

// Continuation of (define variable e)
type DefineCont struct {
	Variable *Sym
	Env      *Cell
}

// A singleton value to represent no need of evaluation
var DoneEnv = &Cell{nil, nil}

//----------------------------------------------------------------------

// Eval evaluates expression in env.
// Eval will panic with an EvalError if it panics.
func Eval(expression Any, env *Cell) Any {
	var k *Cell = Nil // continuation
	defer func() {
		if err := recover(); err != nil {
			ex, ok := err.(*EvalError)
			if !ok {
				ex = &EvalError{fmt.Sprintf("%v", err)}
			}
			ex.Message += fmt.Sprintf(" at %v", expression)
			panic(ex)
		}
	}()
	for {
	INNER_LOOP:
		for {
			switch x := expression.(type) {
			case *Sym:
				expression = GetVar(x, env)
				break INNER_LOOP
			case *Cell:
				xcar, xcdr := x.Car, x.Tail()
				if f, ok := xcar.(*Sym); ok && f.IsKeyword {
					switch f {
					case Quote_: // (quote e)
						expression = xcdr.Car
						break INNER_LOOP
					case If_: // (if cond then [else])
						k = &Cell{&IfCont{xcdr.Tail(), env}, k}
						expression = xcdr.Car // cond
					case Begin_: // (begin e1...)
						k = &Cell{&BeginCont{xcdr.Tail(), env}, k}
						expression = xcdr.Car // e1
					case Lambda_: // (lambda (v...) e...)
						expression = &Expr{xcdr.Car, xcdr.Tail(), env}
						break INNER_LOOP
					case SetQ_: // (set! sym val)
						sym := xcdr.Car.(*Sym)
						k = &Cell{&SetQCont{sym, env}, k}
						expression = xcdr.Tail().Car
					case Define_:
						switch s := xcdr.Car.(type) {
						case *Sym: // (define v e)
							expression = xcdr.Tail().Car
							k = &Cell{&DefineCont{s, env}, k}
						case *Cell: // (define (f param..) e...)
							fsymbol, params := s.Car.(*Sym), s.Cdr
							value := &Expr{params, xcdr.Tail(), env}
							DefineVar(fsymbol, value, env)
							expression = VoidToken
							break INNER_LOOP
						default:
							panic(NewEvalError("not definable", s))
						}
					case Quasiquote_: // (quasiquote e)
						expression = QqExpand(xcdr.Car)
					default:
						fsubr := FSubrs[f]
						expression, env, k = fsubr(xcdr, env, k)
						if env == DoneEnv {
							break INNER_LOOP
						}
					}
				} else {
					k = &Cell{&ApplyCont{nil, xcdr, Nil, env}, k}
					expression = xcar
				}
			default:
				break INNER_LOOP // numbers, strings etc.
			}
		} // end of INNER_LOOP
		for {
			if k == Nil {
				return expression
			}
			// Apply the continuation k to the expression value.
			expression, env, k = ApplyContToExp(k, expression)
			if env != DoneEnv {
				break // continue to the next OUTER LOOP
			}
		}
	}
}

// ApplyContToExp applies the continuation k to value.
// It returns the next expression, its environment and the continuation.
// If the environment is DoneEnv, the expression has been evaluated.
func ApplyContToExp(k *Cell, value Any) (Any, *Cell, *Cell) {
	switch cont := k.Car.(type) {
	case *ApplyCont:
		if cont.Fun == nil {
			cont.Fun = value
		} else {
			cont.Evaluated = &Cell{value, cont.Evaluated}
		}
		if cont.Args == Nil {
			return ApplyFunc(cont.Fun, cont.Evaluated.Reverse(), k.Tail())
		}
		expression := cont.Args.Car
		cont.Args = cont.Args.Tail()
		return expression, cont.Env, k
	case *IfCont: // (if cond then [else])
		b, ok := value.(bool)
		if ok && !b { // If cond is #f...
			tail := cont.Rest.Tail()
			if tail == Nil {
				return VoidToken, DoneEnv, k.Tail()
			} else {
				return tail.Car, cont.Env, k.Tail()
			}
		} else {
			return cont.Rest.Car, cont.Env, k.Tail()
		}
	case *BeginCont: // (begin e1 e2 ... eN)
		if cont.Rest == Nil {
			return value, DoneEnv, k.Tail()
		}
		expression := cont.Rest.Car
		cont.Rest = cont.Rest.Tail()
		return expression, cont.Env, k
	case *SetQCont: // (set! v e)
		if SetVar(cont.Variable, value, cont.Env) {
			return VoidToken, DoneEnv, k.Tail()
		}
		panic(NewEvalError("undefined variable to set", cont.Variable))
	case *DefineCont: // (define v e)
		DefineVar(cont.Variable, value, cont.Env)
		return VoidToken, DoneEnv, k.Tail()
	default:
		panic(NewEvalError("unknown continuation", cont))
	}
}

// ApplyFunc applies fun to arg with the continuation k.
// It returns the next expression, its environment and the continuation.
func ApplyFunc(fun Any, args *Cell, k *Cell) (Any, *Cell, *Cell) {
	// fmt.Printf("\n---%T-%v---%v---%v\n", fun, fun, args, k)
	for {
		switch fn := fun.(type) {
		case *Expr:
			env := PairList(fn.Parameters, args, fn.Environment)
			return &Cell{Begin_, fn.Body}, env, k
		case Subr:
			return fn(args), DoneEnv, k
		case *ApplyType: // (apply fun args)
			fun, args = args.Car, args.Tail().Head()
		case *CallCCType: // (call/cc fun)
			fun, args = args.Car, &Cell{&Cont{NewCont(k)}, Nil}
		case *Cont:
			return args.Car, DoneEnv, NewCont(fn.Continuation)
		case *EvalType: // (eval expression env)
			return args.Car, args.Tail().Head(), k
		default:
			panic(NewEvalError("unknown function", fn))
		}
	}
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
			dotted_pair := &Cell{s.Car.(*Sym), v.Car}
			x := &Cell{dotted_pair, Nil}
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

//----------------------------------------------------------------------

var x_ = NewSym("x")
var thunk_ = NewSym("thunk")
var thunk2_ = NewSym("thunk2")
var key_ = NewSym("key")
var ___ = List

// Intrinsic special-form subroutines
var FSubrs = map[*Sym]FSubr{
	// (and e1 ... eN)
	And_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		if args == Nil { // (and) => #t
			return true, DoneEnv, k
		} else {
			e1, eRest := args.Car, args.Tail()
			if eRest == Nil { // (and e1) => e1
				return e1, env, k
			} else {
				e := ___(Let_, ___(
					___(x_, e1),
					___(thunk_, ___(Lambda_, Nil, &Cell{And_, eRest}))),
					___(If_, x_, ___(thunk_), x_))
				return e, env, k
			}
		}
	},

	// (case key ((d1...) e1...) ((d2...) e2...) ... [(else e...)])
	Case_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		key := args.Car
		binds, conds := expandCaseBody(args.Tail(), 1)
		e := ___(Let_, &Cell{___(key_, key), binds}, &Cell{Cond_, conds})
		return e, env, k
	},

	// (cond (test e1...eN)... (else e...))
	Cond_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		if args == Nil {
			return VoidToken, DoneEnv, k
		}
		clause := args.Head() // (test e1 ... eN)
		test, body := clause.Car, clause.Tail()
		rest := args.Tail()
		if rest == Nil && test == Else_ { // (else e1 ... eN)
			return body.Car, env, &Cell{&BeginCont{body.Tail(), env}, k}
		}
		if body == Nil { // (cond (test) ...)
			e := ___(Or_, test, &Cell{Cond_, rest})
			return e, env, k
		} else if body.Car == Arrow_ { // (cond (test => recipient) ...)
			e := ___(Let_, ___(___(x_, test),
				___(thunk_, ___(Lambda_, Nil, body.Tail().Car)),
				___(thunk2_, ___(Lambda_, Nil, &Cell{Cond_, rest}))),
				___(If_, x_,
					___(___(thunk_), x_),
					___(thunk2_)))
			return e, env, k
		} else { // (cond (test e1...eN) ...)
			thenElse := Nil
			if rest != Nil {
				thenElse = &Cell{&Cell{Cond_, rest}, thenElse}
			}
			thenElse = &Cell{&Cell{Begin_, body}, thenElse}
			k = &Cell{&IfCont{thenElse, env}, k}
			return test, env, k
		}
	},

	// (let ((v e)...) e...)
	Let_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		bindings, body := args.Head(), args.Tail()
		var syms *Cell = Nil
		var vals *Cell = Nil
		for j := bindings; j != Nil; j = j.Tail() {
			ve := j.Head() // (v e)
			syms = &Cell{ve.Car, syms}
			vals = &Cell{ve.Tail().Car, vals}
		}
		expr := &Expr{syms, body, env}
		if vals == Nil {
			k = &Cell{&ApplyCont{nil, Nil, Nil, env}, k}
			return expr, DoneEnv, k
		} else {
			k = &Cell{&ApplyCont{expr, vals.Tail(), Nil, env}, k}
			return vals.Car, env, k
		}
	},

	// (letrec ((v e)...) e...)
	Letrec_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		bindings, body := args.Head(), args.Tail()
		var syms *Cell = Nil
		var voids *Cell = Nil
		for j := bindings; j != Nil; j = j.Tail() {
			ve := j.Head() // (v e)
			syms = &Cell{ve.Car, syms}
			voids = &Cell{VoidToken, voids}
			set := ___(SetQ_, ve.Car, ve.Tail().Car)
			body = &Cell{set, body}
		}
		expr := &Expr{syms, body, env}
		k = &Cell{&ApplyCont{nil, Nil, voids, env}, k}
		return expr, DoneEnv, k
	},

	// (let* ((v e)...) e...)
	LetStar_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		bindings, body := args.Head(), args.Tail()
		if bindings.Cdr == Nil { // (let* ((v e)) e...)
			e := ___(Let_, bindings, body)
			return e, env, k
		} else {
			firstBinding, restBindings := bindings.Head(), bindings.Tail()
			e := ___(Let_,
				___(firstBinding),
				___(LetStar_, restBindings, body))
			return e, env, k
		}
	},

	// (or e1 ... eN)
	Or_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		if args == Nil { // (or) => #f
			return false, DoneEnv, k
		} else {
			e1, eRest := args.Car, args.Tail()
			if eRest == Nil { // (or e1) => e1
				return e1, env, k
			} else {
				e := ___(Let_, ___(
					___(x_, e1),
					___(thunk_, ___(Lambda_, Nil, &Cell{Or_, eRest}))),
					___(If_, x_, x_, ___(thunk_)))
				return e, env, k
			}
		}
	},
}

// ((d1..) e1..) ((d2...) e2..) ... (else e..))
func expandCaseBody(args *Cell, count int) (*Cell, *Cell) {
	if args == Nil {
		return Nil, Nil
	} else {
		clause := args.Head() // ((dN..) eN..) or (else e..)
		test, body := clause.Car, clause.Tail()
		rest := args.Tail()
		if rest == Nil && test == Else_ { // (else e..)
			bind := ___(thunk_, &Cell{Lambda_, &Cell{Nil, body}})
			cond := ___(Else_, ___(thunk_))
			return ___(bind), ___(cond)
		} else { // ((d..) e...)
			thunkN := NewSym(fmt.Sprintf("thunk%d", count))
			bind := ___(thunkN, &Cell{Lambda_, &Cell{Nil, body}})
			cond := ___(___(Memv_, key_, ___(Quote_, test)), ___(thunkN))
			baseBinds, baseConds := expandCaseBody(rest, count+1)
			return &Cell{bind, baseBinds}, &Cell{cond, baseConds}
		}
	}
}

//----------------------------------------------------------------------
// Subrs

func Car_(x *Cell) Any {
	return x.Head().Car
}

func Cdr_(x *Cell) Any {
	return x.Head().Cdr
}

func ConsSubr(x *Cell) Any { // cf. ConsSym
	obj1, obj2 := x.Car, x.Tail().Car
	return &Cell{obj1, obj2}
}

func PairP_(x *Cell) Any {
	a, ok := x.Car.(*Cell)
	return ok && a != nil
}

func Eqv_(x *Cell) Any {
	obj1, obj2 := x.Car, x.Tail().Car
	return obj1 == obj2
}

func Memv_(x *Cell) Any {
	obj, list := x.Car, x.Tail().Head()
	for j := list; j != Nil; j = j.Tail() {
		if j.Car == obj {
			return j
		}
	}
	return false
}

func Assv_(x *Cell) Any {
	obj, alist := x.Car, x.Tail().Head()
	for j := alist; j != Nil; j = j.Tail() {
		a := j.Head()
		if a.Car == obj {
			return a
		}
	}
	return false
}

func NullP_(x *Cell) Any {
	return x.Car == Nil
}

func Not_(x *Cell) Any {
	a, ok := x.Car.(bool)
	return ok && !a
}

func Set_Car_(x *Cell) Any {
	pair, obj := x.Head(), x.Tail().Car
	pair.Car = obj
	return VoidToken
}

func Set_Cdr_(x *Cell) Any {
	pair, obj := x.Head(), x.Tail().Car
	pair.Cdr = obj
	return VoidToken
}

func ListSubr(x *Cell) Any { // cf. List(...Any) and ListSym
	return x
}

func Reverse_(x *Cell) Any {
	return x.Head().Reverse()
}

func Append_(x *Cell) Any {
	car, tail := x.Car, x.Tail()
	if tail == Nil {
		return car
	} else {
		return append2Lists(car.(*Cell), Append_(tail))
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

func Caar_(x *Cell) Any {
	return x.Head().Head().Car
}

func Cdar_(x *Cell) Any {
	return x.Head().Head().Cdr
}

func Cadr_(x *Cell) Any {
	return x.Head().Tail().Car
}

func Cddr_(x *Cell) Any {
	return x.Head().Tail().Cdr
}

func Caddr_(x *Cell) Any {
	return x.Head().Tail().Tail().Car
}

func Cadddr_(x *Cell) Any {
	return x.Head().Tail().Tail().Tail().Car
}

func Length_(x *Cell) Any {
	return x.Head().FoldL(0.0, func(a, b Any) Any {
		return a.(float64) + 1.0
	})
}

func Plus_(x *Cell) Any {
	return x.FoldL(0.0, func(a, b Any) Any {
		return a.(float64) + b.(float64)
	})
}

func Star_(x *Cell) Any {
	return x.FoldL(1.0, func(a, b Any) Any {
		return a.(float64) * b.(float64)
	})
}

func Minus_(x *Cell) Any {
	a1 := x.Car.(float64)
	if x.Cdr == Nil {
		return -a1
	} else {
		return x.Tail().FoldL(a1, func(a, b Any) Any {
			return a.(float64) - b.(float64)
		})
	}
}

func Slash_(x *Cell) Any {
	a1 := x.Car.(float64)
	if x.Cdr == Nil {
		return 1 / a1
	} else {
		return x.Tail().FoldL(a1, func(a, b Any) Any {
			return a.(float64) / b.(float64)
		})
	}
}

func Remainder_(x *Cell) Any {
	return math.Mod(x.Car.(float64), x.Tail().Car.(float64))
}

func Equal_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) == b.(float64)
	})
}

func LessThan_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) < b.(float64)
	})
}

func GreaterThan_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) > b.(float64)
	})
}

func LessThanOrEqual_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) <= b.(float64)
	})
}

func GreaterThanOrEqual_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) >= b.(float64)
	})
}

func Write_(x *Cell) Any {
	fmt.Print(Str2(x.Car, true))
	return VoidToken
}

func Display_(x *Cell) Any {
	fmt.Print(Str2(x.Car, false))
	return VoidToken
}

func Newline_(x *Cell) Any {
	fmt.Println()
	return VoidToken
}

func Read_(x *Cell) Any {
	rr := NewReader(os.Stdin)
	result, err := rr.Read()
	if err != nil {
		panic(err)
	}
	return result
}

// MakeGlobalEnv constructs an environment which contains built-in values.
func MakeGlobalEnv() *Cell {
	gl := &Globals{}
	result := &Cell{gl, Nil}
	__ := NewSym

	builtIns := map[*Sym]Any{
		__("car"):                            Car_,
		__("cdr"):                            Cdr_,
		__("cons"):                           ConsSubr,
		__("pair?"):                          PairP_,
		__("eq?"):                            Eqv_,
		__("eqv?"):                           Eqv_,
		__("memq"):                           Memv_,
		__("memv"):                           Memv_,
		__("assq"):                           Assv_,
		__("assv"):                           Assv_,
		__("null?"):                          NullP_,
		__("not"):                            Not_,
		__("set-car!"):                       Set_Car_,
		__("set-cdr!"):                       Set_Cdr_,
		__("list"):                           ListSubr,
		__("reverse"):                        Reverse_,
		__("append"):                         Append_,
		__("caar"):                           Caar_,
		__("cdar"):                           Cdar_,
		__("cadr"):                           Cadr_,
		__("cddr"):                           Cddr_,
		__("caddr"):                          Caddr_,
		__("cadddr"):                         Cadddr_,
		__("length"):                         Length_,
		__("+"):                              Plus_,
		__("*"):                              Star_,
		__("-"):                              Minus_,
		__("/"):                              Slash_,
		__("remainder"):                      Remainder_,
		__("="):                              Equal_,
		__("<"):                              LessThan_,
		__(">"):                              GreaterThan_,
		__("<="):                             LessThanOrEqual_,
		__(">="):                             GreaterThanOrEqual_,
		__("write"):                          Write_,
		__("display"):                        Display_,
		__("newline"):                        Newline_,
		__("read"):                           Read_,
		__("apply"):                          Apply_,
		__("call/cc"):                        CallCC_,
		__("call-with-current-continuation"): CallCC_,
		__("eval"):                           Eval_,
		__("interaction-environment"): func(x *Cell) Any {
			return result
		},
		__("dump"): func(x *Cell) Any {
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
		},
		__("*version*"): List(Version,
			fmt.Sprintf("%s %s/%s",
				runtime.Version(), runtime.GOOS, runtime.GOARCH),
			"Nukata Scheme"),
	}

	proc, lst1, lsts := __("proc"), __("lst1"), __("lsts")
	cars_cdrs, map1, cars := __("cars_cdrs"), __("map1"), __("cars")
	cdrs, a, b, x := __("cdrs"), __("a"), __("b"), __("x")

	builtIns[__("map")] = &Expr{&Cell{proc, &Cell{lst1, lsts}},
		___(___(___(Lambda_, ___(cars_cdrs, map1),
			___(SetQ_, cars_cdrs,
				___(Lambda_, ___(lsts, a, b),
					___(If_, ___(NullP_, lsts),
						___(ConsSubr, a, b),
						___(cars_cdrs, ___(Cdr_, lsts),
							___(ConsSubr, ___(Caar_, lsts), a),
							___(ConsSubr, ___(Cdar_, lsts), b))))),
			___(SetQ_, map1,
				___(Lambda_, ___(lsts),
					___(If_, ___(NullP_, ___(Car_, lsts)),
						___(Quote_, Nil),
						___(Let_, ___(___(x_, ___(cars_cdrs,
							lsts, ___(Quote_, Nil), ___(Quote_, Nil)))),
							___(Let_, ___(___(cars,
								___(Reverse_, ___(Car_, x))),
								___(cdrs,
									___(Reverse_, ___(Cdr_, x)))),
								___(ConsSubr, ___(Apply_, proc, cars),
									___(map1, cdrs))))))),
			___(map1, ___(ConsSubr, lst1, lsts))),
			VoidToken, VoidToken)),
		result}

	gl.Map = builtIns
	return result
}

//----------------------------------------------------------------------
// Quasi-Quotation

// QqExpand expands x of any quasi-quote `x into the equivalent S-expression.
func QqExpand(x Any) Any {
	return qqExpand0(x, 0) // Begin with the nesting level 0.
}

// QqQuote quotes x so that the result evaluates to x.
func QqQuote(x Any) Any {
	switch x.(type) {
	case *Sym, *Cell:
		return List(Quote_, x)
	default:
		return x
	}
}

func qqExpand0(x Any, level int) Any {
	if j, ok := x.(*Cell); ok {
		if j == Nil {
			return Nil
		}
		if j.Car == Unquote_ { // ,a
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
		return &Cell{Append_, t}
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
			return List(Nil)
		}
		switch j.Car {
		case Unquote_: // ,a
			if level == 0 {
				return j.Tail() // ,a => (a)
			}
			level--
		case Quasiquote_: // `a
			level++
		}
		h := qqExpand2(j.Car, level)
		t := qqExpand1(j.Cdr, level) // != Nil
		if t.Car == Nil && t.Cdr == Nil {
			return List(h)
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
		return List(QqQuote(x))
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
		return List(ConsSym, x.Car, qqConsCons(x.Tail(), y))
	}
}

// qqExpand2 expands x.car (= y) of `x so that the result can be used as an
// argument of append.
// Examples: ,a => (list a); ,@(foo 1 2) => (foo 1 2); b => (list 'b)
func qqExpand2(y Any, level int) Any {
	if j, ok := y.(*Cell); ok {
		if j == Nil {
			return List(ListSym, Nil) // (list nil)
		}
		switch j.Car {
		case Unquote_: // ,a
			if level == 0 {
				return &Cell{ListSym, j.Cdr} // ,a => (list a)
			}
			level--
		case Unquote_splicing_: // ,@a
			if level == 0 {
				return j.Tail().Car // ,@a => a
			}
			level--
		case Quasiquote_: // `a
			level++
		}
	}
	return List(ListSym, qqExpand0(y, level))
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
	return &EvalError{s}
}

func (rr *Reader) parseExpression() Any {
	switch rr.token {
	case LeftParenSym: // (a b c)
		rr.readToken()
		return rr.parseListBody()
	case SingleQuoteSym: // 'a => (quote a)
		rr.readToken()
		return List(Quote_, rr.parseExpression())
	case BackQuoteSym: // `a => (quasiquote a)
		rr.readToken()
		return List(Quasiquote_, rr.parseExpression())
	case CommaSym: // ,a => (unquote a)
		rr.readToken()
		return List(Unquote_, rr.parseExpression())
	case CommaAtSym: // ,@a => (unquote-splicing a)
		rr.readToken()
		return List(Unquote_splicing_, rr.parseExpression())
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
