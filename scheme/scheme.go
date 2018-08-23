/*
  Scheme in [Go 1.11] by SUZUKI Hisao (H30.8/5 - H30.8/23).

  The Reader type and other portions are derived from
  Nukata Lisp in Go (https://github.com/nukata/lisp-in-go).
*/
package scheme

import (
	"errors"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
	"sync"
)

const Version = 0.50

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

func __(j ...Any) *Cell {
	var result Any = Nil
	p := &result
	for _, v := range j {
		x := &Cell{v, Nil}
		*p = x
		p = &x.Cdr
	}
	return result.(*Cell)
}

// List(e1, ..., eN Any) builds a list (e1 ... eN) as *Cell.
var List = __

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

// Expression keywords

var And_ = NewSym2("and", true)
var Arrow_ = NewSym2("=>", true)
var Begin_ = NewSym2("begin", true)
var Case_ = NewSym2("case", true)
var Cond_ = NewSym2("cond", true)
var Define_ = NewSym2("define", true)
var Delay_ = NewSym2("delay", true)
var Do_ = NewSym2("do", true)
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
			dottedPair := &Cell{s.Car.(*Sym), v.Car}
			x := &Cell{dottedPair, Nil}
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
