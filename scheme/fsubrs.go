package scheme

import "fmt"

var x_ = NewSym("x")
var thunk_ = NewSym("thunk")
var thunk2_ = NewSym("thunk2")
var key_ = NewSym("key")

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
				e := __(Let_, __(
					__(x_, e1),
					__(thunk_, __(Lambda_, Nil, &Cell{And_, eRest}))),
					__(If_, x_, __(thunk_), x_))
				return e, env, k
			}
		}
	},

	// (case key ((d1...) e1...) ((d2...) e2...) ... [(else e...)])
	Case_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		key := args.Car
		binds, conds := expandCaseBody(args.Tail(), 1)
		e := __(Let_, &Cell{__(key_, key), binds}, &Cell{Cond_, conds})
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
			e := __(Or_, test, &Cell{Cond_, rest})
			return e, env, k
		} else if body.Car == Arrow_ { // (cond (test => recipient) ...)
			e := __(Let_, __(__(x_, test),
				__(thunk_, __(Lambda_, Nil, body.Tail().Car)),
				__(thunk2_, __(Lambda_, Nil, &Cell{Cond_, rest}))),
				__(If_, x_,
					__(__(thunk_), x_),
					__(thunk2_)))
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

	// (delay e)
	Delay_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		k = &Cell{&ApplyCont{nil, Nil, __(&Expr{Nil, args, env}), env}, k}
		return makePromise, env, k
	},

	// (do ((var init [step])...) (test e...) e...)
	Do_: func(args, env, k *Cell) (Any, *Cell, *Cell) {
		bindings, restdo := args.Head(), args.Tail()
		var vars *Cell = Nil
		var inits *Cell = Nil
		var steps *Cell = Nil
		for j := bindings; j != Nil; j = j.Tail() {
			vis := j.Head() // (var init [step])
			v := vis.Car
			i := vis.Tail().Car
			r := vis.Tail().Tail()
			if r == Nil {
				steps = &Cell{v, steps}
			} else {
				steps = &Cell{r.Car, steps}
			}
			inits = &Cell{i, inits}
			vars = &Cell{v, vars}
		}
		exits, commands := restdo.Head(), restdo.Tail()
		test := exits.Car
		exitsBody := exits.Tail()
		loop := &Expr{vars, Nil, env}
		body := __(__(If_, test, &Cell{Begin_, exitsBody},
			__(Begin_, &Cell{Begin_, commands}, &Cell{loop, steps})))
		loop.Body = body // make a loop.
		k = &Cell{&ApplyCont{nil, inits, Nil, env}, k}
		return loop, DoneEnv, k
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
			set := __(SetQ_, ve.Car, ve.Tail().Car)
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
			e := __(Let_, bindings, body)
			return e, env, k
		} else {
			firstBinding, restBindings := bindings.Head(), bindings.Tail()
			e := __(Let_,
				__(firstBinding),
				__(LetStar_, restBindings, body))
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
				e := __(Let_, __(
					__(x_, e1),
					__(thunk_, __(Lambda_, Nil, &Cell{Or_, eRest}))),
					__(If_, x_, x_, __(thunk_)))
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
			bind := __(thunk_, &Cell{Lambda_, &Cell{Nil, body}})
			cond := __(Else_, __(thunk_))
			return __(bind), __(cond)
		} else { // ((d..) e...)
			thunkN := NewSym(fmt.Sprintf("thunk%d", count))
			bind := __(thunkN, &Cell{Lambda_, &Cell{Nil, body}})
			cond := __(__(memv_, key_, __(Quote_, test)), __(thunkN))
			baseBinds, baseConds := expandCaseBody(rest, count+1)
			return &Cell{bind, baseBinds}, &Cell{cond, baseConds}
		}
	}
}

var proc_ = NewSym("proc")
var result_ready_ = NewSym("result-ready?")
var result_ = NewSym("result")

var makePromise = __(Lambda_, __(proc_),
	__(Let_, __(
		__(result_ready_, false),
		__(result_, false)),
		__(Lambda_, Nil,
			__(If_, result_ready_, result_,
				__(Let_, __(__(x_, __(proc_))),
					__(If_, result_ready_, result_,
						__(Begin_,
							__(SetQ_, result_ready_, true),
							__(SetQ_, result_, x_),
							result_)))))))
