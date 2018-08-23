package scheme

import (
	"fmt"
	"math"
	"os"
	"runtime"
)

// Subrs

func car_(x *Cell) Any {
	return x.Head().Car
}

func cdr_(x *Cell) Any {
	return x.Head().Cdr
}

func cons_(x *Cell) Any {
	obj1, obj2 := x.Car, x.Tail().Car
	return &Cell{obj1, obj2}
}

func pairP_(x *Cell) Any {
	a, ok := x.Car.(*Cell)
	return ok && a != nil
}

func eqv_(x *Cell) Any {
	obj1, obj2 := x.Car, x.Tail().Car
	return obj1 == obj2
}

func memv_(x *Cell) Any {
	obj, list := x.Car, x.Tail().Head()
	for j := list; j != Nil; j = j.Tail() {
		if j.Car == obj {
			return j
		}
	}
	return false
}

func assv_(x *Cell) Any {
	obj, alist := x.Car, x.Tail().Head()
	for j := alist; j != Nil; j = j.Tail() {
		a := j.Head()
		if a.Car == obj {
			return a
		}
	}
	return false
}

func nullP_(x *Cell) Any {
	return x.Car == Nil
}

func not_(x *Cell) Any {
	a, ok := x.Car.(bool)
	return ok && !a
}

func set_car_(x *Cell) Any {
	pair, obj := x.Head(), x.Tail().Car
	pair.Car = obj
	return VoidToken
}

func set_cdr_(x *Cell) Any {
	pair, obj := x.Head(), x.Tail().Car
	pair.Cdr = obj
	return VoidToken
}

func list_(x *Cell) Any {
	return x
}

func reverse_(x *Cell) Any {
	return x.Head().Reverse()
}

func append_(x *Cell) Any {
	car, tail := x.Car, x.Tail()
	if tail == Nil {
		return car
	} else {
		return append2Lists(car.(*Cell), append_(tail))
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

func caar_(x *Cell) Any {
	return x.Head().Head().Car
}

func cdar_(x *Cell) Any {
	return x.Head().Head().Cdr
}

func cadr_(x *Cell) Any {
	return x.Head().Tail().Car
}

func cddr_(x *Cell) Any {
	return x.Head().Tail().Cdr
}

func caddr_(x *Cell) Any {
	return x.Head().Tail().Tail().Car
}

func cadddr_(x *Cell) Any {
	return x.Head().Tail().Tail().Tail().Car
}

func length_(x *Cell) Any {
	return x.Head().FoldL(0.0, func(a, b Any) Any {
		return a.(float64) + 1.0
	})
}

func plus_(x *Cell) Any {
	return x.FoldL(0.0, func(a, b Any) Any {
		return a.(float64) + b.(float64)
	})
}

func star_(x *Cell) Any {
	return x.FoldL(1.0, func(a, b Any) Any {
		return a.(float64) * b.(float64)
	})
}

func minus_(x *Cell) Any {
	a1 := x.Car.(float64)
	if x.Cdr == Nil {
		return -a1
	} else {
		return x.Tail().FoldL(a1, func(a, b Any) Any {
			return a.(float64) - b.(float64)
		})
	}
}

func slash_(x *Cell) Any {
	a1 := x.Car.(float64)
	if x.Cdr == Nil {
		return 1 / a1
	} else {
		return x.Tail().FoldL(a1, func(a, b Any) Any {
			return a.(float64) / b.(float64)
		})
	}
}

func remainder_(x *Cell) Any {
	return math.Mod(x.Car.(float64), x.Tail().Car.(float64))
}

func equal_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) == b.(float64)
	})
}

func lessThan_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) < b.(float64)
	})
}

func greaterThan_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) > b.(float64)
	})
}

func lessThanOrEqual_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) <= b.(float64)
	})
}

func greaterThanOrEqual_(x *Cell) Any {
	return x.CompareAll(func(a, b Any) bool {
		return a.(float64) >= b.(float64)
	})
}

func write_(x *Cell) Any {
	fmt.Print(Str2(x.Car, true))
	return VoidToken
}

func display_(x *Cell) Any {
	fmt.Print(Str2(x.Car, false))
	return VoidToken
}

func newline_(x *Cell) Any {
	fmt.Println()
	return VoidToken
}

func read_(x *Cell) Any {
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

	var apply_ = &ApplyType{}
	var eval_ = &EvalType{}
	var callcc_ = &CallCCType{}

	builtIns := map[*Sym]Any{
		NewSym("car"):                            car_,
		NewSym("cdr"):                            cdr_,
		NewSym("cons"):                           cons_,
		NewSym("pair?"):                          pairP_,
		NewSym("eq?"):                            eqv_,
		NewSym("eqv?"):                           eqv_,
		NewSym("memq"):                           memv_,
		NewSym("memv"):                           memv_,
		NewSym("assq"):                           assv_,
		NewSym("assv"):                           assv_,
		NewSym("null?"):                          nullP_,
		NewSym("not"):                            not_,
		NewSym("set-car!"):                       set_car_,
		NewSym("set-cdr!"):                       set_cdr_,
		NewSym("list"):                           list_,
		NewSym("reverse"):                        reverse_,
		NewSym("append"):                         append_,
		NewSym("caar"):                           caar_,
		NewSym("cdar"):                           cdar_,
		NewSym("cadr"):                           cadr_,
		NewSym("cddr"):                           cddr_,
		NewSym("caddr"):                          caddr_,
		NewSym("cadddr"):                         cadddr_,
		NewSym("length"):                         length_,
		NewSym("+"):                              plus_,
		NewSym("*"):                              star_,
		NewSym("-"):                              minus_,
		NewSym("/"):                              slash_,
		NewSym("remainder"):                      remainder_,
		NewSym("="):                              equal_,
		NewSym("<"):                              lessThan_,
		NewSym(">"):                              greaterThan_,
		NewSym("<="):                             lessThanOrEqual_,
		NewSym(">="):                             greaterThanOrEqual_,
		NewSym("write"):                          write_,
		NewSym("display"):                        display_,
		NewSym("newline"):                        newline_,
		NewSym("read"):                           read_,
		NewSym("apply"):                          apply_,
		NewSym("call/cc"):                        callcc_,
		NewSym("call-with-current-continuation"): callcc_,
		NewSym("eval"):                           eval_,
		NewSym("interaction-environment"): func(x *Cell) Any {
			return result
		},
		NewSym("dump"): func(x *Cell) Any {
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
		NewSym("*version*"): __(Version,
			fmt.Sprintf("%s %s/%s",
				runtime.Version(), runtime.GOOS, runtime.GOARCH),
			"Nukata Scheme"),
	}

	proc, lst1, lsts := NewSym("proc"), NewSym("lst1"), NewSym("lsts")
	cars_cdrs, map1 := NewSym("cars_cdrs"), NewSym("map1")
	cars, cdrs := NewSym("cars"), NewSym("cdrs")
	a, b, x := NewSym("a"), NewSym("b"), NewSym("x")

	builtIns[NewSym("map")] = &Expr{&Cell{proc, &Cell{lst1, lsts}},
		__(__(__(Lambda_, __(cars_cdrs, map1),
			__(SetQ_, cars_cdrs,
				__(Lambda_, __(lsts, a, b),
					__(If_, __(nullP_, lsts),
						__(cons_, a, b),
						__(cars_cdrs, __(cdr_, lsts),
							__(cons_, __(caar_, lsts), a),
							__(cons_, __(cdar_, lsts), b))))),
			__(SetQ_, map1,
				__(Lambda_, __(lsts),
					__(If_, __(nullP_, __(car_, lsts)),
						__(Quote_, Nil),
						__(Let_, __(__(x_, __(cars_cdrs,
							lsts, __(Quote_, Nil), __(Quote_, Nil)))),
							__(Let_, __(__(cars,
								__(reverse_, __(car_, x))),
								__(cdrs,
									__(reverse_, __(cdr_, x)))),
								__(cons_, __(apply_, proc, cars),
									__(map1, cdrs))))))),
			__(map1, __(cons_, lst1, lsts))),
			VoidToken, VoidToken)),
		result}

	builtIns[NewSym("force")] = &Expr{__(x), __(__(x)), result}

	gl.Map = builtIns
	return result
}
