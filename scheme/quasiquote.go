package scheme

// Quasi-Quotation

var cosSym = NewSym("cons")
var listSym = NewSym("list")

// QqExpand expands x of any quasi-quote `x into the equivalent S-expression.
func QqExpand(x Any) Any {
	return qqExpand0(x, 0) // Begin with the nesting level 0.
}

// QqQuote quotes x so that the result evaluates to x.
func QqQuote(x Any) Any {
	switch x.(type) {
	case *Sym, *Cell:
		return __(Quote_, x)
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
				if k.Car == listSym || k.Car == cosSym {
					return k
				}
			}
		}
		return &Cell{append_, t}
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
			return __(Nil)
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
			return __(h)
		} else if hc, ok := h.(*Cell); ok {
			if hc.Car == listSym {
				if tcar, ok := t.Car.(*Cell); ok {
					if tcar.Car == listSym {
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
		return __(QqQuote(x))
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
		return __(cosSym, x.Car, qqConsCons(x.Tail(), y))
	}
}

// qqExpand2 expands x.car (= y) of `x so that the result can be used as an
// argument of append.
// Examples: ,a => (list a); ,@(foo 1 2) => (foo 1 2); b => (list 'b)
func qqExpand2(y Any, level int) Any {
	if j, ok := y.(*Cell); ok {
		if j == Nil {
			return __(listSym, Nil) // (list nil)
		}
		switch j.Car {
		case Unquote_: // ,a
			if level == 0 {
				return &Cell{listSym, j.Cdr} // ,a => (list a)
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
	return __(listSym, qqExpand0(y, level))
}
