"""
Translate types into SMT expressions.
"""

from solvent import syn

import z3
from functools import reduce

def expr_to_smt(e: syn.Expr):
    match e:
        case syn.Variable(name=n):
            # TODO, look up type
            return z3.Int(n)
        case syn.V():
            # TODO, look up type
            return z3.Int(".v")
        case syn.Call(function_name=syn.Variable(name=name), arglist=args):
            print(f"NBT: {args}")
            fn = z3.Function(name, *[z3.IntSort() for _ in args], z3.IntSort())
            call = fn(*[expr_to_smt(a) for a in args])
            print(f"NBT: {call}")
            return call
        case syn.ArithBinOp(lhs=l, op="+", rhs=r):
            return expr_to_smt(l) + expr_to_smt(r)
        case syn.ArithBinOp(lhs=l, op="-", rhs=r):
            return expr_to_smt(l) - expr_to_smt(r)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return expr_to_smt(l) > expr_to_smt(r)
        case syn.BoolOp(lhs=l, op="==", rhs=r):
            return expr_to_smt(l) == expr_to_smt(r)
        case syn.BoolOp(lhs=l, op="<=", rhs=r):
            return expr_to_smt(l) <= expr_to_smt(r)
        case syn.BoolOp(lhs=l, op="<", rhs=r):
            return expr_to_smt(l) < expr_to_smt(r)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return expr_to_smt(l) > expr_to_smt(r)
        case syn.BoolOp(lhs=l, op=">=", rhs=r):
            return expr_to_smt(l) >= expr_to_smt(r)
        case syn.BoolOp(lhs=l, op="and", rhs=r):
            return z3.And(expr_to_smt(l), expr_to_smt(r))
        case syn.BoolLiteral(value=v):
            return v
        case syn.IntLiteral(value=v):
            return v
        case syn.Neg(expr=e):
            return z3.Not(expr_to_smt(e))
        case syn.TypeVar(name=n):
            # will need to infer this type eventually.
            # when that happens, this becomes an error
            raise Exception(f"Can't convert TypeVar, {n}, to smt.")
        case [*items]:
            return reduce(
                lambda x, y: z3.And(x, y),
                [expr_to_smt(i) for i in items],
                True
            )
        case x:
            print(x)
            raise NotImplementedError
