"""
Translate types into SMT expressions.
"""

from solvent import syntax as syn

import z3
from functools import reduce
from typing import List


def from_exprs(items: List[syn.Expr]):
    return reduce(lambda x, y: z3.And(x, y), [from_expr(i) for i in items], True)


def from_expr(e: syn.Expr):
    match e:
        case syn.Variable(name=n):
            # TODO, look up type
            return z3.Int(n)
        case syn.V():
            # TODO, look up type
            return z3.Int(".v")
        case syn.Call(function_name=syn.Variable(name=name), arglist=args):
            fn = z3.Function(name, *[z3.IntSort() for _ in args], z3.IntSort())
            call = fn(*[from_expr(a) for a in args])
            return call
        case syn.ArithBinOp(lhs=l, op="+", rhs=r):
            return from_expr(l) + from_expr(r)
        case syn.ArithBinOp(lhs=l, op="-", rhs=r):
            return from_expr(l) - from_expr(r)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return from_expr(l) > from_expr(r)
        case syn.BoolOp(lhs=l, op="==", rhs=r):
            return from_expr(l) == from_expr(r)
        case syn.BoolOp(lhs=l, op="<=", rhs=r):
            return from_expr(l) <= from_expr(r)
        case syn.BoolOp(lhs=l, op="<", rhs=r):
            return from_expr(l) < from_expr(r)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return from_expr(l) > from_expr(r)
        case syn.BoolOp(lhs=l, op=">=", rhs=r):
            return from_expr(l) >= from_expr(r)
        case syn.BoolOp(lhs=l, op="and", rhs=r):
            return z3.And(from_expr(l), from_expr(r))
        case syn.BoolLiteral(value=v):
            return v
        case syn.IntLiteral(value=v):
            return v
        case syn.Neg(expr=e):
            return z3.Not(from_expr(e))
        case syn.TypeVar(name=n):
            # will need to infer this type eventually.
            # when that happens, this becomes an error
            raise Exception(f"Can't convert TypeVar, {n}, to smt.")
        # case [*items]:
        case x:
            print(x)
            raise NotImplementedError
