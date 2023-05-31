"""
Translate types into SMT expressions.
"""

from functools import reduce
from typing import List

import z3

from solvent import syntax as syn


def from_exprs(items: List[syn.Expr], val_name: str = ".v"):
    return reduce(
        lambda x, y: z3.And(x, y), [from_expr(i, val_name) for i in items], True
    )


def from_expr(e: syn.Expr, val_name: str = ".v"):
    match e:
        case syn.Variable(name=n):
            # TODO, look up type
            return z3.Int(n)
        case syn.V():
            # TODO, look up type
            return z3.Int(val_name)
        case syn.Call(function_name=syn.Variable(name=name), arglist=args):
            fn = z3.Function(name, *[z3.IntSort() for _ in args], z3.IntSort())
            call = fn(*[from_expr(a, val_name) for a in args])
            return call
        case syn.ArithBinOp(lhs=l, op="+", rhs=r):
            return from_expr(l, val_name) + from_expr(r, val_name)
        case syn.ArithBinOp(lhs=l, op="-", rhs=r):
            return from_expr(l, val_name) - from_expr(r, val_name)
        case syn.ArithBinOp(lhs=l, op="*", rhs=r):
            return from_expr(l, val_name) * from_expr(r, val_name)
        case syn.ArithBinOp(lhs=l, op="//", rhs=r):
            return from_expr(l, val_name) / from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return from_expr(l, val_name) > from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op="==", rhs=r):
            return from_expr(l, val_name) == from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op="<=", rhs=r):
            return from_expr(l, val_name) <= from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op="<", rhs=r):
            return from_expr(l, val_name) < from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op=">", rhs=r):
            return from_expr(l, val_name) > from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op=">=", rhs=r):
            return from_expr(l, val_name) >= from_expr(r, val_name)
        case syn.BoolOp(lhs=l, op="and", rhs=r):
            return z3.And(from_expr(l, val_name), from_expr(r, val_name))
        case syn.BoolOp(lhs=l, op="or", rhs=r):
            return z3.Or(from_expr(l, val_name), from_expr(r, val_name))
        case syn.BoolOp(lhs=l, op="==>", rhs=r):
            return z3.Implies(from_expr(l, val_name), from_expr(r, val_name))
        case syn.BoolLiteral(value=v):
            return v
        case syn.IntLiteral(value=v):
            return v
        case syn.Neg(expr=e):
            return -from_expr(e, val_name)
        case syn.TypeVar(name=n):
            # will need to infer this type eventually.
            # when that happens, this becomes an error
            raise Exception(f"Can't convert TypeVar, {n}, to smt.")
        case x:
            raise NotImplementedError(x, repr(x))


def base_type(b: syn.Type):
    match b:
        case syn.RType(base=syn.Int()):
            return z3.IntSort()
        case syn.RType(base=syn.Bool()):
            return z3.BoolSort()
        case x:
            raise NotImplementedError(x)


def from_type(name: str, t: syn.Type):
    match t:
        case syn.RType(predicate=syn.Conjoin(conj)):
            return from_exprs(conj, name)
        case syn.ArrowType(args=_, ret=_):
            return True
        case x:
            raise NotImplementedError(name, type(x))
