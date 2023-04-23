"""
Translate types into SMT expressions.
"""

from solvent import syn

import z3

def expr_to_smt(e: syn.Expr):
    match e:
        case syn.Variable(name=n):
            # TODO, look up type
            return z3.Int(n)
        case syn.V():
            # TODO, look up type
            return z3.Int(".v")
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
        case syn.Neg(expr=e):
            return z3.Not(expr_to_smt(e))
        case syn.TypeVar(name=n):
            # will need to infer this type eventually.
            # when that happens, this becomes an error
            return True
        case x:
            print(x)
            raise NotImplementedError
