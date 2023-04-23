from solvent import syn
from solvent.check import Constraint, Eq, SubType


def pstring_expr(expr: syn.Expr):
    match expr:
        case syn.Variable(name=x): return f"{x}"
        case syn.IntLiteral(value=v): return f"{v}"
        case syn.BoolLiteral(value=v): return f"{v}"
        case syn.BoolOp(lhs=l, op=op, rhs=r):
            return f"{pstring_expr(l)} {op} {pstring_expr(r)}"
        case syn.V():
            return "V"
        case syn.Call(function_name=x, arglist=args):
            fn = pstring_expr(x)
            args = [pstring_expr(a) for a in args]
            return f"{fn}({', '.join(args)})"
        case x:
            return f"`{x}`"


def pstring_type(typ: syn.Type):
    match typ:
        case syn.RType(value=value, predicate=syn.BoolLiteral(value=True)):
            return f"{pstring_base_type(value)}"
        case syn.RType(value=value, predicate=pred):
            return (f"{{ {pstring_base_type(value)} | {pstring_expr(pred)} }}")
        case syn.ArrowType(args=args, ret=ret):
            return "({}) -> {}".format(
                ", ".join(map(pstring_type, args)),
                pstring_type(ret)
            )
        case syn.TypeVar(name=n):
            print(n)
            raise Exception("A TypeVar is not a base type")
        case x:
            print(x)
            raise NotImplementedError


def pstring_base_type(typ: syn.BaseType):
    match typ:
        case syn.Int(): return "int"
        case syn.Bool(): return "bool"
        case syn.Unit(): return "unit"
        case syn.TypeVar(name=n): return f"'{n}"
        case x:
            print(x)
            raise NotImplementedError


def pstring_cvar(c: Constraint):
    match c:
        case Eq(lhs=lhs, rhs=rhs):
            return f"{pstring_type(lhs)} = {pstring_type(rhs)}"
        case SubType(lhs=lhs, rhs=rhs):
            return f"{pstring_type(lhs)} <: {pstring_type(rhs)}"
