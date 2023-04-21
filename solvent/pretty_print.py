
from solvent import syn
import pprint


def pretty_print(stmt: syn.Stmt):
    pp = pprint.PrettyPrinter(indent=2)
    pp.pprint(stmt)


def pstring_expr(expr: syn.Expr):
    match expr:
        case syn.Variable(name=x): return f"{x}"
        case syn.IntLiteral(value=v): return f"{v}"
        case syn.BoolLiteral(value=v): return f"{v}"
        case syn.BoolOp(lhs=l, op=op, rhs=r):
            return f"{pstring_expr(l)} {op} {pstring_expr(r)}"


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
        case x:
            print(x)
            raise NotImplementedError


def pstring_base_type(typ: syn.BaseType):
    match typ:
        case syn.Int(): return "int"
        case syn.Bool(): return "bool"
        case syn.Unit(): return "unit"
        case syn.TypeVar(name=name): return f"'{name}"
