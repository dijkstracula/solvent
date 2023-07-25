"""
Translate types into SMT expressions.
"""

from functools import reduce
from logging import debug
from typing import Any, Callable, Dict, List

import z3

from solvent import env
from solvent import syntax as syn
from solvent.annotate import lookup_path, resolve_class


class ToSmt:
    def __init__(self, context: env.ScopedEnv, types: Dict[int, syn.Type]):
        self.context = context
        # TODO: remove types
        self.types = types

    def from_exprs(self, items: List[syn.Expr], val_name: str = ".v"):
        ret_smt = True
        asms = []
        for i in items:
            ismt, iasms = self.from_expr(i, val_name)
            ret_smt = z3.And(ret_smt, ismt)
            asms += iasms

        return z3.And(reduce(lambda x, y: z3.And(x, y), asms, True), ret_smt)

    def from_expr(self, e: syn.Expr, val_name: str = ".v") -> tuple[Any, List[Any]]:
        match e:
            case syn.Variable(name=n):
                # TODO, look up type
                return (z3.Int(n), [])
            case syn.V():
                # TODO, look up type
                return (z3.Int(val_name), [])
            case syn.Call(
                function_name=syn.GetAttr(name=syn.Variable(var), attr=attr),
                arglist=args,
            ):
                obj_typ = self.context[var]
                debug("huzzah", obj_typ)
                name = f"{var}_{attr}"
                asms = []
                if isinstance(obj_typ, syn.ObjectType):
                    # TODO: have a factored out way of resolving
                    # class names and looking up members
                    cls = resolve_class(obj_typ, self.context)
                    typ = lookup_path(attr.split("."), cls).resolve_name(
                        self.context[var].name
                    )
                    new_typ = typ
                    assert isinstance(typ, syn.ArrowType)
                    for (tyv, kind), arg in zip(
                        typ.type_abs.items(), obj_typ.generic_args
                    ):
                        if kind == "pred" and isinstance(arg, syn.RType):
                            debug(tyv, arg)
                            new_typ = new_typ.subst_typevar(tyv, arg.predicate)

                    assert isinstance(new_typ, syn.ArrowType)
                    debug(new_typ.ret)
                    asms += [self.from_type(name, new_typ.ret)]

                fn = z3.Function(
                    name,
                    *[z3.IntSort() for _ in args],
                    z3.IntSort(),
                )
                call = fn(*[self.from_expr(a, val_name) for a in args])
                return (call, asms)
            case syn.Call(function_name=name, arglist=args):
                fn = z3.Function(
                    str(name).replace(".", "_"),
                    *[z3.IntSort() for _ in args],
                    z3.IntSort(),
                )
                call = fn(*[self.from_expr(a, val_name) for a in args])
                return (call, [])
            case syn.ArithBinOp(lhs=l, op=op, rhs=r) | syn.BoolOp(lhs=l, op=op, rhs=r):
                lsmt, lasms = self.from_expr(l, val_name)
                rsmt, rasms = self.from_expr(r, val_name)
                return (lookup_op(op)(lsmt, rsmt), lasms + rasms)
            case syn.BoolLiteral(value=v):
                return (v, [])
            case syn.IntLiteral(value=v):
                return (v, [])
            case syn.Neg(expr=e):
                esmt, easms = self.from_expr(e, val_name)
                return (-esmt, easms)
            case syn.Not(expr=e):
                esmt, easms = self.from_expr(e, val_name)
                return (z3.Not(esmt), easms)
            case syn.TypeVar(name=n):
                # will need to infer this type eventually.
                # when that happens, this becomes an error
                raise Exception(f"Can't convert TypeVar, {n}, to smt.")
            case x:
                raise NotImplementedError(str(x), repr(x))

    def from_type(self, name: str, t: syn.Type):
        match t:
            case syn.RType(predicate=syn.Conjoin(conj)):
                return self.from_exprs(conj, name)
            case syn.ArrowType() | syn.ListType() | syn.ObjectType() | syn.DictType():
                return True
            case x:
                raise NotImplementedError(name, type(x))


def lookup_op(op: str) -> Callable[[Any, Any], Any]:
    match op:
        case "+":
            return lambda x, y: x + y
        case "-":
            return lambda x, y: x - y
        case "*":
            return lambda x, y: x * y
        case "//":
            return lambda x, y: x // y
        case "/":
            return lambda x, y: x / y
        case ">":
            return lambda x, y: x > y
        case "==":
            return lambda x, y: x == y
        case ">=":
            return lambda x, y: x >= y
        case "<":
            return lambda x, y: x < y
        case "<=":
            return lambda x, y: x <= y
        case "and":
            return lambda x, y: z3.And(x, y)
        case "or":
            return lambda x, y: z3.Or(x, y)
        case "==>":
            return lambda x, y: z3.Implies(x, y)
        case x:
            raise NotImplementedError(x)


def base_type(b: syn.Type):
    match b:
        case syn.RType(base=syn.Int()):
            return z3.IntSort()
        case syn.RType(base=syn.Bool()):
            return z3.BoolSort()
        case x:
            raise NotImplementedError(x)
