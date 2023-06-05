"""
Module to implement expansion for qualifiers.
"""

from dataclasses import dataclass
from typing import List

from solvent import env
from solvent import syntax as syn
from solvent.syntax import Expr, Star
from solvent.visitor import Visitor


def parse_other(sym: object):
    match sym:
        case bool():
            return syn.BoolLiteral(sym)
        case int():
            return syn.IntLiteral(sym)
        case syn.Expr():
            return sym
        case Magic(expr):
            return expr
        case Qualifier(template=temp):
            return temp
        case unknown:
            raise NotImplementedError(unknown)


class SubstStar(Visitor):
    def start(self, variable):
        self.variable = variable

    def start_Star(self, star: Star) -> Expr | None:
        super().start_Star(star)

        return syn.Variable(self.variable)


class HasStar(Visitor):
    def start(self):
        self.has_star = False

    def start_Star(self, star: Star) -> Expr | None:
        self.has_star = True
        return super().start_Star(star)


def type_eq(t0: syn.Type, t1: syn.Type) -> bool:
    match (t0, t1):
        case syn.ListType(inner_typ=t0), syn.ListType(inner_typ=t1):
            return type_eq(t0, t1)
        case syn.Bottom(), _:
            return True
        case _, syn.Bottom():
            return True
        case syn.ArrowType(args=args0, ret=ret0), syn.ArrowType(args=args1, ret=ret1):
            return all(
                [type_eq(a0, a1) for (_, a0), (_, a1) in zip(args0, args1)]
            ) and type_eq(ret0, ret1)
        case t0, t1:
            return t0 == t1


@dataclass
class Qualifier:
    template: syn.Expr
    required_type: syn.Type

    def correct_type(self, typ: syn.Type) -> bool:
        return type_eq(self.required_type, typ)

    def __eq__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.BoolOp(self.template, "==", parse_other(other)), syn.RType.int()
        )

    def __add__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.ArithBinOp(self.template, "+", parse_other(other)),
            syn.RType.int(),
        )

    def __floordiv__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.ArithBinOp(self.template, "//", parse_other(other)),
            syn.RType.int(),
        )

    def implies(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.BoolOp(self.template, "==>", parse_other(other)),
            syn.RType.int(),
        )

    def subst(self, name: str) -> syn.Expr:
        return SubstStar(name).visit_expr(self.template)

    def requires_expr(self) -> bool:
        v = HasStar()
        v.visit_expr(self.template)
        return v.has_star


@dataclass
class Magic:
    symbol: syn.Expr

    def int_op(self, op: str, other: object) -> "Qualifier":
        if op in ["*", "+"]:
            return Qualifier(
                syn.ArithBinOp(self.symbol, op, parse_other(other)), syn.RType.int()
            )
        else:
            return Qualifier(
                syn.BoolOp(self.symbol, op, parse_other(other)), syn.RType.int()
            )

    def bool_op(self, op: str, other: object) -> "Qualifier":
        return Qualifier(
            syn.BoolOp(self.symbol, op, parse_other(other)), syn.RType.bool()
        )

    def __lt__(self, other):
        return self.int_op("<", other)

    def __le__(self, other):
        return self.int_op("<=", other)

    def __eq__(self, other):
        return self.int_op("==", other)

    def __ge__(self, other):
        return self.int_op(">=", other)

    def __gt__(self, other):
        return self.int_op(">", other)

    def __neq__(self, other):
        return self.int_op("!=", other)

    def __add__(self, other):
        return self.int_op("+", other)

    def __mul__(self, other):
        return self.int_op("*", other)

    def len(self):
        return Qualifier(
            syn.Call(syn.Variable("len"), [self.symbol]),
            syn.ListType(inner_typ=syn.Bottom()),
        )


class MagicQ:
    def __getitem__(self, key):
        match key:
            case bool():
                expr = syn.BoolLiteral(key)
            case int():
                expr = syn.IntLiteral(key)
            case str():
                expr = syn.Variable(key)
            case x:
                raise NotImplementedError(x)

        return Magic(expr)

    def __getattr__(self, attr):
        match attr:
            case str():
                return Magic(syn.Variable(attr))
            case x:
                raise AttributeError(x)


def predicate(context: env.ScopedEnv, quals: List[Qualifier]) -> syn.Conjoin:
    conjuncts = []
    for q in quals:
        if not q.requires_expr():
            conjuncts += [q.template]
            continue

        for k, v in context.items():
            if q.correct_type(v):
                conjuncts += [SubstStar(k).visit_expr(q.template)]

    return syn.Conjoin(conjuncts)
