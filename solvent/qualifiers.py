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


@dataclass
class Qualifier:
    template: syn.Expr
    required_type: syn.BaseType

    def correct_type(self, typ: syn.BaseType) -> bool:
        return self.required_type == typ

    def __eq__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.BoolOp(self.template, "==", parse_other(other)),
            syn.Int(),
        )

    def __add__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.ArithBinOp(self.template, "+", parse_other(other)),
            syn.Int(),
        )

    def __floordiv__(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.ArithBinOp(self.template, "//", parse_other(other)),
            syn.Int(),
        )

    def implies(self, other: object) -> "Qualifier":
        return Qualifier(
            syn.BoolOp(self.template, "==>", parse_other(other)),
            syn.Int(),
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
                syn.ArithBinOp(self.symbol, op, parse_other(other)), syn.Int()
            )
        else:
            return Qualifier(syn.BoolOp(self.symbol, op, parse_other(other)), syn.Int())

    def bool_op(self, op: str, other: object) -> "Qualifier":
        return Qualifier(syn.BoolOp(self.symbol, op, parse_other(other)), syn.Bool())

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
            if isinstance(v, syn.RType) and q.correct_type(v.base):
                conjuncts += [SubstStar(k).visit_expr(q.template)]

    return syn.Conjoin(conjuncts)
