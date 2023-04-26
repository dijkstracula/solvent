"""
Module to implement expansion for qualifiers.
"""

from typing import List, Callable, Any
from dataclasses import dataclass

from solvent import constraints as constr, syntax as syn


@dataclass
class Qualifier:
    template: Callable[[syn.Expr], syn.Expr]
    required_type: syn.BaseType

    def correct_type(self, typ: syn.BaseType) -> bool:
        return self.required_type == typ


def parse_other(sym: Any, fill: syn.Expr):
    match sym:
        case str():
            return syn.Variable(sym)
        case bool():
            return syn.BoolLiteral(sym)
        case int():
            return syn.IntLiteral(sym)
        case syn.Expr():
            return sym
        case MagicStar():
            return fill
        case MagicV():
            return syn.V()
        case MagicQInner(item=item):
            return item
        case unknown:
            raise NotImplementedError(unknown)


class MagicStar:
    def __lt__(self, other):
        return Qualifier(lambda x: syn.BoolOp(x, "<", parse_other(other, x)), syn.Int())

    def __le__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(x, "<=", parse_other(other, x)), syn.Int()
        )

    def __eq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(x, "==", parse_other(other, x)), syn.Int()
        )

    def __ge__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(x, ">=", parse_other(other, x)), syn.Int()
        )

    def __gt__(self, other):
        return Qualifier(lambda x: syn.BoolOp(x, ">", parse_other(other, x)), syn.Int())

    def __neq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(x, "!=", parse_other(other, x)), syn.Int()
        )


class MagicV:
    def __lt__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), "<", parse_other(other, x)), syn.Int()
        )

    def __le__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), "<=", parse_other(other, x)), syn.Int()
        )

    def __eq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), "==", parse_other(other, x)), syn.Int()
        )

    def __ge__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), ">=", parse_other(other, x)), syn.Int()
        )

    def __gt__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), ">", parse_other(other, x)), syn.Int()
        )

    def __neq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(syn.V(), "!=", parse_other(other, x)), syn.Int()
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

        return MagicQInner(expr)

    def __getattr__(self, attr):
        match attr:
            case str():
                return MagicQInner(syn.Variable(attr))
            case x:
                raise AttributeError(x)


@dataclass
class MagicQInner:
    item: syn.Expr

    def __lt__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, "<", parse_other(other, x)), syn.Int()
        )

    def __le__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, "<=", parse_other(other, x)), syn.Int()
        )

    def __eq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, "==", parse_other(other, x)), syn.Int()
        )

    def __ge__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, ">=", parse_other(other, x)), syn.Int()
        )

    def __gt__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, ">", parse_other(other, x)), syn.Int()
        )

    def __neq__(self, other):
        return Qualifier(
            lambda x: syn.BoolOp(self.item, "!=", parse_other(other, x)), syn.Int()
        )


def predicate(context: constr.Env, quals: List[Qualifier]) -> syn.Conjoin:
    conjuncts = []
    for k, v in context.items:
        match v:
            case syn.RType(base=base):
                for q in quals:
                    if q.correct_type(base):
                        conjuncts += [q.template(syn.Variable(k))]

    return syn.Conjoin(conjuncts)
