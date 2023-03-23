from . import types
from .. import errors

from .types import _PT, EvalT
from .types import LiquidType, Bool, Int

from dataclasses import dataclass
from typing import Generic, Type, Union


class LiquidExpr(Generic[_PT]):
    t: LiquidType[_PT]

    def __init__(self, tp: Union[Type[_PT], LiquidType[_PT]]):
        if isinstance(tp, LiquidType):
            self.t = tp
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.fromPyType(tp)

    def to_vc(self):
        raise Exception(f"Missing to_vc() implementation for {type(self)}")

    ## AST creation methods

    def lt(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Lt":
        return Lt(self, other)

    def le(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Le":
        return Le(self, other)

    def gt(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Gt":
        return Gt(self, other)

    def ge(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Ge":
        return Ge(self, other)

    def add(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Add":
        return Add(self, other)

    def sub(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Sub":
        return Sub(self, other)

    def mul(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Mul":
        return Mul(self, other)

    def div(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Div":
        return Div(self, other)

    def mod(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Mod":
        return Mod(self, other)

    def band(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "And":
        return And(self, other)

    def bor(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "Or":
        return Or(self, other)

    def len(self: "LiquidExpr[list]"):
        return ArrayLen(self)


@dataclass
class LiquidVar(LiquidExpr[_PT]):
    """ A binding of a name to a type.  the `ident` metavariable name should
    match the name of the local Python variable for consistency."""
    ident: str

    def __init__(self, ident: str, t: Union[Type[_PT], LiquidType[_PT]]):
        # XXX: PyRight complains about:
        # "Argument of type "Type[_PT@LiquidVar] | LiquidType[_PT@LiquidVar]" cannot be assigned to parameter
        #   "tp" of type "Type[_PT@LiquidVar] | LiquidType[_PT@LiquidVar]"
        # if I try to call the superclass' constructor, so it's inlined here.
        if isinstance(t, LiquidType):
            self.t = t
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.fromPyType(t)
        self.ident = ident

    def eq(self, other: _PT | LiquidExpr[_PT]) -> "Eq":
        return Eq(self, other)


# Expressions

@dataclass
class UnaryOp(Generic[_PT, EvalT], LiquidExpr[EvalT]):
    """ A uniary operation on a liquid variable. """
    target: LiquidExpr[_PT]


class BinOp(Generic[_PT, EvalT], LiquidExpr[EvalT]):
    """ A binary operation on a liquid variable and a concrete Python one."""
    lhs: LiquidExpr[_PT]
    rhs: _PT | LiquidExpr[_PT]

    def __init__(self, t: LiquidType[EvalT], lhs: LiquidExpr[_PT], rhs: _PT | LiquidExpr[_PT]):
        super().__init__(t)
        if isinstance(rhs, LiquidExpr):
            if lhs.t.python_type != rhs.t.python_type:
                raise errors.BinopTypeMismatch(lhs, self, rhs)
        else:
            if lhs.t.python_type != type(rhs):
                raise errors.BinopTypeMismatch(lhs, self, rhs)

        self.lhs = lhs
        self.rhs = rhs


@dataclass
class Eq(BinOp[_PT, bool]):
    def __init__(self, lhs: LiquidExpr[_PT], rhs: Union[_PT, LiquidExpr[_PT]]):
        super().__init__(Bool(), lhs, rhs)


### Numeric comparisons

class NumericBinOp(BinOp[int, EvalT]):
    def __init__(self, t: LiquidType[EvalT], lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        if lhs.t.python_type != int:
            raise errors.BinopTypeMismatch(self, self, rhs)
        super().__init__(t, lhs, rhs)


@dataclass
class Le(NumericBinOp[bool]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Lt(NumericBinOp[bool]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Ge(NumericBinOp[bool]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Gt(NumericBinOp[bool]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Bool(), lhs, rhs)


### Numeric operations

@dataclass
class Add(NumericBinOp[int]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Sub(NumericBinOp[int]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Mul(NumericBinOp[int]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Div(NumericBinOp[int]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Mod(NumericBinOp[int]):
    def __init__(self, lhs: LiquidExpr[int], rhs: Union[int, LiquidExpr[int]]):
        super().__init__(Int(), lhs, rhs)


### Boolean operations

class BooleanBinOp(BinOp[bool, bool]):
    def __init__(self, lhs: LiquidExpr[bool], rhs: Union[bool, LiquidExpr[bool]]):
        if lhs.t.python_type != bool:
            raise errors.BinopTypeMismatch(lhs, self, rhs)
        super().__init__(Bool(), lhs, rhs)


@dataclass
class And(BooleanBinOp):
    def __init__(self, lhs: LiquidExpr[bool], rhs: Union[bool, LiquidExpr[bool]]):
        super().__init__(lhs, rhs)


@dataclass
class Or(BooleanBinOp):
    def __init__(self, lhs: LiquidExpr[bool], rhs: Union[bool, LiquidExpr[bool]]):
        super().__init__(lhs, rhs)


## Array operations

@dataclass
class ArrayLen(Generic[_PT], UnaryOp[list[_PT], int]):
    def __init__(self, l: LiquidExpr[list[_PT]]):
        if l.t.python_type != list[_PT]:
            raise errors.UnaryTypeMismatch(self, l)
        super().__init__(l)
