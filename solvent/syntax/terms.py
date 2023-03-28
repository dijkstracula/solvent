from . import types
from .. import errors

from .types import PyT, PyT2, EvalT
from .types import LiquidType, Bool, Int

from dataclasses import dataclass
from typing import Generic, Type, Union


# TODO: This class represents intermediary nodes in the AST, so this means that terminals are not actually
# expressions.  I'd like LiquidExpr to be something like a Union[Type[_PT], AstNode[_PT]] (with this class renamed
# to AstNode) but I'm getting a "can't subclass Union" exception that I haven't been able to diagnose yet.
class LiquidExpr(Generic[PyT]):
    t: LiquidType[PyT]

    def __init__(self, tp: Union[Type[PyT], LiquidType[PyT]]):
        if isinstance(tp, LiquidType):
            self.t = tp
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.from_py_type(tp)

    def to_vc(self):
        raise Exception(f"Missing to_vc() implementation for {type(self)}")

    # AST creation methods

    def eq(self: "LiquidExpr[PyT]", other: PyT | "LiquidExpr[PyT]") -> "Eq":
        return Eq(self, other)

    def lt(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Lt":
        return Lt(self, other)

    def le(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Le":
        return Le(self, other)

    def gt(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Gt":
        return Gt(self, other)

    def ge(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Ge":
        return Ge(self, other)

    def band(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "And":
        return And(self, other)

    def bor(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "Or":
        return Or(self, other)

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

    def len(self: "LiquidExpr[list[PyT]]"):
        return ArrayLen(self)

    # Operator overloading
    def __add__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Add":
        return self.add(other)

    def __sub__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Sub":
        return self.sub(other)

    def __mul__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Mul":
        return self.mul(other)

    def __truediv__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Div":
        return self.div(other)

    def __mod__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Mod":
        return self.mod(other)

    def __and__(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "LiquidExpr[bool]":
        return self.band(other)

    def __or__(self: "LiquidExpr[bool]", other: Union[bool, "LiquidExpr[bool]"]) -> "LiquidExpr[bool]":
        return self.bor(other)

    def __le__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Le":
        return self.le(other)

    def __lt__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Lt":
        return self.lt(other)

    def __gt__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Gt":
        return self.gt(other)

    def __ge__(self: "LiquidExpr[int]", other: Union[int, "LiquidExpr[int]"]) -> "Ge":
        return self.ge(other)


# LiquidExpr = Union[Type[_PT], AstNode[_PT]]

# Expressions

@dataclass
class UnaryOp(Generic[PyT, EvalT], LiquidExpr[EvalT]):
    """ A uniary operation on a liquid variable. """
    target: LiquidExpr[PyT]


class BinOp(Generic[PyT, PyT2, EvalT], LiquidExpr[EvalT]):
    """ A binary operation on a liquid variable and a concrete Python one."""
    lhs: LiquidExpr[PyT]
    rhs: PyT2 | LiquidExpr[PyT2]

    def __init__(self, t: LiquidType[EvalT], lhs: LiquidExpr[PyT], rhs: PyT2 | LiquidExpr[PyT2]):
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
class Eq(BinOp[PyT, PyT, bool]):
    def __init__(self, lhs: LiquidExpr[PyT], rhs: Union[PyT, LiquidExpr[PyT]]):
        super().__init__(Bool(), lhs, rhs)


### Numeric comparisons

class NumericBinOp(BinOp[int, int, EvalT]):
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

class BooleanBinOp(BinOp[bool, bool, bool]):
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


# Array operations

@dataclass
class ArrayLen(Generic[PyT], UnaryOp[list[PyT], int]):
    def __init__(self, l: LiquidExpr[list[PyT]]):
        super().__init__(l)
        if l.t.python_type != list:
            raise errors.UnaryTypeMismatch(self, l)


Predicate = LiquidExpr[bool]