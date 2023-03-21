from . import types
from .. import errors

from .types import _PT

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Type, Union


@dataclass
class LiquidVar(Generic[_PT]):
    """ A binding of a name to a type.  the `ident` metavariable name should
    match the name of the local Python variable for consistency."""
    ident: str
    t: types.LiquidType[_PT]

    def __init__(self, ident: str, t: Type[_PT] | types.LiquidType[_PT]):
        self.ident = ident
        if isinstance(t, types.LiquidType):
            self.t = t
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.fromPyType(t)

    def eq(self, other: _PT) -> "Eq":
        return Eq(self, other)

    def lt(self: "LiquidVar[int]", other: int) -> "Lt":
        return Lt(self, other)
    def le(self: "LiquidVar[int]", other: int) -> "Le":
        return Le(self, other)
    def gt(self: "LiquidVar[int]", other: int) -> "Gt":
        return Gt(self, other)
    def ge(self: "LiquidVar[int]", other: int) -> "Ge":
        return Ge(self, other)

# Expressions

EvalT = TypeVar("EvalT", bound=LiquidVar)

@dataclass
class BinOp(Generic[_PT, EvalT]):
    """ A binary operation on a liquid variable and a concrete Python one. """
    lhs: LiquidVar[_PT]
    z3_op: str
    rhs: _PT | LiquidVar[_PT]

    def __init__(self, lhs: LiquidVar[_PT], op: str, rhs: _PT | LiquidVar[_PT]):
        if isinstance(rhs, LiquidVar):
            if lhs.t.python_type != rhs.t.python_type:
                raise errors.BinopTypeMismatch(lhs, op, rhs)
        else:
            if lhs.t.python_type != type(rhs):
                raise errors.BinopTypeMismatch(lhs, op, rhs)

        self.lhs = lhs
        self.z3_op = op
        self.rhs = rhs

@dataclass
class Eq(BinOp[_PT, LiquidVar[bool]]):
    def __init__(self, lhs, rhs):
        super().__init__(lhs, "=", rhs)

## Numeric comparisons

@dataclass
class Le(BinOp[int, LiquidVar[bool]]):
    def __init__(self, lhs, rhs):
        if lhs.t != int:
            raise errors.BinopTypeMismatch(self, "<=", rhs)
        super().__init__(lhs, "<=", rhs)

@dataclass
class Lt(BinOp[int, LiquidVar[bool]]):
    def __init__(self, lhs, rhs):
        if lhs.t != int:
            raise errors.BinopTypeMismatch(self, "<", rhs)
        super().__init__(lhs, "<", rhs)

@dataclass
class Ge(BinOp[int, LiquidVar[bool]]):
    def __init__(self, lhs, rhs):
        if lhs.t != int:
            raise errors.BinopTypeMismatch(self, ">=", rhs)
        super().__init__(lhs, ">=", rhs)

@dataclass
class Gt(BinOp[int, LiquidVar[bool]]):
    def __init__(self, lhs, rhs):
        if lhs.t != int:
            raise errors.BinopTypeMismatch(self, ">", rhs)
        super().__init__(lhs, ">", rhs)

