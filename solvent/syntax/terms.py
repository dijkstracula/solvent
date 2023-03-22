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

    def eq(self, other: _PT | "LiquidVar[_PT]") -> "Eq":
        return Eq(self, other)

    def lt(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Lt":
        return Lt(self, other)
    def le(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Le":
        return Le(self, other)
    def gt(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Gt":
        return Gt(self, other)
    def ge(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Ge":
        return Ge(self, other)

    def add(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Add":
        return Add(self, other)
    def sub(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Sub":
        return Sub(self, other)
    def mul(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Mul":
        return Mul(self, other)
    def div(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Div":
        return Div(self, other)
    def mod(self: "LiquidVar[int]", other: Union[int, "LiquidVar[int]"]) -> "Mod":
        return Mod(self, other)

    def band(self: "LiquidVar[bool]", other: Union[bool, "LiquidVar[bool]"]) -> "And":
        return And(self, other)
    def bor(self: "LiquidVar[bool]", other: Union[bool, "LiquidVar[bool]"]) -> "Or":
        return Or(self, other)

# Expressions

EvalT = TypeVar("EvalT", bound=LiquidVar)

## Unary operations

### Boolean operations

### Array operations


## Binary operations

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
    def __init__(self, lhs: LiquidVar[_PT], rhs: Union[_PT, LiquidVar[_PT]]):
        super().__init__(lhs, "=", rhs)

### Numeric comparisons

class NumericBinOp(BinOp[int, EvalT]):
    def __init__(self, lhs: LiquidVar[int], op: str, rhs: Union[int, LiquidVar[int]]):
        if lhs.t.python_type != int:
            raise errors.BinopTypeMismatch(self, op, rhs)
        super().__init__(lhs, op, rhs)

@dataclass
class Le(NumericBinOp[LiquidVar[bool]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "<=", rhs)
@dataclass
class Lt(NumericBinOp[LiquidVar[bool]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "<", rhs)
@dataclass
class Ge(NumericBinOp[LiquidVar[bool]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, ">=", rhs)
@dataclass
class Gt(NumericBinOp[LiquidVar[bool]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, ">", rhs)

### Numeric operations

@dataclass
class Add(NumericBinOp[LiquidVar[int]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "+", rhs)
@dataclass
class Sub(NumericBinOp[LiquidVar[int]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "-", rhs)
@dataclass
class Mul(NumericBinOp[LiquidVar[int]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "*", rhs)
@dataclass
class Div(NumericBinOp[LiquidVar[int]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "/", rhs)
@dataclass
class Mod(NumericBinOp[LiquidVar[int]]):
    def __init__(self, lhs: LiquidVar[int], rhs: Union[int, LiquidVar[int]]):
        super().__init__(lhs, "%", rhs)

### Boolean operations

class BooleanBinOp(BinOp[bool, LiquidVar[bool]]):
    def __init__(self, lhs: LiquidVar[bool], op: str, rhs: Union[bool, LiquidVar[bool]]):
        if lhs.t.python_type != bool:
            raise errors.BinopTypeMismatch(self, op, rhs)
        super().__init__(lhs, op, rhs)

@dataclass
class And(BooleanBinOp):
    def __init__(self, lhs: LiquidVar[bool], rhs: Union[bool, LiquidVar[bool]]):
        super().__init__(lhs, "&&", rhs)
class Or(BooleanBinOp):
    def __init__(self, lhs: LiquidVar[bool], rhs: Union[bool, LiquidVar[bool]]):
        super().__init__(lhs, "||", rhs)
