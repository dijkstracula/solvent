""" Type-level DSL for qualified types independent of program terms

At parse time, we are able to convert many program annotations into internal
AST nodes.  For instance, given the program fragment

```
i: i > 0 = 42
```

We extract the annotation `i > 0` from the assignment and transform it into the syntax
subtree `dsl.Compare(dsl.Name("i"), ">=", dsl.Constant(0))`.  Meanwhile, the typechecker
will produce a base type of `int`.  We next[1] have to qualify this type with the constraint
`{i: int | i == 42}`, or, more precisely, `Int().eq(42)`.  This module contains the internal
representation of this final refined type.

TODO: Perhaps rename to something like refined.py?

[1] TODO: Still have to lift base types into their refinements!
"""

from . import types
from .. import errors

from .types import PyT, PyT2, EvalT
from .types import BaseType, Bool, Int

from dataclasses import dataclass
from typing import Generic, Type, Union


@dataclass
class RefinementType(Generic[PyT]):
    t: BaseType[PyT]

    def __init__(self, tp: Union[Type[PyT], BaseType[PyT]]):
        if isinstance(tp, BaseType):
            self.t = tp
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.from_py_type(tp)

    def to_vc(self):
        raise Exception(f"Missing to_vc() implementation for {type(self)}")

    # AST creation methods

    def eq(self: "RefinementType[PyT]", other: PyT | "RefinementType[PyT]") -> "Eq":
        return Eq(self, other)

    def lt(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Lt":
        return Lt(self, other)

    def le(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Le":
        return Le(self, other)

    def gt(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Gt":
        return Gt(self, other)

    def ge(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Ge":
        return Ge(self, other)

    def band(self: "RefinementType[bool]", other: Union[bool, "RefinementType[bool]"]) -> "And":
        return And(self, other)

    def bor(self: "RefinementType[bool]", other: Union[bool, "RefinementType[bool]"]) -> "Or":
        return Or(self, other)

    def add(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Add":
        return Add(self, other)

    def sub(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Sub":
        return Sub(self, other)

    def mul(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Mul":
        return Mul(self, other)

    def div(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Div":
        return Div(self, other)

    def mod(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Mod":
        return Mod(self, other)

    def len(self: "RefinementType[list[PyT]]"):
        return ArrayLen(self)

    # Operator overloading
    def __add__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Add":
        return self.add(other)

    def __sub__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Sub":
        return self.sub(other)

    def __mul__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Mul":
        return self.mul(other)

    def __truediv__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Div":
        return self.div(other)

    def __mod__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Mod":
        return self.mod(other)

    def __and__(self: "RefinementType[bool]", other: Union[bool, "RefinementType[bool]"]) -> "RefinementType[bool]":
        return self.band(other)

    def __or__(self: "RefinementType[bool]", other: Union[bool, "RefinementType[bool]"]) -> "RefinementType[bool]":
        return self.bor(other)

    def __le__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Le":
        return self.le(other)

    def __lt__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Lt":
        return self.lt(other)

    def __gt__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Gt":
        return self.gt(other)

    def __ge__(self: "RefinementType[int]", other: Union[int, "RefinementType[int]"]) -> "Ge":
        return self.ge(other)


# LiquidExpr = Union[Type[_PT], AstNode[_PT]]

# Expressions

@dataclass
class UnaryOp(Generic[PyT, EvalT], RefinementType[EvalT]):
    """ A uniary operation on a liquid variable. """
    target: RefinementType[PyT]


class BinOp(Generic[PyT, PyT2, EvalT], RefinementType[EvalT]):
    """ A binary operation on a liquid variable and a concrete Python one."""
    lhs: RefinementType[PyT]
    rhs: PyT2 | RefinementType[PyT2]

    def __init__(self, t: BaseType[EvalT], lhs: RefinementType[PyT], rhs: PyT2 | RefinementType[PyT2]):
        super().__init__(t)
        if isinstance(rhs, RefinementType):
            if lhs.t.python_type != rhs.t.python_type:
                raise errors.BinopTypeMismatch(lhs, self, rhs)
        else:
            if lhs.t.python_type != type(rhs):
                raise errors.BinopTypeMismatch(lhs, self, rhs)

        self.lhs = lhs
        self.rhs = rhs


@dataclass
class Eq(BinOp[PyT, PyT, bool]):
    def __init__(self, lhs: RefinementType[PyT], rhs: Union[PyT, RefinementType[PyT]]):
        super().__init__(Bool(), lhs, rhs)


### Numeric comparisons

class NumericBinOp(BinOp[int, int, EvalT]):
    def __init__(self, t: BaseType[EvalT], lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        if lhs.t.python_type != int:
            raise errors.BinopTypeMismatch(self, self, rhs)
        super().__init__(t, lhs, rhs)


@dataclass
class Le(NumericBinOp[bool]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Lt(NumericBinOp[bool]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Ge(NumericBinOp[bool]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Bool(), lhs, rhs)


@dataclass
class Gt(NumericBinOp[bool]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Bool(), lhs, rhs)


### Numeric operations

@dataclass
class Add(NumericBinOp[int]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Sub(NumericBinOp[int]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Mul(NumericBinOp[int]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Div(NumericBinOp[int]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Int(), lhs, rhs)


@dataclass
class Mod(NumericBinOp[int]):
    def __init__(self, lhs: RefinementType[int], rhs: Union[int, RefinementType[int]]):
        super().__init__(Int(), lhs, rhs)


### Boolean operations

class BooleanBinOp(BinOp[bool, bool, bool]):
    def __init__(self, lhs: RefinementType[bool], rhs: Union[bool, RefinementType[bool]]):
        if lhs.t.python_type != bool:
            raise errors.BinopTypeMismatch(lhs, self, rhs)
        super().__init__(Bool(), lhs, rhs)


@dataclass
class And(BooleanBinOp):
    def __init__(self, lhs: RefinementType[bool], rhs: Union[bool, RefinementType[bool]]):
        super().__init__(lhs, rhs)


@dataclass
class Or(BooleanBinOp):
    def __init__(self, lhs: RefinementType[bool], rhs: Union[bool, RefinementType[bool]]):
        super().__init__(lhs, rhs)


# Array operations

@dataclass
class ArrayLen(Generic[PyT], UnaryOp[list[PyT], int]):
    def __init__(self, l: RefinementType[list[PyT]]):
        super().__init__(l, target=l)
        if l.t.python_type != list:
            raise errors.UnaryTypeMismatch(self, l)


Predicate = RefinementType[bool]