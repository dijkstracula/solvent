import types as py_types

from .. import errors

from dataclasses import dataclass
from typing import Generic, TypeVar, Type

# AST grammar:
#
# LiquidType   := <LiquidVar> "|" <Predicate>
#
# LiquidVar    := L[<PyType>]
# PyType       := "int" | "bool" | "str" | "list[" PyType "]"
#
# Predicate     := <LiquidVarRVal> <BinOp> <PyVal>
# LiquidVarLVal := <LiquidVar> | <LiquidVar>.len
# BinOp         := "=" | "<" | "<=" | ">=" | ">"
# PyVal         := int | bool | str | list[PyVal]
#
# e.g. x = L[int];       x | x >= 0 and x < 10
# e.g. l = L[list[str]]; l | l.len > 0

EvalT = TypeVar("EvalT", int, bool, str, list)
_PT = TypeVar("_PT", int, bool, str, list)


class LiquidType(Generic[_PT]):
    """A liquid type, parameterised over some particular Python type."""
    python_type: type

    def __init__(self, t: type):
        self.python_type = t


@dataclass
class Int(LiquidType[int]):
    def __init__(self): super().__init__(int)


@dataclass
class Bool(LiquidType[bool]):
    def __init__(self): super().__init__(bool)


@dataclass
class Str(LiquidType[str]):
    def __init__(self): super().__init__(str)


@dataclass
class Array(LiquidType[list[_PT]]):
    elems: LiquidType[_PT]

    def __init__(self, elems):
        super().__init__(list[_PT])
        self.elems = elems


def fromPyType(t: Type[_PT]) -> LiquidType:
    """ Transforms a Python native type that is supported into its Liquid equivalent."""
    if t == bool:
        return Bool()
    if t == int:
        return Int()
    if t == str:
        return Str()
    if isinstance(t, py_types.GenericAlias):
        iterable = t.__origin__
        params = t.__args__
        if iterable == list and len(params) == 1:
            return Array(fromPyType(params[0]))
    raise errors.UnsupportedPyType(t)

