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
PyT = TypeVar("PyT", int, bool, str, list)


class LiquidType(Generic[PyT]):
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
class Array(Generic[PyT], LiquidType[list[PyT]]):
    elem_type: LiquidType[PyT]

    def __init__(self, et: LiquidType[PyT]):
        # TODO: can we avoid type erasure here somehow???
        super().__init__(list)
        self.elem_type = et


def from_py_type(t: Type[PyT]) -> LiquidType:
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
            return Array(from_py_type(params[0]))
    raise errors.UnsupportedPyType(t)

