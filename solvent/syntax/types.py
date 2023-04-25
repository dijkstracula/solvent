"""
Functions to manipulate the base types we consider.

TODO: Perhaps rename the enclosing syntax package to `types`?
TODO: Perhaps rename this to "base" or something?  The core LiquidType class would have to be moved out.
"""

import types as py_types

from .. import errors

import ast

from dataclasses import dataclass
from typing import Generic, TypeVar, Type

# AST grammar:
#
# LiquidType   := <LiquidVar> "|" <Predicate>
#
# LiquidVar    := L[<PyType>]
# PyType       := "int" | "bool" | "list[" PyType "]"
#
# Predicate     := <LiquidVarRVal> <BinOp> <PyVal>
# LiquidVarLVal := <LiquidVar> | <LiquidVar>.len
# BinOp         := "=" | "<" | "<=" | ">=" | ">"
# PyVal         := int | bool | str | list[PyVal]
#
# e.g. x = L[int];        x | x >= 0 and x < 10
# e.g. l = L[list[bool]]; l | l.len > 0

EvalT = TypeVar("EvalT", int, bool, list)
PyT = TypeVar("PyT", int, bool, list)
PyT2 = TypeVar("PyT2", int, bool, list)


class BaseType(Generic[PyT]):
    """A liquid type, parameterised over some particular Python type."""

    python_type: type

    def __init__(self, t: type):
        self.python_type = t


@dataclass
class Int(BaseType[int]):
    def __init__(self):
        super().__init__(int)


@dataclass
class Bool(BaseType[bool]):
    def __init__(self):
        super().__init__(bool)


@dataclass
class Array(Generic[PyT], BaseType[list[PyT]]):
    elem_type: BaseType[PyT]

    # TODO: We need a way of quantifying over all the elements, which I don't think
    # this syntax lets us do precisely.  Think about how to do that - we need ultimately
    # i = Int(); a = Array(i);
    # a.suchThat(a.len() > 0)
    # a.suchThat(i > 0)
    def __init__(self, et: BaseType[PyT]):
        # TODO: can we avoid type erasure here somehow???
        super().__init__(list)
        self.elem_type = et


def from_py_type(t: Type[PyT]) -> BaseType:
    """Transforms a Python native type that is supported into its Liquid equivalent."""
    if t == bool:
        return Bool()
    if t == int:
        return Int()
    if isinstance(t, py_types.GenericAlias):
        iterable = t.__origin__
        params = t.__args__
        if iterable == list and len(params) == 1:
            return Array(from_py_type(params[0]))
    raise errors.UnsupportedPyType(t)
