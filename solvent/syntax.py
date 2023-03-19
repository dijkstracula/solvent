import typing
import types

from . import errors

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar

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

_T = TypeVar("_T")
_PT = TypeVar("_PT") #TODO: bounds?

class LiquidType(Generic[_PT]):
    "A liquid type, parameterised over some particular Python type."
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
class Array(LiquidType[list[_T]]):
    elems: LiquidType[_T]

    def __init__(self, elems):
        super().__init__(list[_T])
        self.elems = elems

def fromPyType(t: type) -> LiquidType:
    " Transforms a Python native type that is supported into its Liquid equivalent."
    if t == bool:
        return Bool()
    if t == int:
        return Int()
    if t == str:
        return Str()
    if isinstance(t, types.GenericAlias):
        iterable = t.__origin__
        params = t.__args__
        if iterable == list and len(params) == 1:
            return Array(fromPyType(params[0]))
    raise errors.UnsupportedPyType(t)

@dataclass
class LiquidVar(Generic[_PT]):
    """ A binding of a name to a type.  the `ident` metavariable name should
    match the name of the local Python variable for consistency."""
    ident: str
    t: LiquidType[_PT]

    def __init__(self, ident: str, t: type | LiquidType[_PT]):
        self.ident = ident
        if isinstance(t, type):
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = fromPyType(t)
        else:
            self.t = t

@dataclass
class BinOp(Generic[_PT]):
    lhs: LiquidVar[_PT]
    op: str
    rhs: _PT

    def __init__(self, lhs: LiquidVar[_PT], op: str, rhs: _PT):
        if lhs.t.python_type != type(rhs):
            raise errors.BinopTypeMismatch(lhs, rhs)
        self.lhs = lhs
        self.op = op
        self.rhs = rhs
