
from . import types
from .. import errors


from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Type


@dataclass
class LiquidVar(Generic[types._PT]):
    """ A binding of a name to a type.  the `ident` metavariable name should
    match the name of the local Python variable for consistency."""
    ident: str
    t: types.LiquidType[types._PT]

    def __init__(self, ident: str, t: Type[types._PT] | types.LiquidType[types._PT]):
        self.ident = ident
        if isinstance(t, types.LiquidType):
            self.t = t
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = types.fromPyType(t)


# TODO: move to exprs.py
@dataclass
class BinOp(Generic[types._PT]):
    """ A binary operation on a liquid variable and a concrete Python one. """
    lhs: LiquidVar[types._PT]
    op: str
    rhs: types._PT

    def __init__(self, lhs: LiquidVar[types._PT], op: str, rhs: types._PT):
        if lhs.t.python_type != type(rhs):
            raise errors.BinopTypeMismatch(lhs, rhs)
        self.lhs = lhs
        self.op = op
        self.rhs = rhs
