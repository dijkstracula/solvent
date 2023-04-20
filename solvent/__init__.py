from .syntax.quants import RefinementType
from .syntax.types import PyT, BaseType, from_py_type

from dataclasses import dataclass
from typing import Union, Type


@dataclass
class LiquidVar(RefinementType[PyT]):
    """ A binding of a name to a type.  the `ident` metavariable name should
    match the name of the local Python variable for consistency."""
    # TODO: I'm not convinced we want to remember the identifier name here.
    # I thought we'd need it for vc generation, but...
    ident: str

    def __init__(self, ident: str, t: Union[Type[PyT], BaseType[PyT]]):
        # XXX: PyRight complains about:
        # "Argument of type "Type[_PT@LiquidVar] | LiquidType[_PT@LiquidVar]" cannot be assigned to parameter
        #   "tp" of type "Type[_PT@LiquidVar] | LiquidType[_PT@LiquidVar]"
        # if I try to call the superclass' constructor, so it's inlined here.
        if isinstance(t, BaseType):
            self.t = t
        else:
            # TODO: At present, we lose the type parameter on the type returned
            # from `fromPyType()` but I'm not sure how to thread it through.
            self.t = from_py_type(t)
        self.ident = ident
