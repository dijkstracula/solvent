from dataclasses import dataclass
from typing import Generic, TypeVar, Union

T = TypeVar("T", covariant=True)
U = TypeVar("U", covariant=True)


_cvar_counter = 0


@dataclass
class CVar:
    """ A logic variable to be unified against either other variables or a concrete value. """
    id: int

    def __init__(self):
        global _cvar_counter
        self.id = _cvar_counter
        _cvar_counter += 1

    def __repr__(self):
        return f"?{self.id}"


@dataclass(frozen=True)
class Constraint(Generic[T, U]):
    """ Affirms that two entities should be constrained. """
    lhs: Union[CVar, T]
    rhs: Union[CVar, U]
