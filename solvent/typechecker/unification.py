from dataclasses import dataclass
from typing import Generic, TypeVar, Union

T = TypeVar("T", covariant=True)
U = TypeVar("U", covariant=True)


_cvar_counter = 0


@dataclass(frozen=True)
class CVar:
    """ A logic variable to be unified against either other variables or a concrete value. """
    id: int

    @staticmethod
    def next() -> "CVar":
        global _cvar_counter
        _cvar_counter += 1
        return CVar(_cvar_counter)

    def __repr__(self):
        return f"?{self.id}"

    @staticmethod
    def reset():
        """ For testing/debugging purposes only."""
        global _cvar_counter
        _cvar_counter = 0


@dataclass(frozen=True)
class Constraint(Generic[T, U]):
    """ Affirms that two entities should be constrained. """
    lhs: Union[CVar, T]
    rhs: Union[CVar, U]
