"""
Performs classic unification against sequences of constraints between values
and/or logical variables.

Adapted from Norvig: Paradigms of Artificial Intelligence, ch. 11; and, material
from UToronto's CSC324: Principles of Programming Languages course:
http://individual.utoronto.ca/nbtaylor/csc324_s2020/asn2/partb.rkt
"""

from dataclasses import dataclass
from typing import Any, Generic, Optional, TypeVar, Type, Union

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


Env = Optional[dict[CVar, Any]]


@dataclass(frozen=True)
class Constraint(Generic[T, U]):
    """ Affirms that two entities should be constrained. """
    lhs: Union[CVar, T]
    rhs: Union[CVar, U]

    def unify(self, env: Env) -> Env:
        """ See if x and y match given the bindings."""
        if env is None:
            return None
        if self.lhs == self.rhs:
            return env
        if isinstance(self.lhs, CVar):
            return unify_variable(self.lhs, self.rhs, env)
        if isinstance(self.rhs, CVar):
            return unify_variable(self.rhs, self.lhs, env)
        return None


def unify_variable(var: CVar, x: Union[CVar, T], env: Env) -> Env:
    """ Unifies the variable against x, possibly also adding it to the environment. """
    if env is None:
        return env
    if var in env:
        return Constraint(env[var], x).unify(env)
    if isinstance(x, CVar) and x in env:
        return Constraint(var, env[x]).unify(env)
    else:
        new_env = env.copy()
        new_env[var] = x
        return new_env


def subst_env(env: Env, x: Union[CVar, T]) -> Union[CVar, T]:
    if env is None:
        return env
    while isinstance(x, CVar) and x in env:
        x = env[x]
    return x


UnificationEnv = dict["Name", Union[Type, CVar]]


def unifier(constraints: list[Constraint]) -> UnificationEnv:
    """ Return something that unifies with the constraints, or None
    if there's a contradiction."""
    env = {}
    for c in constraints:
        print(c, env)
        env = c.unify(env)
        if env is None:
            return env
    return {x: subst_env(env, x) for x in env}


def flip(lhs: list[Any], rhs: list[Any]) -> list[Constraint]:
    """ A helper to transform two structurally-similar lists into constraints"""
    return [Constraint(l, r) for l, r in zip(lhs, rhs)]
