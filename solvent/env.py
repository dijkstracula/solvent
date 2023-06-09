from copy import deepcopy
from dataclasses import dataclass
from logging import debug
from typing import Any, Dict, List, Self

from solvent import syntax as syn
from solvent.syntax import Type
from solvent.visitor import Visitor


@dataclass(frozen=True)
class ScopedEnv:
    """
    A scoped environment. Each scope is represented as map from variable names (str)
    to anything. New scopes are prepended to the front of the list of scopes.
    Variables in newer scopes, shadow variables in older scopes.
    """

    scopes: List[Dict[str, Any]]

    @staticmethod
    def empty():
        return ScopedEnv([{}])

    def add(self, name: str, data: Any) -> Self:
        new = deepcopy(self)
        new.scopes[0][name] = data
        return new

    def add_mut(self, name: str, data: Any):
        self.scopes[0][name] = data

    def push_scope(self) -> Self:
        return ScopedEnv([{}] + self.scopes)

    def push_scope_mut(self):
        self.scopes.insert(0, {})

    def pop_scope(self) -> Self:
        return ScopedEnv(self.scopes[1:])

    def pop_scope_mut(self):
        self.scopes.pop(0)

    def clone(self) -> Self:
        return deepcopy(self)

    def map(self, fn):
        return ScopedEnv(
            [{k: fn(v) for k, v in scope.items()} for scope in self.scopes]
        )

    def items(self):
        for scope in self.scopes:
            for k, v in scope.items():
                yield (k, v)

    def keys(self):
        for k, _ in self.items():
            yield k

    def __getitem__(self, name):
        for k, v in self.items():
            if k == name:
                return v
        raise IndexError(f"{name} not bound in context.\n{self}")

    def __setitem__(self, name, value):
        self.add_mut(name, value)

    def __contains__(self, name):
        return name in self.keys()

    def __str__(self):
        return (
            "{"
            + ", ".join(
                [
                    "[" + ", ".join([f"{k}: {v}" for k, v in scope.items()]) + "]"
                    for scope in self.scopes
                ]
            )
            + "}"
        )

    def shape(self) -> Self:
        return self.map(Type.shape)


class ScopedEnvVisitor(Visitor):
    def start(self, initial_env: ScopedEnv | None = None):
        if initial_env is None:
            initial_env = ScopedEnv.empty()
        else:
            debug(f"Starting with {initial_env}")

        self.env = initial_env

    def start_FunctionDef(self, fd: syn.FunctionDef):
        if isinstance(fd.typ, syn.ArrowType):
            # add function name to current scope
            self.env[fd.name] = fd.typ

            self.env.push_scope_mut()
            for name, t in fd.typ.args:
                self.env[name] = t

    def end_FunctionDef(self, fd: syn.FunctionDef):
        if isinstance(fd.typ, syn.ArrowType):
            self.env.pop_scope_mut()

    def end_Assign(self, stmt: syn.Assign):
        self.env[stmt.name] = stmt.typ
