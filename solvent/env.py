from dataclasses import dataclass
from typing import Any, Dict, List

from solvent import syntax as syn
from solvent.syntax import Type
from solvent.visitor import Visitor


@dataclass(frozen=True)
class Env:
    items: List[tuple[str, Type]]

    @staticmethod
    def empty():
        return Env([])

    def add(self, name: str, typ: Type) -> "Env":
        return Env([(name, typ)] + self.items)

    def map(self, fn):
        return Env([(k, fn(v)) for k, v in self.items])

    def keys(self):
        return list(map(lambda x: x[0], self.items))

    def __getitem__(self, name):
        for n, t in self.items:
            if name == n:
                return t
        raise IndexError(f"{name} not bound in context")

    def __contains__(self, name):
        return name in [x for x, _ in self.items]

    def __str__(self):
        return "{" + ", ".join([f"{x}: {t}" for x, t in self.items]) + "}"


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

    def add(self, name: str, data: Any) -> "ScopedEnv":
        new = ScopedEnv(self.scopes)
        new.scopes[0][name] = data
        return new

    def push_scope(self):
        return ScopedEnv([{}] + self.scopes)

    def pop_scope(self):
        return ScopedEnv(self.scopes[1:])

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
        raise IndexError(f"{name} not bound in context.")

    def __setitem__(self, name, value):
        self.add(name, value)

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


class ScopedEnvVisitor(Visitor):
    def start(self):
        self.env = ScopedEnv.empty()

    def start_FunctionDef(self, fd: syn.FunctionDef):
        # add function name to current scope
        self.env.add(fd.name, fd.typ)
        self.env.push_scope()

        assert isinstance(fd.typ, syn.ArrowType)

        for name, t in fd.typ.args:
            self.env.add(name, t)

    def end_FunctionDef(self, _: syn.FunctionDef):
        self.env.pop_scope()

    def start_Assign(self, stmt: syn.Assign):
        self.env.add(stmt.name, stmt.typ)
