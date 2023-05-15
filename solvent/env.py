from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Dict, List

from solvent import syntax as syn
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

    def add(self, name: str, data: Any) -> "ScopedEnv":
        new = deepcopy(self)
        new.scopes[0][name] = data
        return new

    def add_mut(self, name: str, data: Any):
        self.scopes[0][name] = data

    def push_scope(self) -> "ScopedEnv":
        return ScopedEnv([{}] + self.scopes)

    def push_scope_mut(self):
        self.scopes.insert(0, {})

    def pop_scope(self) -> "ScopedEnv":
        return ScopedEnv(self.scopes[1:])

    def pop_scope_mut(self):
        self.scopes.pop(0)

    def clone(self) -> "ScopedEnv":
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
        raise IndexError(f"{name} not bound in context.")

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


class ScopedEnvVisitor(Visitor):
    def start(self):
        self.env = ScopedEnv.empty()

    def start_FunctionDef(self, fd: syn.FunctionDef):
        assert isinstance(fd.typ, syn.ArrowType)

        # add function name to current scope
        self.env.add_mut(fd.name, fd.typ)

        self.env.push_scope_mut()
        for name, t in fd.typ.args:
            self.env.add_mut(name, t)

    def end_FunctionDef(self, _: syn.FunctionDef):
        self.env.pop_scope_mut()

    def start_Assign(self, stmt: syn.Assign):
        self.env.add_mut(stmt.name, stmt.typ)