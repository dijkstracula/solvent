from dataclasses import dataclass
from typing import List

from solvent.syntax import Type


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
