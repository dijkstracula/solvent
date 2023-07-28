"""
Generate constraints for our little subset of Python.

We generate classic equality constraints used for Hindley-Milner,
as well as Sub-type constraints for infering refinement predicates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.syntax import Type


@dataclass
class SubType(syn.Pos):
    """
    Represents a subtype constraint between two types with a context of `assumes'
    """

    context: ScopedEnv
    assumes: List[syn.Expr]
    lhs: Type
    rhs: Type

    def __str__(self):
        asm_str = ", ".join([str(e) for e in self.assumes])
        return f"[{asm_str}] |- {self.lhs} <: {self.rhs}"
