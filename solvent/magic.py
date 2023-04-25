from typing import Callable
from dataclasses import dataclass

from solvent import syn


@dataclass
class MagicSymbol:
    constructor: Callable[[], syn.Expr]

    def __lt__(self, other):
        match other:
            case MagicSymbol():
                return syn.BoolOp(self.constructor(), "<", other.constructor())
            case str():
                return syn.BoolOp(self.constructor(), "<", syn.Variable(other))


V = MagicSymbol(syn.V)
_ = MagicSymbol(syn.Star)
