from logging import debug
from typing import List

from ansi.color import fg, fx

from solvent import syntax
from solvent.position import Context


class TypeError(Exception):
    def __init__(self, c):
        msg = (
            f"This expression has type `{c.lhs}`,"
            + f" but an expression of type `{c.rhs}` was expected."
        )
        self.msg = msg
        self.constraint = c
        super().__init__(msg)

    def context(self, lines: List[str], startline: int) -> str:
        res = ""
        pos = self.constraint.position
        if pos is not None:
            line = lines[pos.lineno - 1]
            lineno = f"{pos.lineno - 1 + startline} |"
            lineno_width = len(lineno)
            res += lineno + line
            res += "\n"
            res += " " * (pos.col_offset + lineno_width)
            res += "^" * (pos.end_col_offset - pos.col_offset)
        return res


class UnboundVariable(Exception):
    def __init__(self, var: syntax.Variable):
        self.var = var
        assert var.position is not None
        debug(var.position)
        super().__init__(
            Context.to_string(
                f"Variable {fg.boldred}{var.name}{fx.reset} is not bound in context.",
                at=var.position,
            )
        )


class Unreachable(Exception):
    def __init__(self, *args):
        super().__init__(*args)
