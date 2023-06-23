from ansi.color import fg, fx

from solvent import syntax
from solvent.position import Context


class TypeError(Exception):
    def __init__(self, c, at: syntax.Pos):
        assert at.position is not None

        self.msg = Context.to_string(
            f"This expression has type `{fg.yellow}{c.lhs}{fx.reset}`,"
            + f" but an expression of type `{fg.yellow}{c.rhs}{fx.reset}`"
            + " was expected.",
            at=at.position,
        )

        super().__init__(self.msg)


class UnboundVariable(Exception):
    def __init__(self, var: syntax.Variable):
        self.var = var
        assert var.position is not None
        super().__init__(
            Context.to_string(
                f"Variable {fg.boldred}{var.name}{fx.reset} is not bound in context.",
                at=var.position,
            )
        )


class Unreachable(Exception):
    def __init__(self, *args):
        super().__init__(*args)
