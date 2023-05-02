from typing import List


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
