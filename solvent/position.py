"""
Provides line and position information about python code.
"""

from dataclasses import dataclass
from typing import Any, List

import eff
from termcolor import colored


@dataclass
class Position:
    lineno: int | None = None
    end_lineno: int | None = None
    col_offset: int | None = None
    end_col_offset: int | None = None


class Context(eff.ects):
    lines: List[str]

    @classmethod
    def to_string(cls, msg: str, at: Position):
        res = ""
        pos = at
        startline = 0

        assert pos.lineno is not None
        assert pos.col_offset is not None
        assert pos.end_col_offset is not None

        if pos is not None:
            line = cls.lines[pos.lineno - 1]
            lineno = f"{pos.lineno - 1 + startline} |"
            lineno_width = len(lineno)
            res += lineno + line
            res += "\n"
            res += " " * (pos.col_offset + lineno_width)
            res += "^" * (pos.end_col_offset - pos.col_offset)
        return f"{msg}\n{res}"

    @classmethod
    def single(cls, *, at: Position | None, color: bool = False):
        if at is not None:
            assert at.lineno is not None
            assert at.end_lineno is not None

            line = cls.lines[at.lineno - 1]
            if at.lineno == at.end_lineno:
                res = line[at.col_offset : at.end_col_offset]
            else:
                end_line = cls.lines[at.end_lineno - 1].strip()
                res = f"{line[at.col_offset :]} ... {end_line}"
        else:
            res = "<none>"

        if color:
            return colored(res, "light_green", attrs=[])
        else:
            return res

    @classmethod
    def show(cls, msg: Any, *, at: Position | None):
        print(f"{msg} ({cls.single(at=at, color=True)})")
