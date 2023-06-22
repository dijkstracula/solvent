"""
Provides line and position information about python code.
"""

from dataclasses import dataclass
from logging import debug
from typing import Any, List

import eff
from ansi.color import fg, fx


@dataclass
class Position:
    lineno: int | None = None
    end_lineno: int | None = None
    col_offset: int | None = None
    end_col_offset: int | None = None


class Context(eff.ects):
    lines: List[str]

    @classmethod
    def get_line(cls, lineno: int, highlight: Position | None = None) -> str:
        line = cls.lines[lineno - 1]
        if (
            highlight is not None
            and highlight.col_offset is not None
            and highlight.end_col_offset
        ):
            beg = line[: highlight.col_offset]
            region = line[highlight.col_offset : highlight.end_col_offset]
            end = line[highlight.end_col_offset :]
            line = f"{beg}{fg.boldred}{region}{fx.reset}{end}"

        return f"{line}"

    @classmethod
    def to_string(cls, msg: str, at: Position):
        res = ""
        pos = at
        startline = 0

        assert pos.lineno is not None
        assert pos.col_offset is not None
        assert pos.end_col_offset is not None

        if pos is not None:
            highlight = None
            if pos.lineno == pos.end_lineno:
                highlight = pos
            line = cls.get_line(pos.lineno, highlight)

            lineno = f"{pos.lineno - 1 + startline} "
            lineno_width = len(lineno)

            spacing = " " * (pos.col_offset + lineno_width + 1)
            arrow_width = pos.end_col_offset - pos.col_offset

            res += f"{fg.darkgray}{lineno}│{fx.reset}{line}\n"
            res += spacing
            res += (
                str(fg.boldred) + "┬" + (" " * (arrow_width - 1)) + str(fx.reset) + "\n"
            )

            res += spacing
            res += str(fg.boldred) + "╰" + f"{'─' * (arrow_width - 1)}" + str(fx.reset)
        return f"\n{res} {msg}"

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
            return f"{fx.italic}{fg.magenta}{res}{fx.reset}"
        else:
            return res

    @classmethod
    def show(cls, msg: Any, *, at: Position | None):
        debug(f"{msg} ({cls.single(at=at, color=True)})")
