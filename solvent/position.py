"""
Provides line and position information about python code.
"""

from dataclasses import dataclass


@dataclass
class Position:
    lineno: int | None = None
    end_lineno: int | None = None
    col_offset: int | None = None
    end_col_offset: int | None = None
