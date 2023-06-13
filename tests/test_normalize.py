from typing import List
import difflib

from solvent.normalize import normalize
from solvent.syntax import Stmt
from .utils import parse_stmts


def assert_normalize(a: List[Stmt], b: List[Stmt]):
    a_stmts = normalize(a)

    for a_stmt, b_stmt in zip(a_stmts, b):
        if a_stmt != b_stmt:
            a_lines = str(a_stmt).split("\n")
            b_lines = str(b_stmt).split("\n")

            raise Exception("\n".join(list(difflib.context_diff(a_lines, b_lines))))
        else:
            pass


def test_binop():
    @parse_stmts
    def a():
        x = 1 + 1 + 1
        return x

    @parse_stmts
    def b():
        tmp0 = 1 + 1
        x = tmp0 + 1
        return x

    assert_normalize(a, b)


def test_return_expr():
    @parse_stmts
    def a():
        return 1 + 1 + 1

    @parse_stmts
    def b():
        tmp0 = 1 + 1
        return tmp0 + 1

    assert_normalize(a, b)


def test_multi_assign():
    @parse_stmts
    def a():
        v = 0
        v = v + 1
        return v

    @parse_stmts
    def b():
        v = 0
        v0 = v + 1
        return v0

    assert_normalize(a, b)
