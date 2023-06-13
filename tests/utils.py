import ast
import inspect
from typing import get_type_hints, List

from solvent import parse, frontend
from solvent import syntax as syn
from solvent.visitor import Visitor


def assert_type(quals, expected):
    """
    A python annotatation that runs our end-to-end liquid type inference
    on a function definition and asserts that it has a particular type.
    """

    def inner(func):
        def repl():
            pyast = ast.parse(inspect.getsource(func))
            res = parse.parse(pyast, get_type_hints(func, include_extras=True))

            syn.NameGenerator.reset()
            assert str(frontend.check(res, quals)) == expected

        repl.__name__ = func.__name__

        return repl

    return inner


class RemovePosition(Visitor):
    def start_Stmt(self, stmt: syn.Stmt):
        super().start_Stmt(stmt)

        stmt.position = None

    def start_Expr(self, expr: syn.Expr):
        super().start_Expr(expr)

        expr.position = None

    def end_FunctionDef(self, fd: syn.FunctionDef):
        super().end_FunctionDef(fd)

        fd.name = "fut"
        return fd


def parse_stmts(func) -> List[syn.Stmt]:
    lines = inspect.getsource(func).split("\n")
    indent = len(lines[0]) - len(lines[0].lstrip())
    source = "\n".join([l[indent:] for l in lines])

    syn.NameGenerator.reset()
    pyast = ast.parse(source)
    res = parse.parse(pyast, get_type_hints(func, include_extras=True))

    return RemovePosition().visit_stmts(res)
