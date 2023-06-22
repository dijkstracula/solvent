import ast
import inspect
from typing import get_type_hints

from solvent import frontend, parse
from solvent import syntax as syn
from solvent.position import Context


def assert_type(quals, expected):
    """
    A python annotatation that runs our end-to-end liquid type inference
    on a function definition and asserts that it has a particular type.
    """

    def inner(func):
        def repl():
            lines = inspect.getsource(func)
            pyast = ast.parse(lines)
            res = parse.Parser(get_type_hints(func, include_extras=True)).parse(pyast)

            syn.NameGenerator.reset()
            with Context(lines=lines.split("\n")):  # type: ignore
                types = frontend.check(res, quals)
                assert str(types[func.__name__]) == expected

        repl.__name__ = func.__name__

        return repl

    return inner
