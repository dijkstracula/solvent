import ast
import inspect
from typing import get_type_hints

from solvent import parse, frontend
from solvent import syntax as syn


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
