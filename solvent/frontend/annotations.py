import ast
import inspect
from logging import error, info
from typing import get_type_hints

from solvent import errors, frontend, parse
from solvent import syntax as syn
from solvent.position import Context


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        source, startline = inspect.getsourcelines(func)
        pyast = ast.parse("".join(source))
        res = parse.Parser(get_type_hints(func, include_extras=True)).parse(pyast)
        lines = "".join(source).split("\n")

        syn.NameGenerator.reset()
        with Context(lines=lines):  # type: ignore
            try:
                typ = frontend.check(res, quals)
                info(f"{func.__name__}: {typ}")
            except errors.TypeError as e:
                error(e)
                raise e

        return func

    return inner
