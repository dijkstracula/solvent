import ast
import inspect
from typing import get_type_hints

from solvent import errors, frontend, parse
from solvent import syntax as syn


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        source, startline = inspect.getsourcelines(func)
        pyast = ast.parse("".join(source))
        res = parse.parse(pyast, get_type_hints(func, include_extras=True))

        syn.NameGenerator.reset()
        try:
            typ = frontend.check(res, quals, debug)
            print(f"{func.__name__}: {typ}")
        except errors.TypeError as e:
            lines = "".join(source).split("\n")
            msg = "Context:\n"
            msg += e.context(lines, startline) + "\n"
            msg += f"Type Error: {e.msg}"
            print(msg)

            raise e

        return func

    return inner
