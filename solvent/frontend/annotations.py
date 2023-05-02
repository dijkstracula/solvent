import ast
import inspect
from typing import get_type_hints

from solvent import errors, frontend, parse
from solvent import syntax as syn


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        source = inspect.getsource(func)
        pyast = ast.parse(source)
        res = parse.parse(pyast, get_type_hints(func, include_extras=True))

        syn.NameGenerator.reset()
        try:
            typ = frontend.check(res, quals, debug)
            print(f"{func.__name__}: {typ}")
        except errors.TypeError as e:
            print(e.msg)
            lines = source.split("\n")
            pos = e.constraint.position
            if pos is not None:
                line = lines[pos.lineno]
                print(line)
                print((" " * (pos.col_offset + 1)) + "^")
            # raise e

        return func

    return inner
