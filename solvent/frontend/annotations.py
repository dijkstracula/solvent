import ast
import inspect
from typing import get_type_hints

from solvent import frontend, parse
from solvent import syntax as syn


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        pyast = ast.parse(inspect.getsource(func))
        res = parse.parse(pyast, get_type_hints(func, include_extras=True))

        syn.NameGenerator.reset()
        typ = frontend.check(res, quals, debug)
        print(f"{func.__name__}: {typ}")

        return func

    return inner
