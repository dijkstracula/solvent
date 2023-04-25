import ast
import inspect

from solvent import parse, frontend


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        pyast = ast.parse(inspect.getsource(func))
        res = parse.parse(pyast)

        typ = frontend.check(res, quals, debug)
        print(f"{func.__name__}: {typ}")

        return func

    return inner
