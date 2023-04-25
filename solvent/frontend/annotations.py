import ast
import inspect

from solvent import parse, frontend, syntax as syn


def infer(quals=None, debug=False):
    if quals is None:
        quals = []

    def inner(func):
        pyast = ast.parse(inspect.getsource(func))
        res = parse.parse(pyast)

        syn.NameGenerator.reset()
        typ = frontend.check(res, quals, debug)
        print(f"{func.__name__}: {typ}")

        return func

    return inner
