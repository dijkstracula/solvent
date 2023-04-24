import ast
import inspect

from solvent import parse, frontend


def infer(quals):
    def inner(func):
        pyast = ast.parse(inspect.getsource(func))
        res = parse.parse(pyast)

        frontend.check(res, quals)

        return func
    return inner
