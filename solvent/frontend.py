import inspect
import ast
from solvent.parse import parse
from solvent.pretty_print import pretty_print
from solvent.check import typecheck


def check(func):
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)
    pretty_print(res)
    typecheck(res)
    # # grab the function def out of the module that we get from the
    # # python ast
    # function_def = pyast.body[0]
    # solvent_dsl = FunctionDef.from_pyast(function_def)
    # print(solvent_dsl)
    # print(solvent_dsl.type({}))
    # print(solvent_dsl.unify_type({}))

    return func
