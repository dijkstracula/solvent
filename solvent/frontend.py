import inspect
import ast
from solvent.dsl import FunctionDef


def check(func):
    pyast = ast.parse(inspect.getsource(func))
    # grab the function def out of the module that we get from the
    # python ast
    function_def = pyast.body[0]
    solvent_dsl = FunctionDef.from_pyast(function_def)
    print(solvent_dsl)
    print(solvent_dsl.type({}))
    return func
