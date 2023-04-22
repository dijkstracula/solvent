import inspect
import ast

import solvent.pretty_print as pp
import solvent.check
from solvent.parse import parse
from solvent.check import typecheck

def check(func):
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)
    #pretty_print(res)
    typecheck(res)
    # # grab the function def out of the module that we get from the
    # # python ast
    # function_def = pyast.body[0]
    # solvent_dsl = FunctionDef.from_pyast(function_def)
    # print(solvent_dsl)
    # print(solvent_dsl.type({}))
    # print(solvent_dsl.unify_type({}))

    return func


## Annotations to step through phase 1 (H-M inference)


def infer_base_constraints(func):
    """ Stops after generating constraints for H-M inference, printing them out. """
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)
    typ, constrs, ctx = solvent.check.check_stmt({}, res)
    print("Constraints:    " + "; ".join([pp.pstring_cvar(c) for c in constrs]))
    print("Ununified type: " + pp.pstring_type(typ))
    return func


def infer_base(func):
    """ Prints the inferred base type and stops checking there. """
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    # TODO: This is currently the body of typecheck(), but replicated
    # here because I imagine liquid var typechecking will also happen
    # in there - if not we can just call it directly.
    typ, constrs, _ = solvent.check.check_stmt({}, res)
    solution = dict(solvent.check.unify(constrs))
    final = solvent.check.finish(typ, solution)
    print("Reconstructed base type: " + pp.pstring_type(final))
    return func
