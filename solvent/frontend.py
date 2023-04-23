import inspect
import ast

import solvent.pretty_print as pp
import solvent.check
from solvent.parse import parse
from solvent.check import typecheck, Eq, SubType, RType
from solvent.subtype import subtype
from solvent.syn import BoolLiteral, BoolOp


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


def infer_base(func):
    """ Prints the inferred base type and stops checking there."""
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    typ, constrs, _ = solvent.check.check_stmt({}, [], res)
    print(f"Function: {pyast.body[0].name}")
    print("  Constraints:")
    for c in constrs:
        match c:
            # TODO: This is janky and displeases me.
            case Eq():
                print(f"    {pp.pstring_cvar(c)}")
            case SubType(lhs=RType(predicate=BoolLiteral(True))):
                print(f"    {pp.pstring_cvar(c)}")
            case SubType(lhs=lhs, rhs=rhs):
                lifted_c = SubType(RType.base(lhs.value), rhs)
                print(f"    {pp.pstring_cvar(lifted_c)}")

    print("  Ununified type: " + pp.pstring_type(typ))
    solution = dict(solvent.check.unify(constrs))
    print("  Solution:")
    for k, v in solution.items():
        print(f"    '{k} := {pp.pstring_type(v)}")
    final = solvent.check.finish(typ, solution)
    print("  Reconstructed base type: " + pp.pstring_type(final))
    return func


def infer_constraints(func):
    """ Prints the inferred base type and scope/flow contraints. """
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    typ, constrs, _ = solvent.check.check_stmt({}, [], res)
    print(f"Function: {pyast.body[0].name}")
    print("  Constraints:")
    for c in constrs:
        match c:
            case SubType(lhs=RType(predicate=BoolOp())):
                print(f"    {pp.pstring_cvar(c)}")
    return func


def infer(func):
    """ Prints the inferred base type and scope/flow contraints,
    then the full inferred program type. """
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    typ, constrs, _ = solvent.check.check_stmt({}, [], res)
    eq_constrs = list(filter(
        lambda x: isinstance(x, Eq),
        constrs
    ))
    subtype_constrs = list(filter(
        lambda x: isinstance(x, SubType),
        constrs
    ))
    print(f"Function: {pyast.body[0].name}")

    print("  Constraints:")
    for c in eq_constrs:
        print(f"    {pp.pstring_cvar(c)}")

    print("  Ununified type: " + pp.pstring_type(typ))
    solution = dict(solvent.check.unify(constrs))

    print("  Solution:")
    for k, v in solution.items():
        print(f"    '{k} := {pp.pstring_type(v)}")
    final = solvent.check.finish(typ, solution)

    print("  Reconstructed type: " + pp.pstring_type(final))

    print("  Subtype Constraints:")
    for c in subtype_constrs:
        c.lhs = solvent.check.finish(c.lhs, solution)
        c.rhs = solvent.check.finish(c.rhs, solution)
        print(f"    {pp.pstring_cvar(c)}")
        subtype(c.assumes, c.lhs, c.rhs)

    return func
