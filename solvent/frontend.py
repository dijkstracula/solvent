import inspect
import ast

import solvent.pretty_print as pp
import solvent.check
from solvent.parse import parse
from solvent.check import Constraint, typecheck, BaseEq, SubType, RType
from solvent.subtype import subtype
from solvent.syn import ArrowType, BoolLiteral, BoolOp, Type
from solvent import liquid, syn


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

def baseify_type(typ: Type) -> Type:
    """ Removes all refinements from a type.  (Needed for infer_base because
    we want to show base inference in isolation from predicate refinement)"""
    match typ:
        case RType(value=value):
            return RType.base(value)
        case ArrowType(args=args, ret=ret):
            return ArrowType([baseify_type(t) for t in args], baseify_type(ret))
        case _:
            return typ  # and hope for the best!


def baseify_constraint(c: Constraint) -> Constraint:
    """ Removes all refinements from a type constraint.  (Needed for infer_base
    because we want to show base inference in isolation from predicate refinement)"""
    match c:
        # TODO: This is janky and displeases me.
        case BaseEq(lhs=lhs, rhs=rhs):
            return BaseEq(baseify_type(lhs), baseify_type(rhs))
        case SubType(lhs=lhs, rhs=rhs):
            return SubType([], baseify_type(lhs), baseify_type(rhs))


def infer_base(func):
    """ Prints the inferred base type and stops checking there."""
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    typ, constrs, _ = solvent.check.check_stmt({}, [], res)
    typ = baseify_type(typ)
    constrs = [baseify_constraint(c) for c in constrs]
    print(f"Function: {pyast.body[0].name}")
    print("  Ununified type: " + pp.pstring_type(typ))
    print("  Constraints:")
    for c in constrs:
        if isinstance(c, BaseEq):
            print(f"    {pp.pstring_cvar(c)}")

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
    solution = dict(solvent.check.unify(constrs))
    print(f"Function: {pyast.body[0].name}")
    print("  Constraints:")
    for c in constrs:
        match c:
            case SubType(lhs=RType(predicate=BoolOp())):
                c.lhs = solvent.check.finish(c.lhs, solution)
                c.rhs = solvent.check.finish(c.rhs, solution)
                print(f"    {pp.pstring_cvar(c)}")
    return func



def infer(func):
    """ Cuts to the chance and just prints the full inferred program type. """
    pyast = ast.parse(inspect.getsource(func))
    res = parse(pyast)

    typ, constrs, _ = solvent.check.check_stmt({}, [], res)
    eq_constrs = list(filter(
        lambda x: isinstance(x, BaseEq),
        constrs
    ))
    print(f"Function: {pyast.body[0].name}")

    solution = dict(solvent.check.unify(constrs))

    for c in constrs:
        c.lhs = solvent.check.finish(c.lhs, solution)
        c.rhs = solvent.check.finish(c.rhs, solution)
    solution = liquid.solve(constrs, solution)

    final = solvent.check.finish(typ, solution)
    print("Reconstructed type: " + pp.pstring_type(final))

    return func


def infer_full(quals):
    def inner(func):
        """ Prints the inferred base type and scope/flow contraints,
        then the full inferred program type. """
        pyast = ast.parse(inspect.getsource(func))
        res = parse(pyast)

        typ, constrs, _ = solvent.check.check_stmt({}, [], res)
        eq_constrs = list(filter(
            lambda x: isinstance(x, BaseEq),
            constrs
        ))
        print(f"Function: {pyast.body[0].name}")

        print("  Constraints:")
        for c in eq_constrs:
            print(f"    {pp.pstring_cvar(c)}")

        print("  Ununified type: " + pp.pstring_type(typ))
        solution = dict(solvent.check.unify(constrs))

        print("  HM Solution:")
        for k, v in solution.items():
            print(f"    '{k} := {pp.pstring_type(v)}")

        for c in constrs:
            c.lhs = solvent.check.finish(c.lhs, solution)
            c.rhs = solvent.check.finish(c.rhs, solution)
        solution = liquid.solve(constrs, solution, quals)

        print("  Final Solution:")
        for k, v in solution.items():
            match v:
                case syn.Type():
                    print(f"    '{k} := {pp.pstring_type(v)}")
                case syn.Expr():
                    print(f"    '{k} := {pp.pstring_expr(v)}")
                case [*exprs]:
                    print(f"    '{k} := {[pp.pstring_expr(x) for x in exprs]}")

        final = solvent.check.finish(typ, solution)
        print("Reconstructed type: " + pp.pstring_type(final))

    return inner
