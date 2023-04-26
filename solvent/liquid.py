"""
Implement Liquid Type inference
"""

from typing import List, Optional, Dict, cast

from solvent import (
    constraints as constr,
    qualifiers,
    subtype,
    liquid,
    syntax as syn,
    qualifiers as quals,
)

Solution = Dict[str, syn.Conjoin]


def solve(
    context: constr.Env,
    constrs: List[constr.Constraint],
    quals: List[quals.Qualifier],
    show_work=False,
) -> Solution:
    solution: Solution = {}

    for c in constrs:
        match c:
            case constr.Scope(
                context=ctx, typ=syn.RType(predicate=syn.PredicateVar(name=n))
            ):
                solution[n] = qualifiers.predicate(ctx, quals)

    if show_work:
        print("Initial Predicates:")
        for k, v in solution.items():
            print(f"{k} := {v}")
        print("======")

    subtype_eqs = cast(
        List[constr.SubType],
        list(filter(lambda x: isinstance(x, constr.SubType), constrs)),
    )
    scope_eqs = cast(
        List[constr.Scope],
        list(filter(lambda x: isinstance(x, constr.Scope), constrs)),
    )
    if show_work:
        print("== scope ==")
        for e in scope_eqs:
            print(e)
        print("== scope ==")

    return liquid.constraints_valid(context, subtype_eqs, solution, show_work)


def constraints_valid(
    context: constr.Env,
    constrs: List[constr.SubType],
    solution: Solution,
    show_work=False,
):
    """
    Check if solution satisfies every constraint in constrs.
    Returns the first constraints that is not satisified.
    Returns None otherwise.
    """

    for c in constrs:
        if not subtype.check_constr(
            apply_ctx(context, solution), apply_constr(c, solution)
        ):
            return constraints_valid(
                context, constrs, weaken(context, c, solution, show_work), show_work
            )

    return solution


def weaken(
    context: constr.Env, c: constr.SubType, solution: Solution, show_work=False
) -> Solution:
    """
    Weaken constr and return a new solution.

    Only implementing case 2 right now. I never generate constraints
    of the other forms. I probably should.
    """

    if show_work:
        print(f"Weakening {c}, under { {k: str(v) for k, v in context.items()} }")

    match c:
        case constr.SubType(
            assumes=assumes,
            lhs=lhs,
            rhs=syn.RType(base=b2, predicate=syn.PredicateVar(name=n)),
        ):
            assert n in solution

            qs = []
            for qual in solution[n].conjuncts:
                if show_work:
                    print(f"Checking {qual}: ", end="")
                if subtype.check(
                    apply_ctx(context, solution),
                    assumes,
                    apply(lhs, solution),
                    syn.RType(b2, syn.Conjoin([qual])),
                    show_work=show_work,
                ):
                    if show_work:
                        print("Ok")
                    qs += [qual]

            solution[n] = syn.Conjoin(qs)
        case x:
            print(repr(x))
            raise NotImplementedError

    if show_work:
        print("Current Solution:")
        for k, v in solution.items():
            match v:
                case syn.Type():
                    print(f"  {k}: {v}")
                case x:
                    print(f"  {k}: {x}")

    return solution


def get_predicate_vars(t: syn.Type) -> Optional[str]:
    match t:
        case syn.RType(predicate=syn.PredicateVar(name=name)):
            return name
        case _:
            return None


def apply_constr(c: constr.SubType, solution: Solution) -> constr.SubType:
    return constr.SubType(c.assumes, apply(c.lhs, solution), apply(c.rhs, solution))


def apply_ctx(ctx: constr.Env, solution: Solution) -> constr.Env:
    return {k: apply(v, solution) for k, v in ctx.items()}


def apply(typ: constr.Type, solution: Solution) -> constr.Type:
    match typ:
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n)) if n in solution:
            return syn.RType(base=base, predicate=solution[n])
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n)):
            return syn.RType.lift(base)
        case syn.ArrowType(args=args, ret=ret):
            return syn.ArrowType(
                args=[(x, apply(t, solution)) for x, t in args],
                ret=apply(ret, solution),
            )
        case x:
            return x
