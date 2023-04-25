"""
Implement Liquid Type inference
"""

from typing import List, Optional, Dict

from solvent import (
    constraints as constr,
    qualifiers,
    subtype,
    liquid,
    syn,
    qualifiers as quals,
    unification as uni,
)


# DEFAULT_QUALS = [
#     # "(0 < V)",
#     "(0 <= V)",
#     "(x <= V)",
#     "(y <= V)",
#     "(V < x)",
#     "(V < y)",
# ]

Solution = Dict[str, syn.Conjoin]


def solve(
    context: constr.Env,
    constrs: List[constr.SubType],
    quals: List[quals.Qualifier],
    show_work=False,
) -> Solution:
    pred_vars = set()

    for c in constrs:
        pred_vars.add(get_predicate_vars(c.lhs))
        pred_vars.add(get_predicate_vars(c.rhs))

    pred_vars.remove(None)

    # add qualifiers to the solution
    solution: Solution = {pv: qualifiers.predicate(context, quals) for pv in pred_vars}

    if show_work:
        print("Initial Predicates:")
        for k, v in solution.items():
            print(f"{k} := {v}")
        print("======")

    return liquid.constraints_valid(constrs, solution, show_work)


def constraints_valid(
    constrs: List[constr.SubType], solution: Solution, show_work=False
):
    """
    Check if solution satisfies every constraint in constrs.
    Returns the first constraints that is not satisified.
    Returns None otherwise.
    """

    for c in constrs:
        cp = apply_constr(c, solution)
        if not subtype.subtype(cp.assumes, cp.lhs, cp.rhs):
            return constraints_valid(constrs, weaken(c, solution, show_work), show_work)

    return solution


def weaken(c: constr.SubType, solution: Solution, show_work=False) -> Solution:
    """
    Weaken constr and return a new solution.

    Only implementing case 2 right now. I never generate constraints
    of the other forms. I probably should.
    """

    if show_work:
        print(f"Weakening {c}")

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
                if subtype.subtype(
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


def apply(typ: constr.Type, solution: Solution) -> constr.Type:
    match typ:
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n)) if n in solution:
            return syn.RType(base=base, predicate=solution[n])
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n)):
            return syn.RType.lift(base)
        case syn.ArrowType(args=args, ret=ret):
            return syn.ArrowType(
                args=[apply(a, solution) for a in args],
                ret=apply(ret, solution),
            )
        case x:
            return x
