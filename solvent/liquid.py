"""
Implement Liquid Type inference
"""

import pprint
from typing import Dict, List, Optional, cast

from solvent import constraints as constr
from solvent import liquid
from solvent import qualifiers
from solvent import qualifiers as quals
from solvent import subtype
from solvent import syntax as syn

Solution = Dict[str, syn.Conjoin]


def solve(
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

    return liquid.constraints_valid(subtype_eqs, solution, show_work)


def constraints_valid(
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
        sc = apply_constr(c, solution)
        valid = subtype.check_constr(sc)
        if show_work:
            print(f"Checking for validity ({valid}): G |- {sc.lhs} <: {sc.rhs}")
        if not valid:
            return constraints_valid(constrs, weaken(c, solution, show_work), show_work)

    return solution


def weaken(c: constr.SubType, solution: Solution, show_work=False) -> Solution:
    """
    Weaken constr and return a new solution.

    Only implementing case 2 right now. I never generate constraints
    of the other forms. I probably should.
    """

    match c:
        case constr.SubType(
            context=ctx,
            assumes=assumes,
            lhs=lhs,
            rhs=syn.RType(
                base=b2, predicate=syn.PredicateVar(name=n), pending_subst=ps
            ),
        ):
            assert n in solution

            qs = []
            for qual in solution[n].conjuncts:
                if show_work:
                    print(f"Checking {qual}: ", end="\n")
                    print(f"  ctx: {apply_ctx(ctx, solution)}")
                    print(f"  constr: {apply_constr(c, solution)}")
                    print(f"  substs: {ps}")
                if subtype.check(
                    apply_ctx(ctx, solution),
                    # constr.Env.empty(),  # TODO: fix
                    assumes,
                    apply(lhs, solution),
                    syn.RType(b2, syn.Conjoin([apply_substs(qual, ps)])),
                    show_work=show_work,
                ):
                    if show_work:
                        print("Ok")
                    qs += [qual]

            solution[n] = syn.Conjoin(qs)
        case x:
            pprint.pprint(x)
            raise NotImplementedError(str(x))

    if show_work:
        print("=================")
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
    return constr.SubType(
        apply_ctx(c.context, solution),
        c.assumes,
        apply(c.lhs, solution),
        apply(c.rhs, solution),
    )


def apply_ctx(ctx: constr.Env, solution: Solution) -> constr.Env:
    return ctx.map(lambda v: apply(v, solution))


def apply(typ: constr.Type, solution: Solution) -> constr.Type:
    match typ:
        case syn.RType(
            base=base, predicate=syn.PredicateVar(name=n), pending_subst=ps
        ) if n in solution:
            cjct = syn.Conjoin([apply_substs(c, ps) for c in solution[n].conjuncts])
            return syn.RType(
                base,
                cjct,
            )
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n), pending_subst=ps):
            return syn.RType.lift(base)
        case syn.ArrowType(args=args, ret=ret, pending_subst=ps):
            return syn.ArrowType(
                args=[(x, apply(t, solution)) for x, t in args],
                ret=apply(ret, solution),
                pending_subst=ps,
            )
        case x:
            return x


def apply_substs(e: syn.Expr, substs: Dict[str, syn.Expr]) -> syn.Expr:
    match e:
        case syn.Variable(name=n) if n in substs:
            return substs[n]
        case syn.BoolOp(lhs=l, op=op, rhs=r):
            return syn.BoolOp(apply_substs(l, substs), op, apply_substs(r, substs))
        case syn.ArithBinOp(lhs=l, op=op, rhs=r):
            return syn.ArithBinOp(apply_substs(l, substs), op, apply_substs(r, substs))
        case syn.Neg(expr=e):
            return syn.Neg(apply_substs(e, substs))
        case syn.Call(function_name=fn, arglist=args):
            return syn.Call(
                apply_substs(fn, substs), [apply_substs(a, substs) for a in args]
            )
        case x:
            return x
