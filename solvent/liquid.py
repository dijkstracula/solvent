"""
Implement Liquid Type inference
"""

import pprint
from logging import debug, info
from typing import Dict, List, cast

from solvent import constraints as constr
from solvent import liquid
from solvent import qualifiers as quals
from solvent import subtype
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.initial_predicates import InitialPredicatesVisitor
from solvent.position import Context

Solution = Dict[str, syn.Conjoin]


def split(c: constr.SubType) -> List[constr.SubType]:
    """
    Split compound constraints into simpler constraints.
    """

    match c:
        case constr.SubType(context=ctx, assumes=asms, lhs=lhs, rhs=rhs):
            match (lhs, rhs):
                case (syn.ListType(inner_typ=t0), syn.ListType(inner_typ=t1)):
                    return split(
                        constr.SubType(
                            ctx,
                            asms,
                            t0.subst(lhs.pending_subst.items()),
                            t1.subst(rhs.pending_subst.items()),
                        ).pos(c)
                    )
                case (
                    syn.ArrowType(args=args0, ret=ret0),
                    syn.ArrowType(args=args1, ret=ret1),
                ):
                    split_constrs = [
                        # arguments are contravariant
                        *[
                            constr.SubType(ctx, asms, a1, a0).pos(c)
                            for (_, a0), (_, a1) in zip(args0, args1)
                        ],
                        # ret type is covariant
                        # TODO: I don't add arguments to the context like in the algo
                        # I probably should?
                        constr.SubType(ctx, asms, ret0, ret1).pos(c),
                    ]
                    return sum([split(x) for x in split_constrs], [])
                case (
                    syn.ObjectType(generic_args=args1),
                    syn.ObjectType(generic_args=args2),
                ):
                    split_constrs = [
                        constr.SubType(
                            ctx,
                            asms,
                            t0.subst(lhs.pending_subst.items()),
                            t1.subst(rhs.pending_subst.items()),
                        ).pos(c)
                        for t0, t1 in zip(args1, args2)
                    ]
                    return sum([split(x) for x in split_constrs], [])
                # case (syn.ObjectType(fields=f1), syn.ObjectType(fields=f2)):
                #     split_constrs = [
                #         # TODO: Variance for field constraints???
                #         constr.SubType(
                #             ctx,
                #             asms,
                #             t0.subst(lhs.pending_subst.items()),
                #             t1.subst(rhs.pending_subst.items()),
                #         ).pos(c)
                #         for (_, t0), (_, t1) in zip(
                #             sorted(f1.items()), sorted(f2.items())
                #         )
                #     ]
                #     return sum([split(x) for x in split_constrs], [])

                case _:
                    return [c]
        case _:
            return [c]


def solve(
    stmts: List[syn.Stmt],
    constrs: List[constr.SubType],
    quals: List[quals.Qualifier],
    types: Dict[int, syn.Type],
) -> Solution:
    debug("Raw Constraints:")
    for c in constrs:
        Context.debug(c, at=c.position)
    debug("======")

    # split all the constraints that we have into base constraints
    constrs = sum([split(c) for c in constrs], [])

    debug("Constraints after splitting:")
    for c in constrs:
        Context.debug(c, at=c.position)
    debug("======")

    ipv = InitialPredicatesVisitor(quals, types)
    ipv.visit_stmts(stmts)
    solution = ipv.solution

    info("Initial Predicates:")
    for k, v in solution.items():
        info(f"{k} := {v}")
    info("======")

    subtype_eqs = cast(
        List[constr.SubType],
        list(
            filter(
                lambda x: isinstance(x, constr.SubType)
                and isinstance(x.lhs, syn.RType)
                and not isinstance(x.lhs.base, syn.TypeVar),
                constrs,
            )
        ),
    )

    return liquid.constraints_valid(subtype_eqs, solution, types)


def constraints_valid(
    constrs: List[constr.SubType], solution: Solution, types: Dict[int, syn.Type]
):
    """
    Check if solution satisfies every constraint in constrs.
    Returns the first constraints that is not satisified.
    Returns None otherwise.
    """

    for c in constrs:
        sc = apply_constr(c, solution)
        Context.show(f"G |- {c.lhs} <: {c.rhs}", at=c.position)
        try:
            valid = subtype.check_constr(sc, types)
        except NotImplementedError as e:
            info("culprit", sc)
            ctx = "\n    ".join([f"{k}: {v}" for k, v in sc.context.items()])
            assums = "\n    ".join([str(a) for a in c.assumes])
            info(f"  Valid? w/ context:\n    {ctx}\n    {assums}")
            raise e

        ctx = "\n    ".join([f"{k}: {v}" for k, v in sc.context.items()])
        assums = "\n    ".join([str(a) for a in c.assumes])
        info(f"  Valid? ({valid}) w/ context:\n    {ctx}\n    {assums}")

        if not valid:
            return constraints_valid(constrs, weaken(c, solution, types), types)

    return solution


def weaken(
    c: constr.SubType, solution: Solution, types: Dict[int, syn.Type]
) -> Solution:
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
                info(f"Checking {qual}: ")
                info(f"  ctx: {apply_ctx(ctx, solution)}")
                info(f"  constr: {apply_constr(c, solution)}")
                info(f"  substs: {lhs.pending_subst}, {ps}")

                if subtype.check(
                    apply_ctx(ctx, solution),
                    types,
                    assumes,
                    apply(lhs, solution),
                    syn.RType(b2, syn.Conjoin([qual.apply_substs(ps)])),
                ):
                    info("Ok")
                    qs += [qual]

            solution[n] = syn.Conjoin(qs)
        case constr.SubType(lhs=lhs):
            if get_predicate_vars(lhs) is not None:
                raise Exception(f"Invalid constraint: {c}")

            if not subtype.check_constr(c, types):
                raise Exception(f"Not subtype: {c}")
        case x:
            raise NotImplementedError(pprint.pformat(x))

    info("=================")
    info("Current Solution:")
    for k, v in solution.items():
        match v:
            case syn.Type():
                info(f"  {k}: {v}")
            case x:
                info(f"  {k}: {x}")

    return solution


def get_predicate_vars(t: syn.Type) -> List[str]:
    match t:
        case syn.RType(predicate=syn.PredicateVar(name=name)):
            return [name]
        case syn.ArrowType(args=args, ret=ret):
            return sum(
                [get_predicate_vars(t) for _, t in args], []
            ) + get_predicate_vars(ret)
        case _:
            return []


def apply_constr(c: constr.SubType, solution: Solution) -> constr.SubType:
    return constr.SubType(
        apply_ctx(c.context, solution),
        c.assumes,
        apply(c.lhs, solution),
        apply(c.rhs, solution),
        position=c.position,
    )


def apply_ctx(ctx: ScopedEnv, solution: Solution) -> ScopedEnv:
    return ctx.map(lambda v: apply(v, solution))


def apply(typ: syn.Type, solution: Solution) -> syn.Type:
    match typ:
        case syn.RType(
            base=base, predicate=syn.PredicateVar(name=n), pending_subst=ps
        ) if n in solution:
            cjct = syn.Conjoin([c.apply_substs(ps) for c in solution[n].conjuncts])
            return syn.RType(
                base,
                cjct,
            )
        case syn.RType(base=base, predicate=syn.PredicateVar(name=n), pending_subst=ps):
            return syn.RType.lift(base)
        case syn.ArrowType(type_abs=abs, args=args, ret=ret, pending_subst=ps):
            return syn.ArrowType(
                type_abs=abs,
                args=[(x, apply(t, solution)) for x, t in args],
                ret=apply(ret, solution),
                pending_subst=ps,
            )
        case syn.ListType(inner_typ=inner):
            return syn.ListType(inner_typ=apply(inner, solution))
        case syn.ObjectType(name=name, generic_args=args):
            return syn.ObjectType(name, [apply(typ, solution) for typ in args])
        case x:
            return x
