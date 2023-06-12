"""
Implement Liquid Type inference
"""

import pprint
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

    TODO: Do I need to split constraints in the environment?
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
                case _:
                    return [c]
        case _:
            return [c]


def solve(
    stmts: List[syn.Stmt],
    constrs: List[constr.SubType],
    quals: List[quals.Qualifier],
    show_work=False,
) -> Solution:
    solution: Solution = {}

    if show_work:
        print("Raw Constraints:")
        for c in constrs:
            Context.show(c, at=c.position)
        print("======")

    # split all the constraints that we have into base constraints
    constrs = sum([split(c) for c in constrs], [])

    ipv = InitialPredicatesVisitor(quals)
    ipv.visit_stmts(stmts)
    solution = ipv.solution

    if show_work:
        print("Initial Constraints:")
        for c in constrs:
            Context.show(c, at=c.position)
        print("======")

        print("Initial Predicates:")
        for k, v in solution.items():
            print(f"{k} := {v}")
        print("======")

    subtype_eqs = cast(
        List[constr.SubType],
        list(
            filter(
                lambda x: isinstance(x, constr.SubType)
                and isinstance(x.lhs, constr.RType)
                and not isinstance(x.lhs.base, constr.TypeVar),
                constrs,
            )
        ),
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
        if show_work:
            Context.show(f"G |- {c.lhs} <: {c.rhs}", at=c.position)
        try:
            valid = subtype.check_constr(sc, show_work)
        except NotImplementedError:
            print("culprit", sc)
            ctx = "\n    ".join([f"{k}: {v}" for k, v in sc.context.items()])
            assums = "\n    ".join([str(a) for a in c.assumes])
            print(f"  Valid? w/ context:\n    {ctx}\n    {assums}")
            raise Exception()

        if show_work:
            ctx = "\n    ".join([f"{k}: {v}" for k, v in sc.context.items()])
            assums = "\n    ".join([str(a) for a in c.assumes])
            print(f"  Valid? ({valid}) w/ context:\n    {ctx}\n    {assums}")
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
                    print(f"  substs: {lhs.pending_subst}, {ps}")
                if subtype.check(
                    apply_ctx(ctx, solution),
                    assumes,
                    apply(lhs, solution),
                    syn.RType(b2, syn.Conjoin([apply_substs(qual, ps)])),
                    show_work=show_work,
                ):
                    if show_work:
                        print("Ok")
                    qs += [qual]

            solution[n] = syn.Conjoin(qs)
        case constr.SubType(lhs=lhs):
            if get_predicate_vars(lhs) is not None:
                raise Exception(f"Invalid constraint: {c}")

            if not subtype.check_constr(c):
                raise Exception(f"Not subtype: {c}")
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
        case syn.ListType(inner_typ=inner):
            return syn.ListType(inner_typ=apply(inner, solution))
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
