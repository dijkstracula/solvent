"""
Implementation of the Hindley-Milner Unification Algorithm
"""

from solvent.syntax import Type, TypeVar, RType, ArrowType
from solvent.constraints import Constraint, Env, SubType, BaseEq, Scope

from typing import Dict, List, Tuple, cast

Solution = Dict[str, Type]


def base_type_eq(t1: Type, t2: Type) -> bool:
    """
    Implements equality between base types.
    """

    match (t1, t2):
        case (TypeVar(name=n1), TypeVar(name=n2)):
            return n1 == n2
        case (RType(base=v1, predicate=_), RType(base=v2, predicate=_)):
            return v1 == v2
        case (ArrowType(args=args1, ret=ret1), ArrowType(args=args2, ret=ret2)):
            args_eq = all(
                map(lambda a: base_type_eq(a[0][1], a[1][1]), zip(args1, args2))
            )
            return args_eq and base_type_eq(ret1, ret2)
        case _:
            return False


def solve(constrs: List[BaseEq], show_work=False) -> List[tuple[str, Type]]:
    match constrs:
        case []:
            return []
        case [top, *rest]:
            if show_work:
                print("====== unify ======")
                print(f"=> {top}")
                for c in rest:
                    print(c)

            lX = tvar_name(top.lhs)
            rX = tvar_name(top.rhs)

            if base_type_eq(top.lhs, top.rhs):
                return solve(rest, show_work)
            # if lhs is variable
            elif lX is not None and lX not in free_vars(top.rhs):
                return solve(subst(lX, top.rhs, rest), show_work) + [(lX, top.rhs)]
            # if rhs is variable
            elif rX is not None and rX not in free_vars(top.lhs):
                return solve(subst(rX, top.lhs, rest), show_work) + [(rX, top.lhs)]
            # if both are functions variables
            elif (
                isinstance(top.lhs, ArrowType)
                and isinstance(top.rhs, ArrowType)
                and len(top.lhs.args) == len(top.rhs.args)
            ):
                arg_constrs = list(
                    map(
                        lambda a: BaseEq(lhs=a[0][1], rhs=a[1][1]),
                        zip(top.lhs.args, top.rhs.args),
                    )
                )
                ret_constr = BaseEq(lhs=top.lhs.ret, rhs=top.rhs.ret)
                return solve(arg_constrs + [ret_constr] + rest, show_work)
            else:
                raise Exception(f"{top.lhs} is incompatible with {top.rhs}")
        case _:
            raise Exception(f"Constrs wasn't a list: {constrs}")


def unify(
    constrs: List[Constraint], show_work=False
) -> Tuple[List[Constraint], Solution]:
    """
    Find a satisfying assignment of types for a list of equality constraints
    over base types.
    """

    # call solve to find a solution to the system of constraints
    base_eqs = cast(
        List[BaseEq],
        list(filter(lambda x: isinstance(x, BaseEq), constrs)),
    )
    solution = dict(solve(base_eqs, show_work))

    # then use a worklist algorithm to simplify the solution so
    # that you only ever have to look up one step to find the type
    # for a variable.
    # the algorithm works by mainting a list of names that may potentially
    # need updating.

    # we start off wth all the variables
    worklist: List[str] = list(solution.keys())

    # while there are still variables in the worklist
    while len(worklist) != 0:
        # get an element from the worklist
        name: str = worklist.pop()
        match solution[name]:
            case ArrowType():
                solution[name] = apply(solution[name], solution)
            # if this name maps to a variable in the solution,
            # update solution, and add name back to the worklist.
            # it may need to be updated again.
            case RType(base=TypeVar(name=n)) if n in solution:
                solution[name] = solution[n]
                worklist += [name]

    return (apply_constraints(constrs, solution), solution)


def tvar_name(typ: Type):
    """
    Returns the type variable name of `typ' if it exists, and none otherwise.
    """

    match typ:
        case RType(base=TypeVar(name=name)):
            return name


def free_vars(typ: Type):
    """
    Returns the free variables of typ.
    """

    match typ:
        case RType(base=TypeVar(name=n)):
            return [n]
        case RType():
            return []
        case ArrowType(args=args, ret=ret):
            return sum([free_vars(t) for _, t in args], []) + free_vars(ret)
        case x:
            print(x)
            raise NotImplementedError


def subst(name: str, typ: Type, constrs: List[BaseEq]) -> List[BaseEq]:
    res = []
    for x in constrs:
        res.append(
            BaseEq(lhs=subst_one(name, typ, x.lhs), rhs=subst_one(name, typ, x.rhs))
        )

    return res


def subst_one(name: str, tar: Type, src: Type) -> Type:
    match src:
        case RType(base=TypeVar(name=n)) if name == n:
            return tar
        case RType():
            return src
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[(x, subst_one(name, tar, t)) for x, t in args],
                ret=subst_one(name, tar, ret),
            )
        case x:
            print("subst_one:", x)
            raise NotImplementedError


def apply(typ: Type, solution: Solution) -> Type:
    """
    Given a type, resolve all type variables using `solution'.
    """

    match typ:
        case RType(base=TypeVar(name=n), predicate=p) if n in solution:
            new = solution[n]
            if isinstance(new, RType):
                return apply(RType(new.base, p), solution)
            else:
                return new
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[(name, apply(t, solution)) for name, t in args],
                ret=apply(ret, solution),
            )
        case _:
            return typ


def apply_context(context: Env, solution) -> Env:
    """
    Given a type, resolve all type variables using `solution'.
    """

    return {k: apply(v, solution) for k, v in context.items()}


def apply_constraints(
    constrs: List[Constraint], solution: Solution
) -> List[Constraint]:
    res = []
    for c in constrs:
        match c:
            case BaseEq(lhs=lhs, rhs=rhs):
                res += [BaseEq(apply(lhs, solution), apply(rhs, solution))]
            case SubType(assumes=asms, lhs=lhs, rhs=rhs):
                res += [
                    SubType(
                        assumes=asms,
                        lhs=apply(lhs, solution),
                        rhs=apply(rhs, solution),
                    )
                ]
            case Scope(context=ctx, typ=typ):
                res += [
                    Scope(
                        context={k: apply(v, solution) for k, v in ctx.items()},
                        typ=apply(typ, solution),
                    )
                ]
    return res
