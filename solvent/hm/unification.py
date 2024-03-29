"""
Implementation of the Hindley-Milner Unification Algorithm
"""

from logging import info
from typing import Dict, List, Tuple

from solvent import errors
from solvent.env import ScopedEnv
from solvent.syntax import (
    AnyType,
    ArrowType,
    HMType,
    ListType,
    ObjectType,
    RType,
    Type,
    TypeVar,
    Unknown,
    base_type_eq,
)
from solvent.utils import unwrap

from .constraints import BaseEq

Solution = Dict[str, Type]


def solve(constrs: List[BaseEq]) -> List[tuple[str, Type]]:
    match constrs:
        case []:
            return []
        case [top, *rest]:
            info(
                "unification step",
                top,
                "  rest:" if len(rest) > 0 else "<none>",
                *rest,
            )
            # info("====== unify ======")
            # info(f"=> {top}")
            # for c in rest:
            #     info(c)

            lX = tvar_name(top.lhs)
            rX = tvar_name(top.rhs)

            if base_type_eq(top.lhs, top.rhs):
                return solve(rest)
            # if lhs is variable
            elif lX is not None and lX not in free_vars(top.rhs):
                return solve(subst(lX, top.rhs, rest)) + [(lX, top.rhs)]
            # if rhs is variable
            elif rX is not None and rX not in free_vars(top.lhs):
                return solve(subst(rX, top.lhs, rest)) + [(rX, top.lhs)]
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
                return solve(arg_constrs + [ret_constr] + rest)
            elif isinstance(top.lhs, ListType) and isinstance(top.rhs, ListType):
                inner_constr = BaseEq(lhs=top.lhs.inner_typ, rhs=top.rhs.inner_typ).pos(
                    top.lhs.inner_typ
                )
                return solve([inner_constr] + rest)
            else:
                raise errors.TypeError(top, at=top)
        case _:
            raise Exception(f"Constrs wasn't a list: {constrs}")


def unify(constrs: List[BaseEq]) -> Tuple[List[BaseEq], Solution]:
    """
    Find a satisfying assignment of types for a list of equality constraints
    over base types.
    """

    # call solve to find a solution to the system of constraints
    solution = dict(solve(constrs))

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
            # if this name maps to a variable in the solution,
            # update solution, and add name back to the worklist.
            # it may need to be updated again.
            case HMType(TypeVar(name=n)) if n in solution:
                solution[name] = solution[n]
                worklist += [name]
            # otherwise call apply
            case x:
                solution[name] = apply(x, solution)

    return (apply_constraints(constrs, solution), solution)


def tvar_name(typ: Type):
    """
    Returns the type variable name of `typ' if it exists, and none otherwise.
    """

    match typ:
        case HMType(TypeVar(name=name)):
            return name
        case RType(base=TypeVar(name=name)):
            return name
        case _:
            return None


def free_vars(typ: Type) -> list[str]:
    """
    Returns the free variables of typ.
    """

    match typ:
        case HMType(TypeVar(name=n)):
            return [n]
        case HMType():
            return []
        case RType(base=TypeVar(name=n)):
            return [n]
        case RType():
            return []
        case ArrowType(args=args, ret=ret):
            return sum([free_vars(t) for _, t in args], []) + free_vars(ret)
        case ListType(inner_typ=inner_typ):
            return free_vars(inner_typ)
        case ObjectType(generic_args=args):
            return sum([free_vars(t) for t in args], [])
        case Unknown():
            return []
        case AnyType():
            return []
        case x:
            raise NotImplementedError(x, type(x))


def subst(name: str, typ: Type, constrs: List[BaseEq]) -> List[BaseEq]:
    res = []
    for x in constrs:
        res.append(
            BaseEq(lhs=subst_one(name, typ, x.lhs), rhs=subst_one(name, typ, x.rhs))
        )

    return res


def subst_one(name: str, tar: Type, src: Type) -> Type:
    match src:
        case HMType(TypeVar(name=n)) if name == n:
            return tar
        case RType(base=TypeVar(name=n), predicate=p, pending_subst=ps) if name == n:
            return RType(
                base=unwrap(tar.base_type()), predicate=p, pending_subst=ps
            ).pos(tar)
        case HMType() | RType() | Unknown() | AnyType():
            return src
        case RType():
            return src
        case ArrowType(type_abs=abs, args=args, ret=ret):
            return ArrowType(
                type_abs=abs,
                args=[(x, subst_one(name, tar, t)) for x, t in args],
                ret=subst_one(name, tar, ret),
            ).pos(src)
        case ListType(inner_typ=inner):
            return ListType(subst_one(name, tar, inner)).pos(src)
        case ObjectType(name=obj_name, generic_args=args):
            return ObjectType(obj_name, [subst_one(name, tar, t) for t in args]).pos(
                src
            )
        case x:
            raise NotImplementedError(f"subst one: {x}")


def apply(typ: Type, solution: Solution) -> Type:
    """
    Given a type, resolve all type variables using `solution'.
    """

    match typ:
        case HMType(TypeVar(name=n)) if n in solution:
            return apply(solution[n], solution)
        case RType(base=TypeVar(name=n)) if n in solution:
            ret = apply(solution[n], solution)
            return ret
        case ArrowType(type_abs=abs, args=args, ret=ret):
            return ArrowType(
                type_abs=abs,
                args=[(name, apply(t, solution)) for name, t in args],
                ret=apply(ret, solution),
            )
        case ListType(inner_typ=inner):
            return ListType(inner_typ=apply(inner, solution))
        case ObjectType(name=name, generic_args=args):
            return ObjectType(
                name=name, generic_args=[apply(t, solution) for t in args]
            )
        case _:
            return typ


def apply_context(context: ScopedEnv, solution) -> ScopedEnv:
    """
    Given a type, resolve all type variables using `solution'.
    """

    return context.map(lambda v: apply(v, solution))


def apply_constraints(constrs: List[BaseEq], solution: Solution) -> List[BaseEq]:
    res = []
    for c in constrs:
        res += [BaseEq(apply(c.lhs, solution), apply(c.rhs, solution))]
    return res
