"""
Generate constraints for our little subset of Python.

We generate classic equality constraints used for Hindley-Milner,
as well as Sub-type constraints for infering refinement predicates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from solvent import errors
from solvent import syntax as syn
from solvent.env import Env
from solvent.syntax import ArrowType, Conjoin, RType, Type, TypeVar


class Constraint(syn.Pos):
    def __str__(self):
        match self:
            case SubType(context=ctx, assumes=assumes, lhs=lhs, rhs=rhs):
                asm_str = ", ".join([str(e) for e in assumes])
                return f"[{asm_str}] |- {lhs} <: {rhs} ({self.position})"
            case Scope(context=ctx, typ=typ):
                asm_str = ", ".join([f"{k}: {v}" for k, v in ctx.items])
                return f"[{asm_str}] |- {typ}"


@dataclass
class SubType(Constraint):
    """
    Represents a subtype constraint between two types with a context of `assumes'
    """

    context: Env
    assumes: List[syn.Expr]
    lhs: Type
    rhs: Type


@dataclass
class Scope(Constraint):
    """
    Represents the context of an expression
    """

    context: Env
    typ: Type


def check_stmts(
    context: Env, assums: List[syn.Expr], stmts: List[syn.Stmt]
) -> tuple[syn.Type, List[Constraint], Env]:
    typ = syn.RType.lift(syn.Unit())
    constraints = []
    for stmt in stmts:
        typ, cs, context = check_stmt(context, assums, stmt)
        constraints += cs
    return typ, constraints, context


def check_stmt(
    context: Env, assums: List[syn.Expr], stmt: syn.Stmt
) -> tuple[syn.Type, List[Constraint], Env]:
    match stmt:
        case syn.FunctionDef(name=name, body=body, typ=ArrowType(args=args, ret=ret)):
            # construct a new context to typecheck our body with
            body_context = context

            # add the type of arguments to the new context
            for name, t in args:
                body_context = body_context.add(name, t)

            # add the function that we are currently defining to our
            # context, so that we can support recursive uses
            this_type = syn.ArrowType(args, ret)
            body_context = body_context.add(name, this_type)

            # scope constraints
            scope_constr = [
                *[Scope(context, t) for _, t in args],
                Scope(body_context, ret),
            ]

            # now typecheck the body
            body_type, body_constrs, body_context = check_stmts(
                body_context, assums, body
            )

            ret_typ_constr = [
                SubType(body_context, assums, body_type, ret).pos(body_type),
            ]

            return (
                this_type,
                body_constrs + ret_typ_constr + scope_constr,
                context.add(name, this_type),
            )

        case syn.If(test=test, body=body, orelse=orelse, typ=if_typ):
            assert if_typ is not None

            _, test_constrs = check_expr(context, assums, test)
            body_typ, body_constrs, body_ctx = check_stmts(
                context, [test] + assums, body
            )
            else_typ, else_constrs, else_ctx = check_stmts(
                context, [syn.Neg(test)] + assums, orelse
            )
            cstrs = [
                # body is a subtype of ret type
                SubType(body_ctx, [test] + assums, body_typ, if_typ).pos(body_typ),
                # else is a subtype of ret type
                SubType(else_ctx, [syn.Neg(test)] + assums, else_typ, if_typ).pos(
                    else_typ
                ),
                Scope(context, if_typ),
            ]
            return (
                if_typ.pos(stmt),
                cstrs + test_constrs + body_constrs + else_constrs,
                context,
            )
        case syn.Assign(name=id, value=e):
            e_typ, e_constrs = check_expr(context, assums, e)
            return e_typ, e_constrs, context.add(id, e_typ)
        case syn.Return(value=value):
            ty, constrs = check_expr(context, assums, value)
            # for now just throw away the predicate of ty
            nty = ty.set_predicate(
                Conjoin([syn.BoolOp(lhs=syn.V(), op="==", rhs=value)])
            )
            return nty.pos(stmt), constrs, context
        case x:
            print(x)
            raise NotImplementedError


def check_expr(context: Env, assums, expr: syn.Expr) -> tuple[Type, List[Constraint]]:
    match expr:
        case syn.Variable(typ=typ):
            assert typ is not None
            return (typ, [])
        case syn.IntLiteral():
            typ = RType(syn.Int(), syn.Conjoin([syn.BoolOp(syn.V(), "==", expr)])).pos(
                expr
            )
            return (typ, [])
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            _, lhs_constrs = check_expr(context, assums, lhs)
            _, rhs_constrs = check_expr(context, assums, rhs)
            ret_ty = RType(syn.Int(), Conjoin([syn.BoolOp(syn.V(), "==", expr)])).pos(
                expr
            )
            return (
                ret_ty,
                lhs_constrs + rhs_constrs + [Scope(context, ret_ty).pos(ret_ty)],
            )
        case syn.BoolLiteral(_):
            return (RType.bool().pos(expr), [])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            _, lhs_constrs = check_expr(context, assums, lhs)
            _, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool().pos(expr), lhs_constrs + rhs_constrs)
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["and", "or", "not"]:
            _, lhs_constrs = check_expr(context, assums, lhs)
            _, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool().pos(expr), lhs_constrs + rhs_constrs)
        case syn.Call(function_name=fn, arglist=args):
            fn_ty, constrs = check_expr(context, assums, fn)
            subst = []
            types = []

            match fn_ty:
                # if we know that we have a function type,
                # we can generate subtyping relations
                case ArrowType(args=fn_arg_typs, ret=fn_ret_type) if len(
                    fn_arg_typs
                ) == len(args):
                    for (x1, arg_ty), e in zip(fn_arg_typs, args):
                        expr_ty, cs = check_expr(context, assums, e)
                        types += [(x1, expr_ty)]
                        constrs += cs + [
                            SubType(context, assums, expr_ty, arg_ty).pos(expr_ty),
                        ]
                        subst += [(x1, e)]
                    ret_type = fn_ret_type
                case x:
                    raise errors.Unreachable(x)
            return (ret_type.subst(subst).pos(expr), constrs)
        case x:
            print(x)
            raise NotImplementedError


def shape_typ(typ: Type) -> Type:
    """
    Implementation of the shape function from the paper.
    Removes a predicate from a RType.
    """

    match typ:
        case ArrowType(args=args, ret=ret, pending_subst=ps):
            return ArrowType(
                args=[(name, shape_typ(a)) for name, a in args],
                ret=shape_typ(ret),
                pending_subst=ps,
            ).pos(typ)
        case RType(base=base):
            return RType.lift(base).pos(typ)
        case x:
            raise Exception(f"`{x}` is not a Type.")


def shape_env(env: Env) -> Env:
    return env.map(shape_typ)


# don't actually need this
def shrink(solution):
    """
    Returns a solution where every entry maps to something that isn't
    in the solution.

    For example:
      3 := '4
      4 := '5
    Get's turned into:
      3 := '5
      4 := '5

    I'm doing the dumbest thing right now. This can definitely be improved.
    """

    def lookup(typ: Type, solution) -> Type:
        """For composite types, I need to potentially dig into the type."""
        match typ:
            case TypeVar(name=n):
                if n in solution:
                    return solution[n]
                else:
                    return typ
            case ArrowType(args=args, ret=ret, pending_subst=ps):
                return ArrowType(
                    args=[(name, lookup(a, solution)) for name, a in args],
                    ret=lookup(ret, solution),
                    pending_subst=ps,
                )
            case x:
                return x

    new_solution = solution.copy()
    for k, v in solution.items():
        new_solution[k] = lookup(v, solution)
    if new_solution == solution:
        return new_solution
    else:
        return shrink(new_solution)
