"""
Generate constraints for our little subset of Python.

We generate classic equality constraints used for Hindley-Milner,
as well as Sub-type constraints for infering refinement predicates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from solvent import syntax as syn
from solvent.syntax import ArrowType, Conjoin, RType, Type, TypeVar


@dataclass(frozen=True)
class Env:
    items: List[tuple[str, Type]]

    @staticmethod
    def empty():
        return Env([])

    def add(self, name: str, typ: Type) -> "Env":
        return Env([(name, typ)] + self.items)

    def map(self, fn):
        return Env([(k, fn(v)) for k, v in self.items])

    def __getitem__(self, name):
        for n, t in self.items:
            if name == n:
                return t
        raise IndexError(f"{name} not bound in context")

    def __contains__(self, name):
        return name in [x for x, _ in self.items]

    def __str__(self):
        return "{" + ", ".join([f"{x}: {t}" for x, t in self.items]) + "}"


class Constraint(syn.Pos):
    def __str__(self):
        match self:
            case BaseEq(lhs=lhs, rhs=rhs, position=p):
                return f"{lhs} = {rhs} ({p})"
            case SubType(context=ctx, assumes=assumes, lhs=lhs, rhs=rhs):
                # ctx_str = ", ".join([f"{x}:{t}" for x, t in ctx.items])
                asm_str = ", ".join([str(e) for e in assumes])
                return f"[{asm_str}] |- {lhs} <: {rhs}"
            case Scope(context=ctx, typ=typ):
                asm_str = ", ".join([f"{k}: {v}" for k, v in ctx.items])
                return f"[{asm_str}] |- {typ}"


@dataclass
class BaseEq(Constraint):
    """
    Represents an equality constraint between the base types of two types
    """

    lhs: Type
    rhs: Type


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
        case syn.FunctionDef(name=name, args=args, return_annotation=ret, body=body):
            # construct a new context to typecheck our body with
            body_context = context
            # add the type of arguments to the new context
            argtypes: List[tuple[str, Type]] = []
            for a in args:
                if a.annotation is not None:
                    t = a.annotation
                else:
                    t = RType.template(TypeVar.fresh(name=a.name))
                argtypes += [(a.name, t)]
                body_context = body_context.add(a.name, t)

            # we want to add the name of the function currently being defined
            # to the context so that we can define recursive functions.
            # if we don't know the return type before typecehcking, just
            # invent a new type variable.
            if ret is not None:
                ret_typ = ret
            else:
                ret_typ = RType.template(TypeVar.fresh(name="ret"))

            # add the function that we are currently defining to our
            # context, so that we can support recursive uses
            body_context = body_context.add(name, syn.ArrowType(argtypes, ret_typ))

            # scope constraints
            scope_constr = [
                *[Scope(context, t) for _, t in argtypes],
                Scope(body_context, ret_typ),
            ]

            # now typecheck the body
            inferred_typ, constrs, context = check_stmts(body_context, assums, body)

            ret_typ_constr = [
                BaseEq(lhs=shape_typ(inferred_typ), rhs=shape_typ(ret_typ)).pos(
                    inferred_typ
                ),
                SubType(context, [], inferred_typ, ret_typ),
            ]

            this_type = syn.ArrowType(argtypes, ret_typ)
            return this_type, constrs + ret_typ_constr + scope_constr, context

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(context, assums, test)
            body_typ, body_constrs, body_ctx = check_stmts(
                context, [test] + assums, body
            )
            else_typ, else_constrs, else_ctx = check_stmts(
                context, [syn.Neg(test)] + assums, orelse
            )
            ret_typ = RType.template(TypeVar.fresh("if"))
            cstrs = [
                # test is a boolean
                BaseEq(shape_typ(test_typ), RType.bool()),
                # base types of branches are equal
                BaseEq(shape_typ(body_typ), shape_typ(else_typ)),
                BaseEq(shape_typ(body_typ), shape_typ(ret_typ)),
                # body is a subtype of ret type
                SubType(body_ctx, [test] + assums, body_typ, ret_typ),
                # else is a subtype of ret type
                SubType(else_ctx, [syn.Neg(test)] + assums, else_typ, ret_typ),
                Scope(context, ret_typ),
            ]
            return ret_typ, cstrs + test_constrs + body_constrs + else_constrs, context
        case syn.Assign(name=id, value=e):
            e_typ, e_constrs = check_expr(context, assums, e)
            return e_typ, e_constrs, context.add(id, e_typ)
        case syn.Return(value=value):
            ty, constrs = check_expr(context, assums, value)
            # for now just throw away the predicate of ty
            nty = ty.set_predicate(
                Conjoin([syn.BoolOp(lhs=syn.V(), op="==", rhs=value)])
            )
            return nty, constrs, context
        case x:
            print(x)
            raise NotImplementedError


def check_expr(context: Env, assums, expr: syn.Expr) -> tuple[Type, List[Constraint]]:
    match expr:
        case syn.Variable(name=name):
            if name in context:
                return (context[name].pos(expr), [])
            else:
                raise Exception(f"Variable {name} not bound in context.")
        case syn.IntLiteral(_):
            return (RType.int().pos(expr), [])
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (
                RType.int().pos(expr),
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(shape_typ(lhs_ty), RType.int()).pos(lhs_ty),
                    BaseEq(shape_typ(rhs_ty), RType.int()).pos(rhs_ty),
                ],
            )
        case syn.BoolLiteral(_):
            return (RType.bool().pos(expr), [])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (
                RType.bool(),
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(shape_typ(lhs_ty), RType.int()).pos(lhs_ty),
                    BaseEq(shape_typ(rhs_ty), RType.int()).pos(rhs_ty),
                ],
            )
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["and", "or", "not"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (
                RType.bool(),
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(shape_typ(lhs_ty), RType.bool()).pos(lhs_ty),
                    BaseEq(shape_typ(rhs_ty), RType.bool()).pos(rhs_ty),
                ],
            )
        case syn.Call(function_name=fn, arglist=args):
            # TODO, subst args into fn_typ
            fn_ty, constrs = check_expr(context, assums, fn)
            subst = []
            types = []

            match fn_ty:
                # if we know that we have a function type,
                # we can generate subtyping relations
                case ArrowType(args=fn_arg_typs, ret=fn_ret_type) if len(
                    fn_arg_typs
                ) == len(args):
                    for (x1, t1), e in zip(fn_arg_typs, args):
                        ty, cs = check_expr(context, assums, e)
                        types += [(x1, ty)]
                        constrs += cs + [SubType(context, assums, t1, ty)]
                        subst += [(x1, e)]
                    ret_type = fn_ret_type
                case x:
                    for e in args:
                        ty, cs = check_expr(context, assums, e)
                        types += [(syn.NameGenerator.fresh("arg"), ty)]
                        constrs += cs

                    ret_type = RType.lift(TypeVar.fresh())
                    constrs += [BaseEq(fn_ty, ArrowType(types, ret_type))]
            return (ret_type.subst(subst), constrs)
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
