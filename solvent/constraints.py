"""
Generate constraints for our little subset of Python.

We generate classic equality constraints used for Hindley-Milner,
as well as Sub-type constraints for infering refinement predicates.
"""

from dataclasses import dataclass
from typing import List

from solvent import syn
from solvent.syn import RType, Type, ArrowType, TypeVar, Conjoin


Env = dict[str, Type]


@dataclass
class Constraint:
    def __str__(self):
        match self:
            case BaseEq(lhs=lhs, rhs=rhs):
                return f"{lhs} = {rhs}"
            case SubType(assumes=assumes, lhs=lhs, rhs=rhs):
                asm_str = ", ".join([str(e) for e in assumes])
                return f"{asm_str} |- {lhs} <: {rhs}"


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

    assumes: List[syn.Expr]
    lhs: Type
    rhs: Type


# def typecheck(stmt: syn.Stmt):
#     typ, constrs, _ = check_stmt({}, stmt)
#     # TODO: avoid circular import by not pprinting in here (side-effecting stuff
#     # like that probably should live in the frontend, anyway)
#     #print(pstring_type(typ))
#     solution = dict(unify(constrs))
#     final = finish(typ, solution)
#     print(final)
#     #print(pstring_type(final))
#     return final


def check_stmts(context: Env, assums: List[syn.Expr], stmts: List[syn.Stmt]):
    typ = syn.Unit()
    constraints = []
    for stmt in stmts:
        typ, cs, context = check_stmt(context, assums, stmt)
        constraints += cs
    return typ, constraints, context


def check_stmt(context: Env, assums: List[syn.Expr], stmt: syn.Stmt):
    match stmt:
        case syn.FunctionDef(name=name, args=args, return_annotation=ret, body=body):
            # construct a new context to typecheck our body with
            body_context = context.copy()
            # add the type of arguments to the new context
            argtypes = []
            for a in args:
                if a.annotation is not None:
                    t = a.annotation
                else:
                    t = RType.template(TypeVar.fresh(name=a.name))
                argtypes += [t]
                body_context[a.name] = t

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
            body_context[name] = syn.ArrowType(
                args=argtypes,
                ret=ret_typ
            )

            # now typecheck the body
            inferred_typ, constrs, context = check_stmts(body_context, assums, body)

            ret_typ_constr = [
                BaseEq(lhs=shape_typ(inferred_typ), rhs=shape_typ(ret_typ)),
                SubType([], lhs=inferred_typ, rhs=ret_typ),
            ]

            this_type = syn.ArrowType(
                args=argtypes,
                ret=ret_typ
            )
            return this_type, constrs + ret_typ_constr, context

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(context, assums, test)
            body_typ, body_constrs, _ = check_stmts(context, [test] + assums, body)
            else_typ, else_constrs, _ = check_stmts(context, [syn.Neg(test)] + assums, orelse)
            ret_typ = RType.template(TypeVar.fresh("if"))
            cstrs = [
                # test is a boolean
                BaseEq(test_typ, RType.bool()),
                # base types of branches are equal
                BaseEq(shape_typ(body_typ), shape_typ(else_typ)),
                BaseEq(shape_typ(body_typ), shape_typ(ret_typ)),
                # body is a subtype of ret type
                SubType([test] + assums, body_typ, ret_typ),  
                # else is a subtype of ret type
                SubType([syn.Neg(test)] + assums, else_typ, ret_typ),  
            ]
            return ret_typ, cstrs + test_constrs + body_constrs + else_constrs, context
        case syn.Return(value=value):
            ty, constrs = check_expr(context, assums, value)
            # for now just throw away the predicate of ty
            nty = RType(base=ty.base, predicate=Conjoin([syn.BoolOp(lhs=syn.V(), op="==", rhs=value)]))
            return nty, constrs, context
        case x:
            print(x)
            raise NotImplementedError


def check_expr(context: Env, assums, expr: syn.Expr) -> (Type, List[Constraint]):
    match expr:
        case syn.Variable(name=name):
            if name in context:
                return (context[name], [])
            else:
                raise Exception(f"Variable {name} not bound in context.")
        case syn.IntLiteral(_):
            return (RType.int(), [])
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.int(), lhs_constrs + rhs_constrs + [
                BaseEq(lhs_ty, RType.int()),
                BaseEq(rhs_ty, RType.int()),
            ])
        case syn.BoolLiteral(_):
            return (RType.bool(), [])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                BaseEq(lhs_ty, RType.int()),
                BaseEq(rhs_ty, RType.int()),
            ])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["and", "or", "not"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                BaseEq(lhs_ty, RType.bool()),
                BaseEq(rhs_ty, RType.bool()),
            ])
        case syn.Call(function_name=name, arglist=args):
            fn_ty, constrs = check_expr(context, assums, name)
            types = []
            for e in args:
                ty, cs = check_expr(context, assums, e)
                types += [ty]
                constrs += cs
            ret_type = RType.lift(TypeVar.fresh())
            return (ret_type, constrs + [
                BaseEq(lhs=fn_ty, rhs=ArrowType(args=types, ret=ret_type))
            ])
        case x:
            print(x)
            raise NotImplementedError


def shape_typ(typ: Type) -> Type:
    """
    Implementation of the shape function from the paper.
    Removes a predicate from a RType.
    """

    return RType.lift(typ.base)


def shape_env(env: Env) -> Env:
    return { (k, shape_typ(v)) for k, v in env.items() }


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
            case ArrowType(args=args, ret=ret):
                return ArrowType(
                    args=[lookup(a, solution) for a in args],
                    ret=lookup(ret, solution)
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
