from dataclasses import dataclass
from typing import List

from solvent import syntax as syn
from solvent.env import Env
from solvent.syntax import ArrowType, HMType, Type, TypeVar


@dataclass
class BaseEq(syn.Pos):
    """
    Represents an equality constraint between the base types of two types
    """

    lhs: Type
    rhs: Type

    def __str__(self):
        return f"{self.lhs} == {self.rhs}"


def check_stmts(
    context: Env, stmts: List[syn.Stmt]
) -> tuple[syn.Type, List[BaseEq], Env]:
    typ = HMType(syn.Unit())
    constraints = []
    for stmt in stmts:
        typ, cs, context = check_stmt(context, stmt)
        constraints += cs
    return typ, constraints, context


def check_stmt(context: Env, stmt: syn.Stmt) -> tuple[syn.Type, List[BaseEq], Env]:
    ret_type: syn.Type
    ret_constrs: List[BaseEq]
    ret_context: Env

    match stmt:
        case syn.FunctionDef(name=name, args=args, return_annotation=ret, body=body):
            # construct a new context to typecheck our body with
            body_context = context
            # add the type of arguments to the new context
            argtypes: List[tuple[str, Type]] = []
            for a in args:
                if isinstance(a.annotation, syn.RType):
                    t = HMType(a.annotation.base)
                else:
                    t = HMType.fresh(name=a.name)
                argtypes += [(a.name, t)]
                body_context = body_context.add(a.name, t)

            # we want to add the name of the function currently being defined
            # to the context so that we can define recursive functions.
            # if we don't know the return type before typecehcking, just
            # invent a new type variable.
            if ret is not None:
                ret_typ = ret
            else:
                ret_typ = HMType.fresh(name="ret")
            ret_typ.pos(stmt)

            # add the function that we are currently defining to our
            # context, so that we can support recursive uses
            this_type = syn.ArrowType(argtypes, ret_typ).pos(stmt)
            body_context = body_context.add(name, this_type)

            # now typecheck the body
            inferred_typ, constrs, body_context = check_stmts(body_context, body)

            ret_typ_constr = [
                BaseEq(lhs=inferred_typ, rhs=ret_typ).pos(inferred_typ),
            ]

            ret_type = this_type
            ret_constrs = constrs + ret_typ_constr
            ret_context = context.add(name, this_type)

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(context, test)
            body_typ, body_constrs, _ = check_stmts(context, body)
            else_typ, else_constrs, _ = check_stmts(context, orelse)
            ret_typ = HMType(TypeVar.fresh("if")).pos(stmt)
            cstrs = [
                # test is a boolean
                BaseEq(test_typ, HMType.bool()),
                # base types of branches are equal
                BaseEq(body_typ, ret_typ),
                BaseEq(body_typ, else_typ),
            ]
            ret_type = ret_typ.pos(stmt)
            ret_constrs = cstrs + test_constrs + body_constrs + else_constrs
            ret_context = context

        case syn.Assign(name=id, value=e):
            ret_type, ret_constrs = check_expr(context, e)
            ret_context = context.add(id, ret_type)
        case syn.Return(value=value):
            ret_type, ret_constrs = check_expr(context, value)
            ret_context = context
        case x:
            print(x)
            raise NotImplementedError
    stmt.annot(ret_type)
    return ret_type.pos(stmt), ret_constrs, ret_context


def check_expr(context: Env, expr: syn.Expr) -> tuple[Type, List[BaseEq]]:
    ret_typ = None
    ret_constrs: List[BaseEq] = []
    match expr:
        case syn.Variable(name=name):
            if name in context:
                ret_typ = context[name]
            else:
                raise Exception(f"Variable {name} not bound in context.")
        case syn.IntLiteral():
            ret_typ = HMType.int()
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            ret_typ = HMType.int()
            ret_constrs = (
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(lhs_ty, HMType.int()).pos(lhs_ty),
                    BaseEq(rhs_ty, HMType.int()).pos(rhs_ty),
                ]
            )
        case syn.BoolLiteral(_):
            ret_typ = HMType.bool()
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            ret_typ = HMType.bool()
            ret_constrs = (
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(lhs_ty, HMType.int()).pos(lhs_ty),
                    BaseEq(rhs_ty, HMType.int()).pos(rhs_ty),
                ]
            )
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["and", "or", "not"]:
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            ret_typ = HMType.bool()
            ret_constrs = (
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(lhs_ty, HMType.bool()).pos(lhs_ty),
                    BaseEq(rhs_ty, HMType.bool()).pos(rhs_ty),
                ]
            )
        case syn.Call(function_name=fn, arglist=args):
            fn_ty, constrs = check_expr(context, fn)
            types = []

            for e in args:
                ty, cs = check_expr(context, e)
                types += [(syn.NameGenerator.fresh("arg"), ty)]
                constrs += cs

            ret_typ = HMType.fresh("f")
            constrs += [BaseEq(fn_ty, ArrowType(types, ret_typ))]
            ret_constrs = constrs
        case x:
            print(x)
            raise NotImplementedError
    expr.annot(ret_typ)
    return ret_typ.pos(expr), ret_constrs
