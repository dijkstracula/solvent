"""
The Hindley-Milner type-checker for our little language.
"""

from dataclasses import dataclass

from solvent import syn
from solvent.syn import RType
from solvent.pretty_print import pretty_print, pstring_type


@dataclass
class Constraint:
    lhs: RType
    rhs: RType


def typecheck(stmt: syn.Stmt):
    typ, constrs, _ = check_stmt({}, stmt)
    print(pstring_type(typ))
    for c in constrs:
        print(f"{pstring_type(c.lhs)} = {pstring_type(c.rhs)}")


def check_stmt(context, stmt: syn.Stmt):
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
                    t = RType.base(syn.TypeVar.fresh())
                argtypes += [t]
                body_context[a.name] = t

            # now typecheck the body
            last_type = syn.Unit()
            new_constraints = []
            for s in body:
                last_type, constrs, body_context = check_stmt(body_context, s)
                new_constraints += constrs

            this_type = syn.ArrowType(
                args=argtypes,
                ret=last_type
            )
            return this_type, new_constraints, context

        case syn.If(test=test, body=body, orelse=orelse):
            raise NotImplementedError
        case syn.Return(value=value):
            ty, constrs = check_expr(context, value)
            return ty, constrs, context
        case _:
            raise NotImplementedError


def check_expr(context, expr: syn.Expr):
    match expr:
        case syn.Variable(name=name):
            if name in context:
                return (context[name], [])
            else:
                raise Exception(f"Variable {name} not bound in context.")
        case syn.IntLiteral(_):
            return (RType.int(), [])
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            return (RType.int(), lhs_constrs + rhs_constrs + [
                Constraint(lhs=lhs_ty, rhs=RType.int()),
                Constraint(lhs=rhs_ty, rhs=RType.int()),
            ])
        case syn.BoolLiteral(_):
            return (RType.bool(), [])
        case syn.BoolOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                Constraint(lhs=lhs_ty, rhs=RType.bool()),
                Constraint(lhs=rhs_ty, rhs=RType.bool()),
            ])
        case x:
            print(x)
            raise NotImplementedError
