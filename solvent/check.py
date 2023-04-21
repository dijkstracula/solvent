"""
The Hindley-Milner type-checker for our little language.
"""

from dataclasses import dataclass
from typing import List

from solvent import syn
from solvent.syn import RType, Type, ArrowType
from solvent.pretty_print import pretty_print, pstring_type


@dataclass
class Constraint:
    lhs: Type
    rhs: Type


def typecheck(stmt: syn.Stmt):
    typ, constrs, _ = check_stmt({}, stmt)
    print(pstring_type(typ))
    for c in constrs:
        print(f"{pstring_type(c.lhs)} = {pstring_type(c.rhs)}")
    solution = dict(unify(constrs))
    final = finish(typ, solution)
    print(final)
    print(pstring_type(final))
    return final


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


def unify(constrs):
    if len(constrs) == 0:
        return []
    else:
        top = constrs[0]
        rest = constrs[1:]
        lX = tvar_name(top.lhs)
        rX = tvar_name(top.rhs)
        if top.lhs.value == top.rhs.value:
            return unify(constrs[1:])
        # if lhs is variable
        elif lX is not None and lX not in free_vars(top.rhs):
            return unify(subst(lX, top.rhs, rest)) + [(lX, top.rhs)]
        # if rhs is variable
        elif rX is not None and rX not in free_vars(top.lhs):
            return unify(subst(rX, top.lhs, rest)) + [(rX, top.lhs)]
        # if both are functions variables
        else:
            print(top)
            print(lX)
            raise NotImplementedError


def tvar_name(typ: Type):
    match typ:
        case RType(value=syn.TypeVar(name=name)):
            return name


def free_vars(typ: Type):
    match typ:
        case RType(value=syn.TypeVar(name=name)):
            return [name]
        case RType():
            return []
        case ArrowType(args=args, ret=ret):
            return free_vars(args) + free_vars(ret)
        case _:
            return NotImplementedError


def subst(name: str, typ: Type, constrs: List[Constraint]) -> List[Constraint]:
    return [
        Constraint(lhs=subst_one(name, typ, x.lhs), rhs=subst_one(name, typ, x.rhs))
        for x in constrs
    ]


def subst_one(name: str, tar: Type, src: Type) -> Type:
    match src:
        case RType(value=value):
            if tvar_name(src) == name:
                return tar
            else:
                return src
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[subst_one(name, tar, x) for x in args],
                ret=[subst_one(name, tar, ret)]
            )


def finish(typ: Type, solution) -> Type:
    match typ:
        case RType():
            if tvar_name(typ) in solution:
                return solution[tvar_name(typ)]
            else:
                return typ
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[finish(t, solution) for t in args],
                ret=finish(ret, solution)
            )
        case x:
            print(x)
            raise NotImplementedError
