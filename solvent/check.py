"""

The Hindley-Milner type-checker for our little language.
"""

from dataclasses import dataclass
from typing import List

from solvent import syn
from solvent.syn import RType, Type, ArrowType



@dataclass
class Constraint:
    lhs: Type
    rhs: Type


def typecheck(stmt: syn.Stmt):
    typ, constrs, _ = check_stmt({}, stmt)
    # TODO: avoid circular import by not pprinting in here (side-effecting stuff
    # like that probably should live in the frontend, anyway)
    #print(pstring_type(typ))
    solution = dict(unify(constrs))
    final = finish(typ, solution)
    print(final)
    #print(pstring_type(final))
    return final


def check_stmts(context, stmts: list[syn.Stmt]):
    for stmt in stmts:
        typ, constraints, context = check_stmt(context, stmt)
    return typ, constraints, context


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
            # TODO: Sammy, decrease my 386L grade if I got this wrong
            # (in particular: fine to discard the context from the body and else  Python
            # has weird not-really-lexical scoping that I don't fully grok?)
            test_typ, test_constrs = check_expr(context, test)
            body_typ, body_constrs, _ = check_stmts(context, body)
            else_typ, else_constrs, _ = check_stmts(context, orelse)
            cstrs = [
                Constraint(test_typ, test_typ.bool()),
                Constraint(body_typ, else_typ),
            ]
            return body_typ, cstrs + test_constrs + body_constrs + else_constrs, context
        case syn.Return(value=value):
            ty, constrs = check_expr(context, value)
            return ty, constrs, context
        case x:
            print(x)
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
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                Constraint(lhs=lhs_ty, rhs=RType.int()),
                Constraint(lhs=rhs_ty, rhs=RType.int()),
            ])
        case syn.BoolOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                Constraint(lhs=lhs_ty, rhs=RType.bool()),
                Constraint(lhs=rhs_ty, rhs=RType.bool()),
            ])
        case syn.Call(function_name=name, arglist=args):
            fn_ty, constrs = check_expr(context, name)
            types = []
            for e in args:
                ty, cs = check_expr(context, e)
                types += [ty]
                constrs += cs
            ret_type = syn.TypeVar.fresh()
            return (ret_type, constrs + [
                Constraint(lhs=fn_ty, rhs=ArrowType(args=types, ret=ret_type))
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
            print(lX)
            raise Exception(f"Can't unify {top.lhs} with {top.rhs}")


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
                return finish(solution[tvar_name(typ)], solution)
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