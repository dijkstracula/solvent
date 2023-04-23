"""
The Hindley-Milner type-checker for our little language.
"""

from dataclasses import dataclass
from typing import List

from solvent import syn
from solvent.syn import RType, Type, ArrowType, TypeVar
from solvent import pretty_print as pp


@dataclass
class Constraint:
    pass


@dataclass
class Eq:
    lhs: Type
    rhs: Type


@dataclass
class SubType:
    assumes: List[syn.Expr]
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


def check_stmts(context, assums: List[syn.Expr], stmts: List[syn.Stmt]):
    for stmt in stmts:
        typ, constraints, context = check_stmt(context, assums, stmt)
    return typ, constraints, context


def check_stmt(context, assums: List[syn.Expr], stmt: syn.Stmt):
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
                    t = RType.base(TypeVar.fresh(name=a.name))
                argtypes += [t]
                body_context[a.name] = t

            # we want to add the name of the function currently being defined
            # to the context so that we can define recursive functions.
            # if we don't know the return type before typecehcking, just
            # invent a new type variable.
            if ret is not None:
                ret_typ = ret
            else:
                ret_typ = RType.base(TypeVar.fresh(name="guess"))
                
            body_context[name] = syn.ArrowType(
                args=argtypes,
                ret=ret_typ
            )

            # now typecheck the body
            typ, constrs, context = check_stmts(body_context, assums, body)

            ret_typ_constr = Eq(lhs=ret_typ, rhs=typ)

            this_type = syn.ArrowType(
                args=argtypes,
                ret=typ
            )
            return this_type, constrs + [ret_typ_constr], context

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(context, assums, test)
            body_typ, body_constrs, _ = check_stmts(context, [test] + assums, body)
            else_typ, else_constrs, _ = check_stmts(context, [syn.Neg(test)] + assums, orelse)
            ret_typ = RType.base(TypeVar.fresh("ifRes"))
            cstrs = [
                # test is a boolean
                Eq(test_typ, RType.bool()),
                # base types of branches are equal
                Eq(body_typ, else_typ),
                # body is a subtype of ret type
                SubType([test] + assums, body_typ, ret_typ),  
                # else is a subtype of ret type
                SubType([syn.Neg(test)] + assums, else_typ, ret_typ),  
            ]
            return ret_typ, cstrs + test_constrs + body_constrs + else_constrs, context
        case syn.Return(value=value):
            ty, constrs = check_expr(context, assums, value)
            # for now just throw away the predicate of ty
            nty = RType(value=ty.value, predicate=syn.BoolOp(lhs=syn.V(), op="==", rhs=value))
            return nty, constrs, context
        case x:
            print(x)
            raise NotImplementedError


def check_expr(context, assums, expr: syn.Expr):
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
                Eq(lhs_ty, RType.int()),
                Eq(rhs_ty, RType.int()),
            ])
        case syn.BoolLiteral(_):
            return (RType.bool(), [])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                Eq(lhs_ty, RType.int()),
                Eq(rhs_ty, RType.int()),
            ])
        case syn.Call(function_name=name, arglist=args):
            fn_ty, constrs = check_expr(context, assums, name)
            types = []
            for e in args:
                ty, cs = check_expr(context, assums, e)
                types += [ty]
                constrs += cs
            ret_type = RType.base(TypeVar.fresh())
            return (ret_type, constrs + [
                Eq(lhs=fn_ty, rhs=ArrowType(args=types, ret=ret_type))
            ])
        case x:
            print(x)
            raise NotImplementedError


def base_type_eq(t1: Type, t2: Type) -> bool:
    """
    We can probably override __eq__ at some point. I'm lazy right now.
    This function implements equality between types
    """

    match (t1, t2):
        case (TypeVar(name=n1), TypeVar(name=n2)):
            return n1 == n2
        case (RType(value=v1, predicate=_), RType(value=v2, predicate=_)):
            return v1 == v2
        case (ArrowType(args=args1, ret=ret1), ArrowType(args=args2, ret=ret2)):
            args_eq = all(map(lambda a: base_type_eq(a[0], a[1]), zip(args1, args2)))
            return args_eq and base_type_eq(ret1, ret2)
        case _: 
            return False


def join(t1: Type, t2: Type):
    match (t1, t2):
        case (RType(value=v, predicate=p1), RType(predicate=p2)) if p1 == p2:
            # Temporary
            return [RType.base(v)]
        case _:
            return []


def unify(constrs):
    if len(constrs) == 0:
        return []
    else:
        top = constrs[0]
        rest = constrs[1:]

        lX = tvar_name(top.lhs)
        rX = tvar_name(top.rhs)
        if base_type_eq(top.lhs, top.rhs):
            return unify(rest)  # + join(top.lhs, top.rhs)
        # if lhs is variable
        elif lX is not None and lX not in free_vars(top.rhs):
            return unify(subst(lX, top.rhs, rest)) + [(lX, top.rhs)]
        # if rhs is variable
        elif rX is not None and rX not in free_vars(top.lhs):
            return unify(subst(rX, top.lhs, rest)) + [(rX, top.lhs)]
        # if both are functions variables
        elif (isinstance(top.lhs, ArrowType)
            and isinstance(top.rhs, ArrowType)
            and len(top.lhs.args) == len(top.rhs.args)):
            arg_constrs = list(map(
                lambda a: Eq(lhs=a[0], rhs=a[1]),
                zip(top.lhs.args, top.rhs.args)
            ))
            ret_constr = Eq(lhs=top.lhs.ret, rhs=top.rhs.ret)
            return unify(arg_constrs + [ret_constr] +  rest)
        else:
            print(lX)
            raise Exception(" ".join([
                pp.pstring_type(top.lhs),
                " is incompatible with ",
                pp.pstring_type(top.rhs)
            ]))


def tvar_name(typ: Type):
    match typ:
        case RType(value=TypeVar(name=name)):
            return name


def free_vars(typ: Type):
    match typ:
        case RType(value=TypeVar(name=n)):
            return [n]
        case RType():
            return []
        case ArrowType(args=args, ret=ret):
            return sum([free_vars(a) for a in args], []) + free_vars(ret)
        case x:
            print(x)
            raise NotImplementedError


def subst(name: str, typ: Type, constrs: List[Eq]) -> List[Eq]:
    return [
        Eq(lhs=subst_one(name, typ, x.lhs), rhs=subst_one(name, typ, x.rhs))
        for x in constrs
    ]


def subst_one(name: str, tar: Type, src: Type) -> Type:
    match src:
        case RType(value=TypeVar(name=n)) if name == n:
            return tar
        case RType():
            return src
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[subst_one(name, tar, x) for x in args],
                ret=subst_one(name, tar, ret)
            )
        case x:
            print("subst_one:", x)
            raise NotImplementedError


def finish(typ: Type, solution) -> Type:
    """
    Given a type, resolve all type variables using `solution'.
    """

    match typ:
        case RType(value=TypeVar(name=n), predicate=p) if n in solution:
            base_ty = solution[n].value
            return finish(RType(base_ty, p), solution)
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[finish(t, solution) for t in args],
                ret=finish(ret, solution)
            )
        case x:
            return typ
