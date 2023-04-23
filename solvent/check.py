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

            # now typecheck the body
            last_type = RType.base(syn.Unit())
            new_constraints = []
            for s in body:
                last_type, constrs, body_context = check_stmt(body_context, assums, s)
                # for c in constrs:
                #     print(pp.pstring_cvar(c))
                new_constraints += constrs

            if ret is not None:
                last_type = ret

            this_type = syn.ArrowType(
                args=argtypes,
                ret=last_type
            )
            return this_type, new_constraints, context

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(context, assums, test)
            body_typ, body_constrs, _ = check_stmts(context, [test] + assums, body)
            else_typ, else_constrs, _ = check_stmts(context, [syn.Neg(test)] + assums, orelse)
            ret_typ = TypeVar.fresh("ifRes")
            cstrs = [
                Eq(test_typ, RType.bool()),  # test is a boolean
                SubType(body_typ, RType.base(ret_typ)),  # body is a subtype of ret type
                SubType(else_typ, RType.base(ret_typ)),  # else is a subtype of ret type
            ]
            return RType.base(ret_typ), cstrs + test_constrs + body_constrs + else_constrs, context
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
            lhs_ty, lhs_constrs = check_expr(context, lhs)
            rhs_ty, rhs_constrs = check_expr(context, rhs)
            return (RType.int(), lhs_constrs + rhs_constrs + [
                SubType(lhs=lhs_ty, rhs=RType.int()),
                SubType(lhs=rhs_ty, rhs=RType.int()),
            ])
        case syn.BoolLiteral(_):
            return (RType.bool(), [])
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(context, assums, lhs)
            rhs_ty, rhs_constrs = check_expr(context, assums, rhs)
            return (RType.bool(), lhs_constrs + rhs_constrs + [
                SubType(lhs=lhs_ty, rhs=RType.int()),
                SubType(lhs=rhs_ty, rhs=RType.int()),
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
            raise Exception(f"Can't unify {top.lhs} with {top.rhs}")


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


# don't actually need this
# def shrink(solution):
#     """
#     Returns a solution where every entry maps to something that isn't
#     in the solution.

#     For example:
#       3 := '4
#       4 := '5
#     Get's turned into:
#       3 := '5
#       4 := '5

#     I'm doing the dumbest thing right now. This can definitely be improved.
#     """

#     def lookup(typ: Type, solution) -> Type:
#         """For composite types, I need to potentially dig into the type."""
#         match typ:
#             case TypeVar(name=n):
#                 if n in solution:
#                     return solution[n]
#                 else:
#                     return typ
#             case ArrowType(args=args, ret=ret):
#                 return ArrowType(
#                     args=[lookup(a, solution) for a in args],
#                     ret=lookup(ret, solution)
#                 )
#             case x:
#                 return x

#     new_solution = solution.copy()
#     for k, v in solution.items():
#         new_solution[k] = lookup(v, solution)
#     if new_solution == solution:
#         return new_solution
#     else:
#         return shrink(new_solution)



def finish(typ: Type, solution) -> Type:
    """
    Given a type, resolve all type variables using `solution'.
    """

    match typ:
        case RType(value=TypeVar(name=n)) if n in solution:
            return finish(solution[n], solution)
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                args=[finish(t, solution) for t in args],
                ret=finish(ret, solution)
            )
        case x:
            return typ
