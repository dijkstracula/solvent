from dataclasses import dataclass
from typing import Dict, List

from solvent import errors
from solvent import syntax as syn
from solvent import utils
from solvent.env import ScopedEnv
from solvent.position import Context
from solvent.syntax import (
    ArrowType,
    Call,
    DictType,
    Expr,
    FunctionDef,
    HMType,
    If,
    ListType,
    Return,
    Type,
    TypeVar,
    base_type_eq,
)
from solvent.visitor import Visitor


@dataclass
class BaseEq(syn.Pos):
    """
    Represents an equality constraint between the base types of two types
    """

    lhs: Type
    rhs: Type

    def __post_init__(self):
        self.call_site = utils.debuginfo()

    def __str__(self):
        return (
            f"{self.lhs} == {self.rhs} "
            + f"({Context.single(at=self.position, color=True)})"
        )


class HindleyMilner(Visitor):
    def start(self, types: Dict[int, Type], env: ScopedEnv):
        self.constrs: List[BaseEq] = []
        self.types = types
        self.env = env.clone()
        self.current_function_ret: Type | None = None

    def start_FunctionDef(self, fd: FunctionDef):
        fd_typ = self.types[fd.node_id]
        assert isinstance(fd_typ, ArrowType)

        # add the type of function arguments to a new context
        self.env.push_scope_mut()
        for name, ty in fd_typ.args:
            self.env[name] = ty

        # add the function that we are currently defining to our
        # context, so that we can support recursive uses
        self.env[fd.name] = fd_typ

        self.current_function_ret = fd_typ.ret

    def start_Return(self, ret: Return):
        # TODO: handle the case where a function doesn't return anything
        assert self.current_function_ret is not None

        self.constrs += [
            BaseEq(
                lhs=self.current_function_ret, rhs=self.types[ret.value.node_id]
            ).pos(ret)
        ]

    def end_FunctionDef(self, _: FunctionDef):
        self.env.pop_scope_mut()
        self.current_function_ret = None

    def end_If(self, if_stmt: If):
        test_typ = self.types[if_stmt.test.node_id]
        self.constrs += [BaseEq(test_typ, HMType.bool()).pos(if_stmt.test)]

    def end_Call(self, op: Call) -> Expr:
        fn_typ = self.types[op.function_name.node_id]
        assert isinstance(fn_typ, ArrowType)

        for (_, fn_arg), op_arg in zip(fn_typ.args, op.arglist):
            self.constrs += [BaseEq(fn_arg, self.types[op_arg.node_id]).pos(op)]

        return op

    # def end_ArithBinOp(self, abo: ArithBinOp):
    #     if not isinstance(self.types[abo.node_id].base_type(), TypeVar):
    #         return

    #     match abo.op:
    #         case "+" | "*" | "/" | "-":
    #             self.constrs += [
    #                 BaseEq(self.types[abo.lhs.node_id], HMType.int()).pos(abo),
    #                 BaseEq(self.types[abo.rhs.node_id], HMType.int()).pos(abo),
    #                 BaseEq(self.types[abo.node_id], HMType.int()).pos(abo),
    #             ]
    #         case x:
    #             raise NotImplementedError(x)

    # def end_BoolOp(self, op: BoolOp):
    #     if not isinstance(self.types[op.node_id].base_type(), TypeVar):
    #         return

    #     match op.op:
    #         case "<" | "<=" | "==" | ">=" | ">":
    #             self.constrs += [
    #                 BaseEq(self.types[op.lhs.node_id], HMType.int()).pos(op),
    #                 BaseEq(self.types[op.rhs.node_id], HMType.int()).pos(op),
    #                 BaseEq(self.types[op.node_id], HMType.bool()).pos(op),
    #             ]
    #         case "and" | "or":
    #             self.constrs += [
    #                 BaseEq(self.types[op.lhs.node_id], HMType.bool()).pos(op),
    #                 BaseEq(self.types[op.rhs.node_id], HMType.bool()).pos(op),
    #                 BaseEq(self.types[op.node_id], HMType.bool()).pos(op),
    #             ]
    #         case x:
    #             raise NotImplementedError(x)


def check_stmts(
    types: Dict[int, Type], context: ScopedEnv, stmts: List[syn.Stmt]
) -> tuple[syn.Type, List[BaseEq], ScopedEnv]:
    typ = HMType(syn.Unit())
    constraints = []
    for stmt in stmts:
        typ, cs, context = check_stmt(types, context, stmt)
        constraints += cs
    return typ, constraints, context


def check_stmt(
    types: Dict[int, Type], context: ScopedEnv, stmt: syn.Stmt
) -> tuple[syn.Type, List[BaseEq], ScopedEnv]:
    ret_type: syn.Type
    ret_constrs: List[BaseEq]
    ret_context: ScopedEnv

    match stmt:
        case syn.FunctionDef(name=name, args=args, return_annotation=ret, body=body):
            ret_context = context.push_scope()
            # add the type of arguments to the new context
            argtypes: List[tuple[str, Type]] = []
            for a in args:
                if isinstance(a.annotation, syn.RType):
                    t = HMType(a.annotation.base)
                else:
                    t = HMType.fresh(name=a.name)
                argtypes += [(a.name, t)]
                ret_context = ret_context.add(a.name, t)

            # we want to add the name of the function currently being defined
            # to the context so that we can define recursive functions.
            # if we don't know the return type before typecehcking, just
            # invent a new type variable.
            if ret is not None:
                ret_typ = ret
            else:
                ret_typ = HMType.fresh(name="t").pos(stmt)

            # add the function that we are currently defining to our
            # context, so that we can support recursive uses
            this_type = syn.ArrowType({}, argtypes, ret_typ).pos(stmt)
            ret_context = ret_context.add(name, this_type)

            # now typecheck the body
            inferred_typ, constrs, ret_context = check_stmts(types, ret_context, body)

            ret_typ_constr = [
                BaseEq(lhs=inferred_typ, rhs=ret_typ).pos(inferred_typ),
            ]

            # remove the scope that we check the body with
            ret_context = ret_context.pop_scope()

            ret_type = this_type
            ret_constrs = constrs + ret_typ_constr
            ret_context = ret_context.add(name, this_type)

        case syn.If(test=test, body=body, orelse=orelse):
            test_typ, test_constrs = check_expr(types, context, test)
            body_typ, body_constrs, _ = check_stmts(types, context, body)
            else_typ, else_constrs, _ = check_stmts(types, context, orelse)
            ret_typ = HMType(TypeVar.fresh("if")).pos(stmt)
            cstrs = [
                # test is a boolean
                BaseEq(test_typ, HMType.bool()).pos(test_typ),
                # base types of branches are equal
                BaseEq(body_typ, ret_typ).pos(ret_typ),
                BaseEq(body_typ, else_typ).pos(else_typ),
            ]
            ret_type = ret_typ.pos(stmt)
            ret_constrs = cstrs + test_constrs + body_constrs + else_constrs
            ret_context = context

        case syn.Assign(name=id, value=e):
            ret_type, ret_constrs = check_expr(types, context, e)
            ret_context = context.add(id, ret_type)
        case syn.Return(value=value):
            ret_type, ret_constrs = check_expr(types, context, value)
            ret_context = context
        case x:
            raise NotImplementedError(x)
    # stmt.annot(ret_type)
    return ret_type.pos(stmt), ret_constrs, ret_context


def check_expr(
    types: Dict[int, Type], context: ScopedEnv, expr: syn.Expr
) -> tuple[Type, List[BaseEq]]:
    ret_typ = None
    ret_constrs: List[BaseEq] = []
    match expr:
        case syn.Variable(name=name):
            if name in context:
                ret_typ = context[name]
            else:
                raise errors.UnboundVariable(expr)
        case syn.IntLiteral():
            ret_typ = HMType.int()
        case syn.Neg(expr=e):
            e_ty, e_constrs = check_expr(types, context, e)
            ret_typ = HMType.int()
            ret_constrs = e_constrs + [BaseEq(e_ty, HMType.int()).pos(expr)]
        case syn.ArithBinOp(lhs=lhs, rhs=rhs, op="+"):
            # give `+` the type `'a -> 'a -> 'a`
            lhs_ty, lhs_constrs = check_expr(types, context, lhs)
            rhs_ty, rhs_constrs = check_expr(types, context, rhs)
            ret_typ = HMType.fresh()
            ret_constrs = (
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(lhs_ty, ret_typ).pos(lhs_ty),
                    BaseEq(rhs_ty, ret_typ).pos(rhs_ty),
                ]
            )
        case syn.ArithBinOp(lhs=lhs, rhs=rhs, op="/"):
            # give `/` the type `'a -> int -> 'a`
            lhs_ty, lhs_constrs = check_expr(types, context, lhs)
            rhs_ty, rhs_constrs = check_expr(types, context, rhs)
            ret_typ = HMType.fresh("div")
            ret_constrs = (
                lhs_constrs
                + rhs_constrs
                + [
                    BaseEq(lhs_ty, ret_typ).pos(lhs_ty),
                    BaseEq(rhs_ty, HMType.int()).pos(rhs_ty),
                ]
            )
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            lhs_ty, lhs_constrs = check_expr(types, context, lhs)
            rhs_ty, rhs_constrs = check_expr(types, context, rhs)
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
        case syn.ListLiteral(elts=[]):
            inner_ty = HMType.fresh("lst").pos(expr)
            ret_typ = ListType(inner_ty)
        case syn.StrLiteral():
            ret_typ = HMType.str()
        case syn.ListLiteral(elts=elts):
            elts_typs = [check_expr(types, context, e) for e in elts]
            assert elts_typs != []
            inner_ty: Type = elts_typs[0][0]

            # check that all list types are of inner type
            # add all constrs to the ret_constrs
            for ty, cstrs in elts_typs:
                if not base_type_eq(inner_ty, ty):
                    raise Exception(f"{repr(inner_ty)} != {repr(ty)}")
                ret_constrs += cstrs

            ret_typ = ListType(inner_ty)
        case syn.DictLit():
            ret_typ = DictType()
        case syn.Subscript(value=v, idx=e):
            v_ty, v_constrs = check_expr(types, context, v)
            e_ty, e_constrs = check_expr(types, context, e)

            ret_typ = HMType.fresh("inner")
            ret_constrs = (
                v_constrs
                + e_constrs
                + [
                    BaseEq(v_ty, ListType(ret_typ)).pos(v),
                    BaseEq(e_ty, HMType.int()).pos(e),
                ]
            )

        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs) if op in ["<", "<=", "==", ">=", ">"]:
            lhs_ty, lhs_constrs = check_expr(types, context, lhs)
            rhs_ty, rhs_constrs = check_expr(types, context, rhs)
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
            lhs_ty, lhs_constrs = check_expr(types, context, lhs)
            rhs_ty, rhs_constrs = check_expr(types, context, rhs)
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
            fn_ty, constrs = check_expr(types, context, fn)
            arg_types = []

            for e in args:
                ty, cs = check_expr(types, context, e)
                arg_types += [(syn.NameGenerator.fresh("arg"), ty)]
                constrs += cs

            match fn_ty:
                case ArrowType(ret=ret):
                    ret_typ = ret
                case syn.HMType(base=TypeVar(name=name)):
                    ret_typ = HMType.fresh("ret")
                case t:
                    raise NotImplementedError(t)

            constrs += [
                BaseEq(fn_ty, ArrowType({}, arg_types, ret_typ).pos(expr)).pos(expr)
            ]
            ret_constrs = constrs

        case syn.GetAttr(name=name, attr=attr):
            (nametyp, namecstrs) = check_expr(types, context, name)
            match nametyp:
                case syn.ObjectType(fields=fields) if attr in fields:
                    ret_typ = fields[attr].pos(expr)
                    ret_constrs = namecstrs
                case syn.HMType(base=TypeVar(name=name)):
                    ret_typ = HMType.fresh("attr").pos(expr)
                case t:
                    raise errors.TypeError(BaseEq(t, syn.ObjectType("object")), at=expr)
        case syn.TypeApp(expr=e, arglist=args):
            e_typ, e_cstrs = check_expr(types, context, e)
            ret_typ = e_typ
            assert isinstance(e_typ, ArrowType)
            for (tv, _), concrete in zip(e_typ.type_abs.items(), args):
                ret_typ = ret_typ.subst_typevar(tv, concrete)
            assert isinstance(ret_typ, ArrowType)
            ret_typ.type_abs = {}
            ret_constrs = e_cstrs
        case x:
            raise NotImplementedError(x)
    # expr.annot(ret_typ)
    return ret_typ.pos(expr), ret_constrs
