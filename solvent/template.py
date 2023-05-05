from typing import List, Type

from solvent import errors
from solvent import syntax as syn
from solvent.syntax import ArrowType, HMType, RType


def template_type(typ: Type) -> Type:
    match typ:
        case RType():
            return typ
        case HMType(base=base):
            return RType.template(base)
        case ArrowType(args=args, ret=ret):
            return ArrowType(
                [(x, template_type(t)) for x, t in args],
                ret=template_type(ret),
            ).pos(typ)
        case x:
            raise errors.Unreachable(x)


def template_stmts(stmts: List[syn.Stmt]):
    for stmt in stmts:
        template_stmt(stmt)


def template_stmt(stmt: syn.Stmt):
    if stmt.typ is not None:
        stmt.annot(template_type(stmt.typ))
    match stmt:
        case syn.FunctionDef(body=body):
            template_stmts(body)
        case syn.If(test=test, body=body, orelse=orelse):
            template_expr(test)
            template_stmts(body)
            template_stmts(orelse)
        case syn.Assign(value=value):
            template_expr(value)
        case syn.Return(value=value):
            template_expr(value)
        case x:
            print(x)
            raise NotImplementedError


def template_expr(expr: syn.Expr):
    if expr.typ is not None:
        expr.annot(template_type(expr.typ))
    match expr:
        case syn.Variable():
            pass
        case syn.IntLiteral():
            pass
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            template_expr(lhs)
            template_expr(rhs)
        case syn.BoolLiteral(_):
            pass
        case syn.BoolOp(lhs=lhs, rhs=rhs):
            template_expr(lhs)
            template_expr(rhs)
        case syn.Call(function_name=fn, arglist=args):
            template_expr(fn)
            for e in args:
                template_expr(e)
        case x:
            print(x)
            raise NotImplementedError
