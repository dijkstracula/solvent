"""
Implement an A-Normalizaton phase.

A-normalization transforms programs so that every intermediate computation
is named.
"""

from typing import List

from solvent import syntax as syn


def normalize(stmts: List[syn.Stmt]) -> List[syn.Stmt]:
    res = sum([normalize_stmt(s) for s in stmts], [])
    return res


def normalize_stmt(stmt: syn.Stmt) -> List[syn.Stmt]:
    match stmt:
        case syn.FunctionDef(name=name, args=args, return_annotation=retann, body=body):
            return [syn.FunctionDef(name, args, retann, normalize(body)).metadata(stmt)]
        case syn.If(test=test, body=body, orelse=orelse):
            temps, simple = normalize_expr(test)
            return temps + [
                syn.If(
                    test=simple,
                    body=normalize(body),
                    orelse=normalize(orelse),
                ).metadata(stmt)
            ]
        case syn.Assign(name=name, value=expr):
            temps, simple = normalize_expr(expr)
            return temps + [syn.Assign(name, simple).metadata(stmt)]
        case syn.Return(value=expr):
            temps, simple = normalize_expr(expr)
            return temps + [syn.Return(simple).metadata(stmt)]
        case x:
            raise NotImplementedError(x)


def normalize_expr(expr: syn.Expr) -> tuple[List[syn.Stmt], syn.Expr]:
    match expr:
        case syn.ArithBinOp(lhs=lhs, op=op, rhs=rhs):
            tmps = []
            if is_compound(lhs):
                res, base = normalize_expr(lhs)
                name = syn.NameGenerator.fresh("tmp")
                tmps += res + [syn.Assign(name, base).pos(lhs)]
                lhs = syn.Variable(name).pos(expr)

            if is_compound(rhs):
                res, base = normalize_expr(rhs)
                name = syn.NameGenerator.fresh("tmp")
                tmps += res + [syn.Assign(name, base).pos(rhs)]
                rhs = syn.Variable(name).pos(expr)

            return (tmps, syn.ArithBinOp(lhs, op, rhs).metadata(expr))
        case syn.BoolOp(lhs=lhs, op=op, rhs=rhs):
            tmps = []
            if is_compound(lhs):
                res, base = normalize_expr(lhs)
                name = syn.NameGenerator.fresh("tmp")
                tmps += res + [syn.Assign(name, base).pos(lhs)]
                lhs = syn.Variable(name).pos(expr)

            if is_compound(rhs):
                res, base = normalize_expr(rhs)
                name = syn.NameGenerator.fresh("tmp")
                tmps += res + [syn.Assign(name, base).pos(rhs)]
                rhs = syn.Variable(name).pos(expr)

            return (tmps, syn.BoolOp(lhs, op, rhs).metadata(expr))
        case syn.Call(function_name=fn, arglist=args):
            tmps = []
            new_arglist = []
            for a in args:
                if is_compound(a):
                    res, base = normalize_expr(a)
                    name = syn.NameGenerator.fresh("tmp")
                    tmps += res + [syn.Assign(name, base).pos(a)]
                    new_arglist.append(syn.Variable(name).pos(a))
                else:
                    new_arglist.append(a)
            return (tmps, syn.Call(fn, new_arglist).metadata(expr))
        case x:
            return ([], x)


def is_compound(expr: syn.Expr) -> bool:
    match expr:
        case syn.ArithBinOp():
            return True
        case syn.BoolOp():
            return True
        case syn.Neg():
            return True
        case syn.ListLiteral():
            return True
        case syn.Call():
            return True
        case _:
            return False
