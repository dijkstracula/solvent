from typing import List

from solvent import syntax as syn
from solvent.syntax import Expr, HMType, Stmt, TypeApp, TypeVar
from solvent.visitor import Visitor

from .unification import Solution, free_vars, subst_one


class Subst(Visitor):
    def start(self, solution: Solution):
        self.solution = solution

    def start_Stmt(self, stmt: Stmt):
        for var in free_vars(stmt.typ):
            if var in self.solution:
                stmt.annot(subst_one(var, self.solution[var], stmt.typ))

        return super().start_Stmt(stmt)

    def start_Expr(self, expr: Expr):
        for var in free_vars(expr.typ):
            if var in self.solution:
                expr.annot(subst_one(var, self.solution[var], expr.typ))

        match expr.typ:
            case HMType(TypeVar(name=n)) if n in self.solution:
                expr.annot(self.solution[n])
            case _:
                pass

    def end_TypeApp(self, op: TypeApp) -> Expr | None:
        new_args = []
        for a in op.arglist:
            match a:
                case HMType(base=TypeVar(name=n)) if n in self.solution:
                    new_args += [self.solution[n]]
                case _:
                    new_args += [a]
        return TypeApp(op.expr, new_args, typ=op.typ).pos(op)


def subst_stmts(solution: Solution, stmts: List[syn.Stmt]):
    for stmt in stmts:
        subst_stmt(solution, stmt)


def subst_stmt(solution: Solution, stmt: syn.Stmt):
    for var in free_vars(stmt.typ):
        if var in solution:
            stmt.annot(subst_one(var, solution[var], stmt.typ))

    match stmt:
        case syn.FunctionDef(body=body):
            subst_stmts(solution, body)
        case syn.If(test=test, body=body, orelse=orelse):
            subst_expr(solution, test)
            subst_stmts(solution, body)
            subst_stmts(solution, orelse)
        case syn.Assign(value=value):
            subst_expr(solution, value)
        case syn.Return(value=value):
            subst_expr(solution, value)
        case x:
            raise NotImplementedError(x)


def subst_expr(solution: Solution, expr: syn.Expr):
    for var in free_vars(expr.typ):
        if var in solution:
            expr.annot(subst_one(var, solution[var], expr.typ))

    match expr.typ:
        case HMType(TypeVar(name=n)) if n in solution:
            expr.annot(solution[n])
        case _:
            pass

    match expr:
        case syn.Variable():
            pass
        case syn.IntLiteral():
            pass
        case syn.BoolLiteral(_):
            pass
        case syn.StrLiteral():
            pass
        case syn.ListLiteral(elts=elts):
            for e in elts:
                subst_expr(solution, e)
        case syn.Neg(expr=e):
            subst_expr(solution, e)
        case syn.ArithBinOp(lhs=lhs, rhs=rhs):
            subst_expr(solution, lhs)
            subst_expr(solution, rhs)
        case syn.BoolOp(lhs=lhs, rhs=rhs):
            subst_expr(solution, lhs)
            subst_expr(solution, rhs)
        case syn.Call(function_name=fn, arglist=args):
            subst_expr(solution, fn)
            for e in args:
                subst_expr(solution, e)
        case syn.Subscript(value=v, idx=e):
            subst_expr(solution, v)
            subst_expr(solution, e)
        case syn.GetAttr(name=name):
            subst_expr(solution, name)
        case syn.TypeApp(expr=e, arglist=args):
            subst_expr(solution, e)
        case x:
            raise NotImplementedError(x)
