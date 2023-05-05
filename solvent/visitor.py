from typing import List, cast

from solvent import errors
from solvent.syntax import (
    ArithBinOp,
    Assign,
    BoolLiteral,
    BoolOp,
    Call,
    Expr,
    FunctionDef,
    If,
    IntLiteral,
    Neg,
    Return,
    Star,
    Stmt,
    Type,
    V,
    Variable,
)


class Visitor:
    def __init__(self) -> None:
        self.start()

    def visit_stmts(self, stmts: List[Stmt]):
        for stmt in stmts:
            self.visit_stmt(stmt)

    def visit_stmt(self, stmt: Stmt):
        self.start_Stmt(stmt)
        match stmt:
            case FunctionDef(body=body):
                self.start_FunctionDef(cast(FunctionDef, stmt))
                self.visit_stmts(body)
                self.end_FunctionDef(cast(FunctionDef, stmt))
            case If(test=test, body=body, orelse=orelse):
                self.start_If(cast(If, stmt))
                self.visit_expr(test)
                self.visit_stmts(body)
                self.visit_stmts(orelse)
                self.end_If(cast(If, stmt))
            case Assign(value=expr):
                self.start_Assign(cast(Assign, stmt))
                self.visit_expr(expr)
                self.end_Assign(cast(Assign, stmt))
            case Return(value=expr):
                self.start_Return(cast(Return, stmt))
                self.visit_expr(expr)
                self.end_Return(cast(Return, stmt))
            case x:
                raise errors.Unreachable(x)
        self.end_Stmt(stmt)

    def visit_expr(self, expr: Expr):
        self.start_Expr(expr)
        match expr:
            case V():
                self.start_V(cast(V, expr))
            case Star():
                self.start_Star(cast(Star, expr))
            case Variable():
                self.start_Variable(cast(Variable, expr))
            case IntLiteral():
                self.start_IntLiteral(cast(IntLiteral, expr))
            case ArithBinOp(lhs=lhs, rhs=rhs):
                self.start_ArithBinOp(cast(ArithBinOp, expr))
                self.visit_expr(lhs)
                self.visit_expr(rhs)
                self.end_ArithBinOp(cast(ArithBinOp, expr))
            case BoolLiteral():
                self.start_BoolLiteral(cast(BoolLiteral, expr))
            case BoolOp(lhs=lhs, rhs=rhs):
                self.start_BoolOp(cast(BoolOp, expr))
                self.visit_expr(lhs)
                self.visit_expr(rhs)
                self.end_BoolOp(cast(BoolOp, expr))
            case Neg(expr=expr):
                self.start_Neg(cast(Neg, expr))
                self.visit_expr(expr)
                self.end_Neg(cast(Neg, expr))
            case Call(function_name=fn, arglist=args):
                self.start_Call(cast(Call, expr))
                self.visit_expr(fn)
                for a in args:
                    self.visit_expr(a)
                self.end_Call(cast(Call, expr))
            case x:
                raise errors.Unreachable(x)
        self.end_Expr(expr)

    def visit_typ(self, typ: Type) -> Type:
        return typ

    def start(self):
        pass

    def start_Stmt(self, stmt: Stmt):
        pass

    def end_Stmt(self, stmt: Stmt):
        pass

    def start_FunctionDef(self, fd: FunctionDef):
        pass

    def end_FunctionDef(self, fd: FunctionDef):
        pass

    def start_If(self, if_stmt: If):
        pass

    def end_If(self, if_stmt: If):
        pass

    def start_Assign(self, asgn: Assign):
        pass

    def end_Assign(self, asgn: Assign):
        pass

    def start_Return(self, ret: Return):
        pass

    def end_Return(self, ret: Return):
        pass

    def start_Expr(self, expr: Expr):
        pass

    def end_Expr(self, expr: Expr):
        pass

    def start_V(self, v: V):
        pass

    def start_Star(self, star: Star):
        pass

    def start_Variable(self, var: Variable):
        pass

    def start_IntLiteral(self, lit: IntLiteral):
        pass

    def start_ArithBinOp(self, arith_bin_op: ArithBinOp):
        pass

    def end_ArithBinOp(self, arith_bin_op: ArithBinOp):
        pass

    def start_BoolLiteral(self, lit: BoolLiteral):
        pass

    def start_BoolOp(self, op: BoolOp):
        pass

    def end_BoolOp(self, op: BoolOp):
        pass

    def start_Neg(self, op: Neg):
        pass

    def end_Neg(self, op: Neg):
        pass

    def start_Call(self, op: Call):
        pass

    def end_Call(self, op: Call):
        pass
