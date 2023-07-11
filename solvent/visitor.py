from typing import Callable, List, cast

from solvent import errors, position
from solvent.syntax import (
    ArithBinOp,
    ArrowType,
    Assign,
    BoolLiteral,
    BoolOp,
    Call,
    Expr,
    FunctionDef,
    GetAttr,
    HMType,
    If,
    IntLiteral,
    ListLiteral,
    ListType,
    Neg,
    ObjectType,
    Return,
    Star,
    Stmt,
    StrLiteral,
    Subscript,
    Type,
    TypeApp,
    V,
    Variable,
)


class Visitor:
    def __init__(self, *args, **kwargs) -> None:
        self.start(*args, **kwargs)

    def visit_stmts(self, stmts: List[Stmt]) -> List[Stmt]:
        return [self.visit_stmt(stmt) for stmt in stmts]

    def visit_stmt(self, stmt: Stmt) -> Stmt:
        self.start_Stmt(stmt)
        new_stmt = stmt
        match stmt:
            case FunctionDef(name=name, args=args, return_annotation=retann, body=body):
                self.start_FunctionDef(cast(FunctionDef, stmt))
                new_stmt = FunctionDef(
                    name,
                    args,
                    retann,
                    self.visit_stmts(body),
                    node_id=stmt.node_id,
                ).pos(stmt)
                self.end_FunctionDef(new_stmt)
            case If(test=test, body=body, orelse=orelse):
                self.start_If(cast(If, stmt))
                new_stmt = If(
                    self.visit_expr(test),
                    self.visit_stmts(body),
                    self.visit_stmts(orelse),
                    node_id=stmt.node_id,
                ).pos(stmt)
                self.end_If(new_stmt)
            case Assign(name=name, value=expr):
                self.start_Assign(cast(Assign, stmt))
                new_stmt = Assign(
                    name, self.visit_expr(expr), node_id=stmt.node_id
                ).pos(stmt)
                self.end_Assign(new_stmt)
            case Return(value=expr):
                self.start_Return(cast(Return, stmt))
                new_stmt = Return(self.visit_expr(expr), node_id=stmt.node_id).pos(stmt)
                self.end_Return(new_stmt)
            case x:
                raise errors.Unreachable(x)
        ret_stmt = self.end_Stmt(new_stmt)
        if ret_stmt is None:
            return new_stmt.pos(stmt)
        else:
            return ret_stmt.pos(stmt)

    def visit_expr(self, expr: Expr) -> Expr:
        self.start_Expr(expr)
        match expr:
            case V():
                new_expr = self.start_V(cast(V, expr))
            case Star():
                new_expr = self.start_Star(cast(Star, expr))
            case Variable():
                new_expr = self.start_Variable(cast(Variable, expr))
            case IntLiteral():
                new_expr = self.start_IntLiteral(cast(IntLiteral, expr))
            case ArithBinOp(lhs=lhs, op=op, rhs=rhs):
                self.start_ArithBinOp(cast(ArithBinOp, expr))
                new_expr = ArithBinOp(
                    self.visit_expr(lhs),
                    op,
                    self.visit_expr(rhs),
                    node_id=expr.node_id,
                ).pos(expr)
                self.end_ArithBinOp(new_expr)
            case BoolLiteral():
                new_expr = self.start_BoolLiteral(cast(BoolLiteral, expr))
            case StrLiteral():
                new_expr = self.start_StrLiteral(cast(StrLiteral, expr))
            case ListLiteral(elts=elts):
                self.start_ListLiteral(cast(ListLiteral, expr))
                new_expr = ListLiteral(
                    [self.visit_expr(e) for e in elts],
                    node_id=expr.node_id,
                )
                self.end_ListLiteral(new_expr)
            case GetAttr(name=name, attr=attr):
                self.start_GetAttr(cast(GetAttr, expr))
                new_expr = self.end_GetAttr(
                    GetAttr(
                        name=self.visit_expr(name),
                        attr=attr,
                        node_id=expr.node_id,
                    )
                )
            case Subscript(value=v, idx=e):
                self.start_Subscript(cast(Subscript, expr))
                new_expr = Subscript(
                    self.visit_expr(v),
                    self.visit_expr(e),
                    node_id=expr.node_id,
                )
                self.end_Subscript(new_expr)
            case BoolOp(lhs=lhs, op=op, rhs=rhs):
                self.start_BoolOp(cast(BoolOp, expr))
                new_expr = BoolOp(
                    self.visit_expr(lhs),
                    op,
                    self.visit_expr(rhs),
                    node_id=expr.node_id,
                ).pos(expr)
                self.end_BoolOp(new_expr)
            case Neg(expr=e):
                self.start_Neg(cast(Neg, expr))
                new_expr = Neg(self.visit_expr(e), node_id=expr.node_id)
                self.end_Neg(new_expr)
            case Call(function_name=fn, arglist=args):
                self.start_Call(cast(Call, expr))
                new_expr = Call(
                    self.visit_expr(fn),
                    [self.visit_expr(a) for a in args],
                    node_id=expr.node_id,
                )
                new_expr = self.end_Call(new_expr)
            case TypeApp(expr=e, arglist=args):
                self.start_TypeApp(cast(TypeApp, expr))
                new_expr = TypeApp(self.visit_expr(e), args, node_id=expr.node_id)
                new_expr = self.end_TypeApp(new_expr)
            case x:
                raise errors.Unreachable(x)
        if new_expr is None:
            new_expr = expr

        end_expr = self.end_Expr(new_expr)
        if end_expr is None:
            return new_expr.pos(expr)
        else:
            return end_expr.pos(expr)

    def visit_typ(self, typ: Type) -> Type:
        return typ

    def start(self, *args, **kwargs):
        pass

    def start_Stmt(self, stmt: Stmt):
        pass

    def end_Stmt(self, stmt: Stmt) -> Stmt | None:
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

    def end_Expr(self, expr: Expr) -> Expr | None:
        pass

    def start_V(self, v: V) -> Expr | None:
        pass

    def start_Star(self, star: Star) -> Expr | None:
        pass

    def start_Variable(self, var: Variable):
        pass

    def start_IntLiteral(self, lit: IntLiteral):
        pass

    def start_BoolLiteral(self, lit: BoolLiteral):
        pass

    def start_StrLiteral(self, lit: StrLiteral):
        pass

    def start_ListLiteral(self, lit: ListLiteral):
        pass

    def end_ListLiteral(self, lit: ListLiteral):
        pass

    def start_ArithBinOp(self, arith_bin_op: ArithBinOp):
        pass

    def end_ArithBinOp(self, arith_bin_op: ArithBinOp):
        pass

    def start_GetAttr(self, lit: GetAttr):
        pass

    def end_GetAttr(self, lit: GetAttr) -> Expr | None:
        pass

    def start_Subscript(self, subscript: Subscript):
        pass

    def end_Subscript(self, subscript: Subscript):
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

    def end_Call(self, op: Call) -> Expr:
        return op

    def start_TypeApp(self, op: TypeApp):
        pass

    def end_TypeApp(self, op: TypeApp) -> Expr | None:
        pass


def type_mapper(typ: Type, fn: Callable[[Type], Type]) -> Type:
    match typ:
        case ArrowType(type_abs=abs, args=args, ret=ret):
            return fn(
                ArrowType(
                    abs,
                    [(name, type_mapper(t, fn)) for name, t in args],
                    type_mapper(ret, fn),
                )
            ).metadata(typ)
        case ListType(inner_typ=inner):
            return fn(ListType(type_mapper(inner, fn))).metadata(typ)
        case ObjectType(name=name, type_abs=abs, fields=fields):
            return fn(
                ObjectType(
                    name=name,
                    type_abs=abs,
                    fields={x: type_mapper(t, fn) for x, t in fields.items()},
                )
            ).metadata(typ)
        case x:
            return fn(x).metadata(x)


# class TypeVisitor:
#     def enter_HMType():
#         pass

#     def
