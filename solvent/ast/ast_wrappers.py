import ast

from solvent import errors
from solvent.syntax.terms import EvalT, Predicate

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Type, Union

# Wrappers for a tiny, tiny subset of AST nodes

# Statements

# FunctionDef
# Return
# Assign
# AnnAssign
# If


PyAst = TypeVar("PyAst", bound=ast.AST, covariant=True)

Env = set[str]


def stmt_from_ast(tree: ast.AST, env: Env) -> "AstWrapper":
    if isinstance(tree, ast.FunctionDef):
        raise Exception("TODO")
    if isinstance(tree, ast.Return):
        raise Exception("TODO")
    if isinstance(tree, ast.Assign):
        return Assign(tree, env)
    if isinstance(tree, ast.AnnAssign):
        raise Exception("TODO")
    if isinstance(tree, ast.If):
        return If(tree, env)
    return expr_from_ast(tree, env)


def expr_from_ast(tree: ast.AST, env: Env) -> "Expr":
    if isinstance(tree, ast.Constant):
        return Constant(tree, env)
    if isinstance(tree, ast.Name):
        return Name(tree, env)
    if isinstance(tree, ast.BinOp):
        return ArithOp(tree, env)
    if isinstance(tree, ast.BoolOp):
        return BoolOp(tree, env)
    if isinstance(tree, ast.Compare):
        return Compare(tree, env)
    raise errors.UnsupportedAST(tree)


class AstWrapper(Generic[PyAst]):
    reified_ast_type: Type

    node: PyAst
    # base_type: Optional[Type[PyT]] = None # TODO: datatype for typevar constraint?
    liquid_type: Optional[Predicate] = None

    def __init__(self, node, env: Env = set()):
        if not isinstance(node, self.reified_ast_type):
            raise errors.MalformedAST(node, self.reified_ast_type)
        self.node = node
        self.validate(env)

    def validate(self, env: Env):
        raise Exception(f"validate() not yet implemented for type {type(self)}")


@dataclass(init=False)
class FunctionDef(AstWrapper[ast.FunctionDef]):
    pass


@dataclass(init=False)
class Return(AstWrapper[ast.Return]):
    pass


@dataclass(init=False)
class Assign(Generic[PyAst, EvalT], AstWrapper[ast.Assign]):
    reified_ast_type = ast.Assign
    lhs: "Name"
    rhs: "Expr"

    def validate(self, env: Env):
        if not isinstance(self.node.targets[0], ast.Name):
            raise errors.MalformedAST(self.node.targets[0], ast.Name)

        self.lhs = Name(self.node.targets[0], env)
        self.rhs = expr_from_ast(self.node.value, env)


@dataclass(init=False)
class AnnAssign(AstWrapper[ast.Assign]):
    pass


@dataclass(init=False)
class If(Generic[PyAst], AstWrapper[ast.If]):
    reified_ast_type = ast.If

    test: "Expr[PyAst, bool]"
    tru: list[AstWrapper]
    fls: list[AstWrapper]

    def validate(self, env: Env):
        test = expr_from_ast(self.node.test, env)
        self.test = test
        self.tru = [stmt_from_ast(stmt, env) for stmt in self.node.body]
        self.fls = [stmt_from_ast(stmt, env) for stmt in self.node.orelse]


# Expressions


class Expr(Generic[PyAst, EvalT], AstWrapper[PyAst]):
    pass


@dataclass(init=False)
class Constant(Expr[ast.Constant, int]):
    reified_ast_type = ast.Constant

    def validate(self, env: Env):
        if type(self.node.value) not in [bool, int]:
            raise errors.UnsupportedAST(self.node)


@dataclass(init=False)
class Name(Expr[ast.Name, EvalT]):
    reified_ast_type = ast.Name

    def validate(self, env: Env):
        if self.node.id not in env:
            if type(self.node.ctx) == ast.Load:
                raise errors.UnknownNameError(self.node)
            else:
                # We're in store scope,
                env.add(self.node.id)


@dataclass(init=False)
class ArithOp(Expr[ast.BinOp, int]):
    reified_ast_type = ast.BinOp
    lhs: Expr
    rhs: Expr

    def validate(self, env: Env):
        self.lhs = expr_from_ast(self.node.left, env)
        self.rhs = expr_from_ast(self.node.right, env)

        ops = [ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Mod]
        if self.node.op.__class__ not in ops:
            raise errors.BinopTypeMismatch(self.lhs, self.node.op, self.rhs)


@dataclass(init=False)
class BoolOp(Expr[ast.BoolOp, bool]):
    reified_ast_type = ast.BoolOp
    subs = list[Expr[PyAst, bool]]

    def validate(self, env: Env):
        self.subs = [expr_from_ast(e, env) for e in self.node.values]

        ops = [ast.Or, ast.And]
        if self.node.op.__class__ not in ops:
            raise errors.BinopTypeMismatch(self.subs[0], self.node.op, self.subs[1])


@dataclass(init=False)
class Compare(Generic[PyAst], Expr[ast.Compare, bool]):
    reified_ast_type = ast.Compare

    lhs: Expr[PyAst, bool]
    rhs: Expr[PyAst, bool]

    def validate(self, env: Env):
        if len(self.node.ops) != 1:
            raise errors.UnsupportedAST(self.node)
        if len(self.node.comparators) != 1:
            raise errors.UnsupportedAST(self.node)

        ops = [ast.Lt, ast.LtE, ast.Eq, ast.NotEq, ast.Gt, ast.GtE]
        if self.node.ops[0].__class__ not in ops:
            raise errors.BinopTypeMismatch(self.node.left, self.node.ops[0], self.node.comparators[0])

        self.lhs = expr_from_ast(self.node.left, env)
        self.rhs = expr_from_ast(self.node.comparators[0], env)
