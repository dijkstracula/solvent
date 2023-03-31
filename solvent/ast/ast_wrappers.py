import ast

from solvent import errors
from solvent.syntax.terms import PyT, Predicate

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Union

# Wrappers for a tiny, tiny subset of AST nodes

# Statements

# FunctionDef
# Return
# Assign
# AnnAssign
# If


PyAst = TypeVar("PyAst", bound=ast.AST)

Env = dict[str, str] # TODO??

Expr = Union["Constant", "Name", "ArithOp"]


class AstWrapper(Generic[PyAst]):
    node: PyAst
    # base_type: Optional[Type[PyT]] = None # TODO: datatype for typevar constraint?
    liquid_type: Optional[Predicate] = None

    def __init__(self, expected_type, env: Env):
        if not isinstance(self.node, expected_type):
            raise errors.MalformedAST(self.node, expected_type)
        self.validate(env)

    def validate(self, env: Env):
        raise Exception(f"validate() not yet implemented for type {type(self)}")


class FunctionDef(AstWrapper[ast.FunctionDef]):
    pass


class Return(AstWrapper[ast.Return]):
    pass


class Assign(AstWrapper[ast.Assign]):
    lhs: "Name"
    rhs: Expr

    def __init__(self, node: ast.Assign, env: Env = {}):
        self.node = node
        super().__init__(ast.Assign, env)

    def validate(self, env: Env):
        if not isinstance(self.node.targets[0], ast.Name):
            raise errors.MalformedAST(self.node.targets[0], ast.Name)

        self.lhs = Name(self.node.targets[0])
        self.rhs = expr_class_from_ast(self.node.value)(self.node.value, env)


class AnnAssign(AstWrapper[ast.Assign]):
    pass


class If(AstWrapper[ast.If]):
    pass


# Expressions


def expr_class_from_ast(tree: ast.AST):
    if isinstance(tree, ast.Constant):
        return Constant
    if isinstance(tree, ast.Name):
        return Name
    if isinstance(tree, ast.BinOp):
        return ArithOp
    if isinstance(tree, ast.BoolOp):
        raise Exception("TODO")
    raise Exception("TODO")


class Constant(AstWrapper[ast.Constant]):
    def __init__(self, node, env: Env = {}):
        self.node = node
        super().__init__(ast.Constant, env)

    def validate(self, env: Env):
        if type(self.node.value) not in [bool, int]:
            raise errors.UnsupportedAST(self.node)


class Name(AstWrapper[ast.Name]):
    def __init__(self, node, env: Env = {}):
        self.node = node
        super().__init__(ast.Name, env)

    def validate(self, env: Env):
        if self.node.id not in env and type(self.node.ctx) == ast.Load:
            raise errors.UnknownNameError(self.node)


@dataclass
class ArithOp(AstWrapper[ast.BinOp]):
    lhs: Expr
    rhs: Expr

    def __init__(self, node, env: Env = {}):
        self.node = node
        super().__init__(ast.BinOp, env)

    def validate(self, env: Env):
        self.lhs = expr_class_from_ast(self.node.left)(self.node.left, env)
        self.rhs = expr_class_from_ast(self.node.right)(self.node.right, env)
