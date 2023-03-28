import ast

from solvent import errors
from solvent.syntax.terms import PyT, Predicate

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Type

# Wrappers for a tiny, tiny subset of AST nodes

# Statements

# FunctionDef
# Return
# Assign
# AnnAssign
# If


PyAst = TypeVar("PyAst", bound=ast.AST)


# TODO: we need an environment
class AstWrapper(Generic[PyAst]):
    node: PyAst
    # base_type: Optional[Type[PyT]] = None # TODO: datatype for typevar constraint?
    liquid_type: Optional[Predicate] = None

    def __init__(self, expected_type):
        if not isinstance(self.node, expected_type):
            raise errors.MalformedAST(self.node, expected_type)
        self.validate()

    def validate(self):
        raise Exception(f"validate() not yet implemented for type {type(self)}")


class FunctionDef(AstWrapper[ast.FunctionDef]):
    pass


class Return(AstWrapper[ast.Return]):
    pass


class Assign(AstWrapper[ast.Assign]):
    pass


class AnnAssign(AstWrapper[ast.Assign]):
    pass


class If(AstWrapper[ast.If]):
    pass


# Expressions

# Constant
# Name

class Constant(AstWrapper[ast.Constant]):
    def __init__(self, node):
        self.node = node
        super().__init__(ast.Constant)

    def validate(self):
        if type(self.node.value) not in [bool, int]:
            raise errors.UnsupportedAST(self.node)


class Name(AstWrapper[ast.Name]):
    pass
