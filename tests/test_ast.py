import ast
import pytest
import sys

sys.path.append("..")

from solvent import errors

from solvent.ast.ast_wrappers import *


def str_to_ast_expr(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Expr):
        raise errors.MalformedAST(tree, ast.Expr)
    return tree.value


def test_constant_wrapper():
    assert Constant(str_to_ast_expr("42")).node.value == 42
    assert Constant(str_to_ast_expr("True")).node.value
    assert not Constant(str_to_ast_expr("False")).node.value

    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("3.14"))
    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("'hello'"))
