import ast
import pytest
import sys

sys.path.append("..")

from solvent.ast.ast_wrappers import *


def str_to_ast_expr(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Expr):
        raise errors.MalformedAST(tree, ast.Expr)
    return tree.value

def str_to_assign(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Assign):
        raise errors.MalformedAST(tree, ast.Assign)
    return tree

def test_constant_wrapper():
    assert Constant(str_to_ast_expr("42")).node.value == 42
    assert Constant(str_to_ast_expr("True")).node.value
    assert not Constant(str_to_ast_expr("False")).node.value

    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("3.14"))
    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("'hello'"))

def test_name_wrapper():
    assert Name(str_to_ast_expr("i"), set("i")).node.id == "i"

    with pytest.raises(errors.UnknownNameError):
        Name(str_to_ast_expr("i"))


def test_assign_wrapper():
    env = set()
    assign = Assign(str_to_assign("i = 42"), env)
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.node.id == "i"
    assert "i" in env

    assert isinstance(assign.rhs, Constant)
    assert assign.rhs.node.value == 42

    assign = Assign(str_to_assign("i = 41 + 1"))
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.node.id == "i"

    assert isinstance(assign.rhs, ArithOp)
    assert isinstance(assign.rhs.lhs, Constant)
    assert assign.rhs.lhs.node.value == 41
    assert isinstance(assign.rhs.rhs, Constant)
    assert assign.rhs.rhs.node.value == 1


def test_arith_expr_wrapper():
    expr = ArithOp(str_to_ast_expr("41 + 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.node.value == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.node.value == 1

    expr = ArithOp(str_to_ast_expr("41 - (2 * 3)"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.node.value == 41
    assert isinstance(expr.rhs, ArithOp)

    with pytest.raises(errors.BinopTypeMismatch):
        ArithOp(str_to_ast_expr("41 ** 2"))


def test_compare_expr_wrapper():
    expr = Compare(str_to_ast_expr("41 < 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.node.value == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.node.value == 1

    with pytest.raises(errors.UnsupportedAST):
        Compare(str_to_ast_expr("1 < 2 < 3"))
    with pytest.raises(errors.UnsupportedAST):
        Compare(str_to_ast_expr("'a' < 'b'"))
    with pytest.raises(errors.BinopTypeMismatch):
        Compare(str_to_ast_expr("1 in 2"))

def test_compare_if_statements():
    py = "\n".join([
        "if True:",
        " i = 42",
        "else: i = 17"
    ])
    If(ast.parse(py).body[0])

    py = "\n".join([
        "if 1 < 2:",
         "  if False: i = 4",
        "else: i = 17"
    ])
    If(ast.parse(py).body[0])
