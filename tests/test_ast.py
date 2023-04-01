from solvent.ast.nodes import *

import ast
import pytest
import sys

sys.path.append("..")


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
    assert Constant(str_to_ast_expr("42")).val == 42
    assert Constant(str_to_ast_expr("True")).val
    assert not Constant(str_to_ast_expr("False")).val

    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("3.14"))
    with pytest.raises(errors.UnsupportedAST):
        Constant(str_to_ast_expr("'hello'"))


def test_name_wrapper():
    assert Name(str_to_ast_expr("i")).node.id == "i"


def test_assign_wrapper():
    assign = Assign(str_to_assign("i = 42"))
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.node.id == "i"

    assert isinstance(assign.rhs, Constant)
    assert assign.rhs.val == 42

    assign = Assign(str_to_assign("i = 41 + 1"))
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.node.id == "i"

    assert isinstance(assign.rhs, ArithOp)
    assert isinstance(assign.rhs.lhs, Constant)
    assert assign.rhs.lhs.val == 41
    assert isinstance(assign.rhs.rhs, Constant)
    assert assign.rhs.rhs.val == 1

    with pytest.raises(errors.ASTError):
        List(str_to_ast_expr("[x,y] = [1,2]"))
    with pytest.raises(errors.ASTError):
        List(str_to_ast_expr("x = x"))
    with pytest.raises(SyntaxError):
        List(str_to_ast_expr("3 = 4"))


def test_arith_expr_wrapper():
    expr = ArithOp(str_to_ast_expr("41 + 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.val == 1

    expr = ArithOp(str_to_ast_expr("41 - (2 * 3)"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, ArithOp)

    with pytest.raises(errors.BinopTypeMismatch):
        ArithOp(str_to_ast_expr("41 ** 2"))


def test_compare_expr_wrapper():
    expr = Compare(str_to_ast_expr("41 < 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.val == 1

    with pytest.raises(errors.UnsupportedAST):
        Compare(str_to_ast_expr("1 < 2 < 3"))
    with pytest.raises(errors.UnsupportedAST):
        Compare(str_to_ast_expr("'a' < 'b'"))
    with pytest.raises(errors.BinopTypeMismatch):
        Compare(str_to_ast_expr("1 in 2"))


def test_list_exprs():
    expr = List(str_to_ast_expr("[1,2,3]"))
    assert isinstance(expr, List)
    assert len(expr.elements) == 3
    assert isinstance(expr.elements[0], Constant)
    assert expr.elements[0].val == 1


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


def test_return_statement():
    assert Return(ast.parse("return").body[0]).val is None
    ret = Return(ast.parse("return 42").body[0])
    assert ret.val
    assert ret.val.node.value == 42


def test_function_def():
    fntext = "def f(x,y): return x + y"

    fn = FunctionDef(ast.parse(fntext).body[0])

    assert len(fn.body) == 1
    assert isinstance(fn.body[0], Return)
    assert isinstance(fn.body[0].val, ArithOp)
    assert isinstance(fn.body[0].val.lhs, Name)
    assert isinstance(fn.body[0].val.rhs, Name)
    assert fn.body[0].val.lhs.id == 'x'
    assert fn.body[0].val.rhs.id == 'y'

    fntext = "def f(x,y): return f(x, y)"
    fn = FunctionDef(ast.parse(fntext).body[0])
