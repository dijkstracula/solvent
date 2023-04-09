from solvent.ast import *

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
    assert Constant.from_pyast(str_to_ast_expr("42")).val == 42
    assert Constant.from_pyast(str_to_ast_expr("True")).val
    assert not Constant.from_pyast(str_to_ast_expr("False")).val

    with pytest.raises(errors.UnsupportedAST):
        Constant.from_pyast(str_to_ast_expr("3.14"))
    with pytest.raises(errors.UnsupportedAST):
        Constant.from_pyast(str_to_ast_expr("'hello'"))


def test_name_wrapper():
    assert Name.from_pyast(str_to_ast_expr("i")).id == "i"


def test_assign_wrapper():
    assign = Assign.from_pyast(str_to_assign("i = 42"))
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.id == "i"

    assert isinstance(assign.rhs, Constant)
    assert assign.rhs.val == 42

    assign = Assign.from_pyast(str_to_assign("i = 41 + 1"))
    assert isinstance(assign.lhs, Name)
    assert assign.lhs.id == "i"

    assert isinstance(assign.rhs, ArithOp)
    assert isinstance(assign.rhs.lhs, Constant)
    assert assign.rhs.lhs.val == 41
    assert isinstance(assign.rhs.rhs, Constant)
    assert assign.rhs.rhs.val == 1

    with pytest.raises(errors.ASTError):
        List.from_pyast(str_to_ast_expr("[x,y] = [1,2]"))
    with pytest.raises(errors.ASTError):
        Assign.from_pyast(str_to_ast_expr("x = x"))
    with pytest.raises(SyntaxError):
        Assign.from_pyast(str_to_ast_expr("3 = 4"))


def test_arith_expr_wrapper():
    expr = ArithOp.from_pyast(str_to_ast_expr("41 + 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.val == 1

    expr = ArithOp.from_pyast(str_to_ast_expr("41 - (2 * 3)"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, ArithOp)

    with pytest.raises(errors.BinopTypeMismatch):
        ArithOp.from_pyast(str_to_ast_expr("41 ** 2"))


def test_bool_op_wrapper():
    expr = BoolOp.from_pyast(str_to_ast_expr("b1 or True"))
    assert isinstance(expr, BoolOp)
    assert expr.op == "Or"
    assert expr.subs == [Name("b1"), Constant(True)]

    expr = BoolOp.from_pyast(str_to_ast_expr("b1 and b2 and b3"))
    assert isinstance(expr, BoolOp)
    assert expr.op == "And"
    assert expr.subs == [Name("b1"), Name("b2"), Name("b3")]


def test_compare_expr_wrapper():
    expr = Compare.from_pyast(str_to_ast_expr("41 < 1"))
    assert isinstance(expr.lhs, Constant)
    assert expr.lhs.val == 41
    assert isinstance(expr.rhs, Constant)
    assert expr.rhs.val == 1

    with pytest.raises(errors.UnsupportedAST):
        Compare.from_pyast(str_to_ast_expr("1 < 2 < 3"))
    with pytest.raises(errors.UnsupportedAST):
        Compare.from_pyast(str_to_ast_expr("'a' < 'b'"))
    with pytest.raises(errors.BinopTypeMismatch):
        Compare.from_pyast(str_to_ast_expr("1 in 2"))


def test_list_exprs():
    expr = List.from_pyast(str_to_ast_expr("[1,2,3]"))
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
    If.from_pyast(ast.parse(py).body[0])

    py = "\n".join([
        "if 1 < 2:",
        "  if False: i = 4",
        "else: i = 17"
    ])
    If.from_pyast(ast.parse(py).body[0])


def test_return_statement():
    assert Return.from_pyast(ast.parse("return").body[0]).val is None
    ret = Return.from_pyast(ast.parse("return 42").body[0])
    assert isinstance(ret.val, Constant)
    assert ret.val.val == 42


def test_function_def():
    fntext = "def f(x,y): return x + y"

    fn = FunctionDef.from_pyast(ast.parse(fntext).body[0])

    assert len(fn.body) == 1
    assert isinstance(fn.body[0], Return)
    assert isinstance(fn.body[0].val, ArithOp)
    assert isinstance(fn.body[0].val.lhs, Name)
    assert isinstance(fn.body[0].val.rhs, Name)
    assert fn.body[0].val.lhs.id == 'x'
    assert fn.body[0].val.rhs.id == 'y'

    fntext = "def f(x,y): return f(x, y)"
    fn = FunctionDef.from_pyast(ast.parse(fntext).body[0])
