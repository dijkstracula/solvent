import ast
import sys

from solvent.dsl import *
from solvent.syntax import types as LiquidTypes

sys.path.append("..")

def str_to_ast_expr(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Expr):
        raise errors.MalformedAST(tree, ast.Expr)
    return tree.value


def str_to_assign(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Assign) and not isinstance(tree, ast.AnnAssign):
        raise errors.MalformedAST(tree, ast.Assign)
    return tree


def test_simple_annot_assign():
    assign = AnnAssign.from_pyast(str_to_assign("i: int = 42"))
    assert assign.lhs == Name("i")
    assert assign.rhs == Constant(42)
    assert assign.annotation == LiquidTypes.Int()

    assign = AnnAssign.from_pyast(str_to_assign("b: bool = True"))
    assert assign.lhs == Name("b")
    assert assign.rhs == Constant(True)
    assert assign.annotation == LiquidTypes.Bool()

    assign = AnnAssign.from_pyast(str_to_assign("xs: list[int] = [1,2,3]"))
    assert assign.lhs == Name("xs")
    assert assign.rhs == List((Constant(1), Constant(2), Constant(3),))
    assert assign.annotation == LiquidTypes.Array(LiquidTypes.Int())

#def test_bound_lt_annot_assign():
    #assign = AnnAssign.from_pyast(str_to_assign("i: i >= 0 = 42"))
