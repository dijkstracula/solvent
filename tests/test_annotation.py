from solvent.dsl import *

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
    if not isinstance(tree, ast.Assign) and not isinstance(tree, ast.AnnAssign):
        raise errors.MalformedAST(tree, ast.Assign)
    return tree


def test_simple_annot_assign():
    assign = AnnAssign.from_pyast(str_to_assign("i: int = 42"))