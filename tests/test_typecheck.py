import pytest

from solvent.ast import *
from solvent.typechecker.unification import unifier

@pytest.fixture(autouse=True)
def before_all():
    CVar.reset()


def str_to_ast_expr(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Expr):
        raise errors.MalformedAST(tree, ast.Expr)
    return tree.value


def test_constant_types():
    expr = Constant(42)
    assert set(expr.constraints({})) == set()
    assert expr.type({}) == int

    expr = Constant(True)
    assert set(expr.constraints({})) == set()
    assert expr.type({}) == bool


def test_name_type():
    expr = Name("i")
    assert set(expr.constraints({})) == set()
    assert expr.type({Name("i"): CVar(1)}) == CVar(1)


def test_arith_ops():
    expr = ArithOp.from_pyast(str_to_ast_expr("41 + 1"))
    constraints = set(expr.constraints({}))
    assert Constraint(int, expr.lhs.type({})) in constraints
    assert Constraint(int, expr.rhs.type({})) in constraints
    assert expr.type({}) == int


def test_bool_ops():
    expr = BoolOp.from_pyast(str_to_ast_expr("True or False"))
    constraints = set(expr.constraints({}))
    assert Constraint(bool, expr.subs[0].type({})) in constraints
    assert Constraint(bool, expr.subs[1].type({})) in constraints
    assert expr.type({}) == bool

    expr = BoolOp.from_pyast(str_to_ast_expr("b1 or b2"))
    env = {
        Name("b1"): bool,
        Name("b2"): bool,
    }

    constraints = set(expr.constraints(env))
    assert Constraint(bool, expr.subs[0].type(env)) in constraints
    assert Constraint(bool, expr.subs[1].type(env)) in constraints
    assert expr.type(env) == bool


def test_compare_ops():
    expr = Compare.from_pyast(str_to_ast_expr("1 < 2"))
    constraints = set(expr.constraints({}))
    assert Constraint(int, int) in constraints
    assert expr.type({}) == bool


def test_list_ops():
    expr = List.from_pyast(str_to_ast_expr("[]"))
    constraints = set(expr.constraints({}))
    assert constraints == set()
    assert expr.type({}) == list[CVar(1)]

    CVar.reset()

    expr = List.from_pyast(str_to_ast_expr("[1,2,3]"))
    constraints = set(expr.constraints({}))
    assert constraints == {Constraint(int, int)}
    assert expr.type({}) == list[int]

    expr = List.from_pyast(str_to_ast_expr("[i,j]"))
    env = {
        Name("i"): CVar(1),
        Name("j"): CVar(2)
    }
    constraints = set(expr.constraints(env))
    assert constraints == {Constraint(CVar(1), CVar(2))}
    assert expr.type(env) == list[CVar(1)]


def test_subscript_ops():
    expr = Subscript.from_pyast(str_to_ast_expr("[1,2,3][4]"))
    constraints = set(expr.constraints({}))
    assert constraints == {Constraint(int, int)}
    assert expr.type({}) == int

    expr = Subscript.from_pyast(str_to_ast_expr("[i, j][4]"))
    env = {
        Name("i"): CVar(1),
        Name("j"): CVar(2)
    }
    constraints = set(expr.constraints(env))
    assert constraints == {Constraint(int, int), Constraint(CVar(1), CVar(2))})
    assert expr.type(env) == CVar(1)
