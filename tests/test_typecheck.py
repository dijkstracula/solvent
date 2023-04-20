import pytest

from solvent.dsl import *


@pytest.fixture(autouse=True)
def before_all():
    CVar.reset()


def str_to_ast_expr(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.Expr):
        raise errors.MalformedAST(tree, ast.Expr)
    return tree.value


def str_to_ast_stmt(source: str):
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.stmt):
        raise errors.MalformedAST(tree, ast.stmt)
    return tree

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
    assert constraints == {Constraint(int, int), Constraint(CVar(1), CVar(2))}
    assert expr.type(env) == CVar(1)

    expr = Subscript.from_pyast(str_to_ast_expr("[1,2,3][True]"))
    constraints = set(expr.constraints({}))
    assert constraints == {Constraint(int, int), Constraint(int, bool)}
    assert expr.type({}) == int


def test_const_function_ops():
    fn = FunctionDef.from_pyast(str_to_ast_stmt("def forty_two(): return 42"))
    constraints = set(fn.constraints({}))
    assert constraints == {Constraint(CVar(1), int)}
    assert fn.type({}) == ArrowType([], CVar(1))
    assert fn.unify_type({}) == ArrowType([], int)


def test_unary_function_ops():
    fn = FunctionDef.from_pyast(str_to_ast_stmt("def inc(i): return i + 1"))
    constraints = set(fn.constraints({}))
    assert fn.type({}) == ArrowType([CVar(1)], CVar(2))
    assert constraints == {
        Constraint(int, CVar(1)),  # arg
        Constraint(int, int),      # body
        Constraint(CVar(2), int)   # ret
    }
    assert fn.unify_type({}) == ArrowType([int], int)


def test_binary_function_op():
    fn = FunctionDef.from_pyast(str_to_ast_stmt("def sum(x, y): return x + y"))
    constraints = set(fn.constraints({}))
    assert fn.type({}) == ArrowType([CVar(1), CVar(2)], CVar(3))
    assert constraints == {
        Constraint(int, CVar(1)),
        Constraint(int, CVar(2)),
        Constraint(CVar(3), int)
    }
    assert fn.unify_type({}) == ArrowType([int, int], int)


def test_max_fn():
    fn = """
def max(x, y):
    if x > y:
        return x
    else:
        return y
"""
    fn = FunctionDef.from_pyast(str_to_ast_stmt(fn))
    assert fn.type({}) == ArrowType([CVar(1), CVar(2)], CVar(3))
    constraints = set(fn.constraints({}))
    assert constraints == {
        Constraint(CVar(1), int),
        Constraint(CVar(2), int),
        Constraint(CVar(3), CVar(1)),
        Constraint(CVar(3), CVar(2)),
    }
    assert fn.unify_type({}) == ArrowType([int, int], int)
