import copy

import pytest

from test_ast import str_to_ast_expr, str_to_assign

from solvent.ast import *


@pytest.fixture(autouse=True)
def before_all():
    CVar.reset()


def test_constant_constraints():
    c = Constant(42)
    assert set(c.constraints({})) == set()

    c = Constant(True)
    assert set(c.constraints({})) == set()


def test_name_constraints():
    n = Name("n")
    assert n.type({n: int}) == int
    assert n.type({n: bool}) == bool
    assert n.type({n: list[int]}) == list[int]


def test_arith_op_constraints():
    expr = ArithOp.from_pyast(str_to_ast_expr("1 + 2"))
    constraints = expr.constraints({})
    assert set(constraints) == {Constraint(int, int)}

    expr = ArithOp.from_pyast(str_to_ast_expr("i + j"))
    constraints = set(expr.constraints({
        Name("i"): CVar(1),
        Name("j"): CVar(2)
    }))
    assert Constraint(int, CVar(1)) in constraints
    assert Constraint(int, CVar(2)) in constraints


def test_bool_op_constraints():
    expr = BoolOp.from_pyast(str_to_ast_expr("b1 or b2 or True"))
    constraints = expr.constraints({Name("b1"): bool, Name("b2"): bool})
    assert set(constraints) == {Constraint(bool, bool)}

    expr = BoolOp.from_pyast(str_to_ast_expr("(b1 or b2) and True"))
    constraints = expr.constraints({Name("b1"): bool, Name("b2"): bool})
    assert set(constraints) == {Constraint(bool, bool)}

    # Here's one that will fail to typecheck later on: we're using i both
    # as an int and a bool.
    expr = BoolOp.from_pyast(str_to_ast_expr("b1 and i"))
    constraints = expr.constraints({Name("b1"): bool, Name("i"): int})
    assert(Constraint(bool, int) in constraints)


def test_compare_constraints():
    expr = Compare.from_pyast(str_to_ast_expr("1 < 2"))
    constraints = set(expr.constraints({}))
    assert set(constraints) == {Constraint(int, int)}

    expr = Compare.from_pyast(str_to_ast_expr("1 < True"))
    constraints = expr.constraints({})
    assert set(constraints) == {Constraint(int, bool)}


def test_list_constraints():
    expr = List.from_pyast(str_to_ast_expr("[]"))
    constraints = expr.constraints({})
    assert set(constraints) == set()

    CVar.reset()

    expr = List.from_pyast(str_to_ast_expr("[1,2]"))
    constraints = expr.constraints({})
    assert set(constraints) == {Constraint(int, int)}


def test_subscript_constraints():
    expr = Subscript.from_pyast(str_to_ast_expr("[1,2,3][4]"))
    constraints = set(expr.constraints({}))
    assert set(constraints) == {Constraint(int, int)}

    CVar.reset()

    # Clearly shouldn't be able to unify; can only subscript by an int.
    expr = Subscript.from_pyast(str_to_ast_expr("[1,2,3][True]"))
    constraints = set(expr.constraints({}))
    assert set(constraints) == set({Constraint(int, bool), Constraint(int, int)})


def test_return_constraints():
    expr = Return(None)
    assert set(expr.constraints({})) == set()

    expr = Return(Constant(42))
    assert set(expr.constraints({})) == set()


def test_if_constraints():
    tru = Constant(True)
    fls = Constant(False)
    b1 = Name("b1")
    b2 = Name("b2")

