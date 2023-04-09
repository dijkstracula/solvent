import copy

import pytest

from test_ast import str_to_ast_expr, str_to_assign

from solvent.ast import *


@pytest.fixture(autouse=True)
def before_all():
    CVar.reset()


def test_constant_constraints():
    c = Constant(42)
    assert Constraint(c, int) in c.constraints({})

    c = Constant(True)
    assert Constraint(c, bool) in c.constraints({})


def test_name_constraints():
    n = Name("n")
    assert [Constraint(n, int)] == n.constraints({n: int})
    assert Constraint(n, bool) in n.constraints({n: bool})
    assert Constraint(n, list) in n.constraints({n: list})


def test_arith_op_constraints():
    expr = ArithOp.from_pyast(str_to_ast_expr("1 + 2"))
    constraints = expr.constraints({})
    assert set(constraints) == set(
         [Constraint(Constant(1), int),
          Constraint(Constant(2), int),
          Constraint(expr, int)])

    expr = ArithOp.from_pyast(str_to_ast_expr("i + j"))
    constraints = expr.constraints({Name("i"): int, Name("j"): int})
    assert set(constraints) == set(
        [Constraint(Name("i"), int),
         Constraint(Name("j"), int),
         Constraint(expr, int)])


def test_bool_op_constraints():
    expr = BoolOp.from_pyast(str_to_ast_expr("b1 or b2 or True"))
    constraints = expr.constraints({Name("b1"): bool, Name("b2"): bool})
    assert set(constraints) == set(
        [Constraint(expr, bool),
         Constraint(Name("b1"), bool),
         Constraint(Name("b2"), bool),
         Constraint(Constant(True), bool)])

    expr = BoolOp.from_pyast(str_to_ast_expr("(b1 or b2) and True"))
    constraints = expr.constraints({Name("b1"): bool, Name("b2"): bool})
    assert set(constraints) == set(
        [Constraint(expr, bool),
         Constraint(BoolOp.from_pyast(str_to_ast_expr("b1 or b2")), bool),
         Constraint(Name("b1"), bool),
         Constraint(Name("b2"), bool),
         Constraint(Constant(True), bool)])

    # Here's one that will fail to typecheck later on: we're using i both
    # as an int and a bool.
    expr = BoolOp.from_pyast(str_to_ast_expr("b1 and i"))
    constraints = expr.constraints({Name("b1"): bool, Name("i"): int})
    assert set(constraints) == set(
        [Constraint(expr, bool),
         Constraint(Name("b1"), bool),
         Constraint(Name("i"), int),
         Constraint(Name("i"), bool)])


def test_compare_constraints():
    expr = Compare.from_pyast(str_to_ast_expr("1 < 2"))
    constraints = expr.constraints({})
    assert set(constraints) == set([
        Constraint(Constant(1), int),
        Constraint(Constant(2), int),
        Constraint(Constant(1), CVar(1)),
        Constraint(Constant(2), CVar(1)),
        Constraint(expr, CVar(1)),
    ])

    CVar.reset()

    expr = Compare.from_pyast(str_to_ast_expr("1 < True"))
    constraints = expr.constraints({})
    assert set(constraints) == set([
        Constraint(Constant(1), int),
        Constraint(Constant(True), bool),
        Constraint(Constant(1), CVar(1)),
        Constraint(Constant(True), CVar(1)),
        Constraint(expr, CVar(1)),
    ])


def test_list_constraints():
    expr = List.from_pyast(str_to_ast_expr("[]"))
    constraints = expr.constraints({})
    assert set(constraints) == set([Constraint(expr, (CVar(1),))])

    CVar.reset()

    expr = List.from_pyast(str_to_ast_expr("[1,2,3]"))
    constraints = expr.constraints({})
    assert set(constraints) == set([
        Constraint(Constant(1), int),
        Constraint(Constant(1), CVar(1)),
        Constraint(Constant(2), int),
        Constraint(Constant(2), CVar(1)),
        Constraint(Constant(3), int),
        Constraint(Constant(3), CVar(1)),
        Constraint(expr, (CVar(1),))
    ])


def test_subscript_constraints():
    expr = Subscript.from_pyast(str_to_ast_expr("a[4]"))


def test_if_constraints():
    tru = Constant(True)
    fls = Constant(False)
    b1 = Name("b1")
    b2 = Name("b2")

