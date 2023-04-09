import copy

from test_ast import str_to_ast_expr, str_to_assign

from solvent.ast import *


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

def test_if_constraints():
    tru = Constant(True)
    fls = Constant(False)
    b1 = Name("b1")
    b2 = Name("b2")

