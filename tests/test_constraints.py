import copy

from test_ast import str_to_ast_expr, str_to_assign

from solvent.ast import *


def test_constant_constraints():
    c = Constant.from_pyast(str_to_ast_expr("42"))
    assert Constraint(c, int) in c.constraints({})

    c = Constant.from_pyast(str_to_ast_expr("True"))
    assert Constraint(c, bool) in c.constraints({})


def test_name_constraints():
    n = Name.from_pyast(str_to_ast_expr("i"))
    assert [Constraint(n, int)] == n.constraints({n: int})
    assert Constraint(n, bool) in n.constraints({n: bool})
    assert Constraint(n, list) in n.constraints({n: list})
