from solvent.typechecker.unification import *


def test_constraint_unify_noenv():
    assert Constraint(CVar(1), CVar(1)).unify({}) == {}
    assert Constraint(CVar(1), CVar(2)).unify({}) == {CVar(1): CVar(2)}
    assert Constraint(CVar(1), 42).unify({}) == {CVar(1): 42}
    assert Constraint(CVar(1), 42).unify({}) == Constraint(42, CVar(1)).unify({})
    assert Constraint(CVar(1), 42).unify({}) == {CVar(1): 42}
    assert Constraint(42, 42).unify({}) == {}
    assert Constraint(41, 42).unify({}) is None


def test_constraint_unify_withenv():
    assert Constraint(CVar(1), CVar(1)).unify({CVar(1): 42}) == {CVar(1): 42}
    assert Constraint(CVar(1), CVar(2)).unify({CVar(1): 42}) == {CVar(1): 42, CVar(2): 42}
    assert Constraint(CVar(2), CVar(1)).unify({CVar(1): 42}) == {CVar(1): 42, CVar(2): 42}


def test_unify_of_equality_constraints():
    # "For instance, if we have the equations ?1 + ?1 = 0 and ?2 + ?3 = ?3 then unification
    # will conclude that ?2 and ?3 are zero."
    constraints = [
        Constraint(CVar(1), CVar(2)),
        Constraint(CVar(1), CVar(3)),
        Constraint(0, CVar(3))]
    env = {}
    [env := c.unify(env) for c in constraints]
    assert env == {CVar(1): CVar(2), CVar(2): CVar(3), CVar(3): 0}

    env = {x: subst_env(env, x) for x in env}
    assert env == {CVar(1): 0, CVar(2): 0, CVar(3): 0}
    assert env == unifier(constraints)


def test_unifier_of_equality_constraints():
    lhs = [CVar(1), "+", CVar(1), "=", 0]
    rhs = [CVar(2), "+", CVar(3), "=", CVar(3)]
    constraints = flip(lhs, rhs)
    env = unifier(constraints)
    assert env == {CVar(1): 0, CVar(2): 0, CVar(3): 0}

def test_unifier():
    constraints = [
        Constraint(CVar(1), CVar(2)),
        Constraint(CVar(2), CVar(1))]
    assert unifier(constraints) == {CVar(1): CVar(2)}


