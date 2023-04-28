import sys

sys.path.append("..")

from solvent import LiquidVar as L
from solvent.syntax import types as T


def test_integral_overloading():
    i = L("i", T.Int())
    j = L("j", T.Int())

    assert (i.add(42) == (i + 42))
    assert (i.add(j) == (i + j))
    assert (i.sub(42) == (i - 42))
    assert (i.sub(j) == (i - j))
    assert (i.mul(42) == (i * 42))
    assert (i.mul(j) == (i * j))
    assert (i.div(42) == (i / 42))
    assert (i.div(j) == (i / j))
    assert (i.mod(42) == (i % 42))
    assert (i.mod(j) == (i % j))

    assert i.lt(j) == (i < j)
    assert i.le(j) == (i <= j)
    assert i.gt(j) == (i > j)
    assert i.ge(j) == (i >= j)
    assert i.lt(42) == (i < 42)
    assert i.le(42) == (i <= 42)
    assert i.gt(42) == (i > 42)
    assert i.ge(42) == (i >= 42)


def test_boolean_overloading():
    b1 = L("b1", T.Bool());
    b2 = L("b2", T.Bool());

    # TODO: once we unify Python types and LiquidExprs, boolean expressions
    # with literals can always be constant-folded down if we really want.
    assert b1.band(True) == (b1 & True)
    assert b1.band(False) == (b1 & False)
    assert b1.band(b2) == (b1 & b2)

    assert b1.bor(True) == (b1 | True)
    assert b1.bor(b2) == (b1 | b2)

