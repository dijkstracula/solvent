import pytest
import sys

from solvent import errors
from solvent import LiquidVar as L

from solvent.syntax import types as T
from solvent.syntax import quants

sys.path.append("..")


def test_fromPyType():
    assert (T.from_py_type(int) == T.Int())
    assert (T.from_py_type(bool) == T.Bool())
    assert (T.from_py_type(list[bool]) == T.Array(T.Bool()))
    assert (T.from_py_type(list[list[bool]]) == T.Array(T.Array(T.Bool())))

    # We can statically catch first-order invalid calls (e.g. fromPyType(float))
    # but higher-order ones have to be deferred to runtime.
    with pytest.raises(errors.UnsupportedPyType):
        T.from_py_type(list[float])


def test_backing_python_type():
    assert (T.Int().python_type == int)
    assert (T.Bool().python_type == bool)
    assert (T.Array(T.Bool()).python_type == list)


def test_liquidvar_construction():
    assert (L("i", int) == L("i", T.Int()))
    assert (L("b", bool) == L("b", T.Bool()))
    assert (L("xs", list[bool]) == L("xs", T.Array(T.Bool())))


def test_int_construction():
    i = L("i", T.Int())

    assert (i.eq(42) == quants.Eq(i, 42))
    assert (i.lt(42) == quants.Lt(i, 42))
    assert (i.le(42) == quants.Le(i, 42))
    assert (i.gt(42) == quants.Gt(i, 42))

    assert (i.add(42) == quants.Add(i, 42))
    assert (i.sub(42) == quants.Sub(i, 42))
    assert (i.mul(42) == quants.Mul(i, 42))
    assert (i.div(42) == quants.Div(i, 42))
    assert (i.mod(42) == quants.Mod(i, 42))

    j = L("j", T.Int())
    assert (i.eq(j) == quants.Eq(i, j))
    assert (i.lt(j) == quants.Lt(i, j))
    assert (i.le(j) == quants.Le(i, j))
    assert (i.gt(j) == quants.Gt(i, j))

    assert (i.add(j) == quants.Add(i, j))
    assert (i.sub(j) == quants.Sub(i, j))
    assert (i.mul(j) == quants.Mul(i, j))
    assert (i.div(j) == quants.Div(i, j))
    assert (i.mod(j) == quants.Mod(i, j))

    assert (i.add(j.add(1)) == quants.Add(i, quants.Add(j, 1)))


def test_bool_construction():
    b1 = L("b1", T.Bool())

    # TODO: once we unify Python types and LiquidExprs, boolean expressions
    # with literals can always be constant-folded down if we really want.
    assert (b1.band(True) == quants.And(b1, True))
    assert (b1.band(False) == quants.And(b1, False))
    assert (b1.bor(True) == quants.Or(b1, True))
    assert (b1.bor(False) == quants.Or(b1, False))

    b2 = L("b2", T.Bool())
    assert (b1.band(b2) == quants.And(b1, b2))
    assert (b1.bor(b2) == quants.Or(b1, b2))


def test_array_construction():
    xs = L("xs", T.Array(T.Bool()))
    assert (xs.len() == quants.ArrayLen(xs))


def test_LV_construction():
    i = L("i", T.Int())
    nat = i >= 0
    pos = i > 0