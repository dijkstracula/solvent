import pytest
import sys

from solvent import errors
from solvent import LiquidVar as L

from solvent.syntax import types as T
from solvent.syntax import terms

sys.path.append("..")

def test_fromPyType():
    assert (T.from_py_type(int) == T.Int())
    assert (T.from_py_type(bool) == T.Bool())
    assert (T.from_py_type(str) == T.Str())
    assert (T.from_py_type(list[str]) == T.Array(T.Str()))
    assert (T.from_py_type(list[list[str]]) == T.Array(T.Array(T.Str())))

    # We can statically catch first-order invalid calls (e.g. fromPyType(float))
    # but higher-order ones have to be deferred to runtime.
    with pytest.raises(errors.UnsupportedPyType):
        T.from_py_type(list[float])


def test_backing_python_type():
    assert (T.Int().python_type == int)
    assert (T.Bool().python_type == bool)
    assert (T.Str().python_type == str)

    assert (T.Array(T.Bool()).python_type == list)


def test_liquidvar_construction():
    assert (L("i", int) == L("i", T.Int()))
    assert (L("b", bool) == L("b", T.Bool()))
    assert (L("s", str) == L("s", T.Str()))
    assert (L("xs", list[str]) == L("xs", T.Array(T.Str())))


def test_int_construction():
    i = L("i", T.Int())

    assert (i.eq(42) == terms.Eq(i, 42))
    assert (i.lt(42) == terms.Lt(i, 42))
    assert (i.le(42) == terms.Le(i, 42))
    assert (i.gt(42) == terms.Gt(i, 42))

    assert (i.add(42) == terms.Add(i, 42))
    assert (i.sub(42) == terms.Sub(i, 42))
    assert (i.mul(42) == terms.Mul(i, 42))
    assert (i.div(42) == terms.Div(i, 42))
    assert (i.mod(42) == terms.Mod(i, 42))

    j = L("j", T.Int())
    assert (i.eq(j) == terms.Eq(i, j))
    assert (i.lt(j) == terms.Lt(i, j))
    assert (i.le(j) == terms.Le(i, j))
    assert (i.gt(j) == terms.Gt(i, j))

    assert (i.add(j) == terms.Add(i, j))
    assert (i.sub(j) == terms.Sub(i, j))
    assert (i.mul(j) == terms.Mul(i, j))
    assert (i.div(j) == terms.Div(i, j))
    assert (i.mod(j) == terms.Mod(i, j))

    assert (i.add(j.add(1)) == terms.Add(i, terms.Add(j, 1)))


def test_bool_construction():
    b1 = L("b1", T.Bool())

    # TODO: once we unify Python types and LiquidExprs, boolean expressions
    # with literals can always be constant-folded down if we really want.
    assert (b1.band(True) == terms.And(b1, True))
    assert (b1.band(False) == terms.And(b1, False))
    assert (b1.bor(True) == terms.Or(b1, True))
    assert (b1.bor(False) == terms.Or(b1, False))

    b2 = L("b2", T.Bool())
    assert (b1.band(b2) == terms.And(b1, b2))
    assert (b1.bor(b2) == terms.Or(b1, b2))


def test_array_construction():
    xs = L("xs", T.Array(T.Str()))
    assert (xs.len() == terms.ArrayLen(xs))
