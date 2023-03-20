import sys
sys.path.append("..")

import pytest

from solvent import errors
from solvent.syntax import types as T

from solvent.syntax import terms
from solvent.syntax.terms import LiquidVar as L

def test_fromPyType():
    assert(T.fromPyType(int) == T.Int())
    assert(T.fromPyType(bool) == T.Bool())
    assert(T.fromPyType(str) == T.Str())
    assert(T.fromPyType(list[str]) == T.Array(T.Str()))
    assert(T.fromPyType(list[list[str]]) == T.Array(T.Array(T.Str())))

    # We can statically catch first-order invalid calls (e.g. fromPyType(float))
    # but higher-order ones have to be deferred to runtime.
    with pytest.raises(errors.UnsupportedPyType):
        T.fromPyType(list[float])

def test_backing_python_type():
    assert(T.Int().python_type == int)

def test_liquidvar_construction():
    assert(L("i", int) == L("i", T.Int()))
    assert(L("b", bool) == L("b", T.Bool()))
    assert(L("s", str) == L("s", T.Str()))
    assert(L("xs", list[str]) == L("xs", T.Array(T.Str())))

def test_binop_construction():
    i = L("i", T.Int())
    print(i)
    terms.BinOp(i, "<", 42)

