import sys
sys.path.append("..")

import pytest

from solvent import errors
from solvent import syntax as S
from solvent.syntax import LiquidVar as L

def test_fromPyType():
    assert(S.fromPyType(int) == S.Int())
    assert(S.fromPyType(bool) == S.Bool())
    assert(S.fromPyType(str) == S.Str())
    assert(S.fromPyType(list[str]) == S.Array(S.Str()))
    assert(S.fromPyType(list[list[str]]) == S.Array(S.Array(S.Str())))

    with pytest.raises(errors.UnsupportedPyType):
        S.fromPyType(float)
    with pytest.raises(errors.UnsupportedPyType):
        S.fromPyType(dict[str, int])
    with pytest.raises(errors.UnsupportedPyType):
        S.fromPyType(list[float])

def test_backing_python_type():
    assert(S.Int().python_type == int)

def test_liquidvar_construction():
    assert(L("i", int) == L("i", S.Int()))
    assert(L("b", bool) == L("b", S.Bool()))
    assert(L("s", str) == L("s", S.Str()))
    assert(L("xs", list[str]) == L("xs", S.Array(S.Str())))

def test_binop_construction():
    i: L = L("i", S.Int())
    S.BinOp(i, "<", 42)

    # TODO: At present, I can't figure out how to thread the python type
    # parameter through when the constructor is called this way, in contrast to
    # the version above which uses S.Int() rather than the Python type.  (See
    # the comment in the LiquidVar cstr.)  So, currently, the following
    # incorrect usage of `i` has to be a runtime error.
    i: L = L("i", int)
    with pytest.raises(errors.BinopTypeMismatch):
        S.BinOp(i, "<", "hello")
