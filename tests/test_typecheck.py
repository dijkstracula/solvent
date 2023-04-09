import ast
import pytest
import sys

from solvent import errors
from solvent import LiquidVar as L

from solvent.syntax import types as T
from solvent.syntax import terms

sys.path.append("..")

#INC_AST: ast.FunctionDef = ast.parse('def inc(i): return i + 1').body[0]

#I = L("I", T.Int())


#def inc(n: I >= 0) -> I > 0:
#    return n + 1


#def test_inc_typecheck():
#    pass