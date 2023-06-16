import ast
import inspect
from typing import get_type_hints

from solvent import Refine, V, _, frontend, parse
from solvent import syntax as syn


def assert_hm(expected):
    """
    A python annotatation that runs phase 1 of type inference on a function
    definition and asserts that it has a particular type.
    """

    def inner(func):
        def repl():
            pyast = ast.parse(inspect.getsource(func))
            res = parse.Parser(get_type_hints(func, include_extras=True)).parse(pyast)

            syn.NameGenerator.reset()
            assert str(frontend.infer_base(res, False)) == expected

        repl.__name__ = func.__name__

        return repl

    return inner


@assert_hm(
    "(x:int, y:int) -> int",
)
def test_max(x, y):
    if x > y:
        return x
    else:
        return y


@assert_hm(
    "(f:(arg0:'a, arg1:'a) -> 'a, x:'a) -> 'a",
)
def test_double(f, x):
    return f(f(x, x), f(x, x))


@assert_hm(
    "(k:int) -> int",
)
def test_sum(k):
    if k <= 0:
        return 0
    else:
        return test_sum(k - 1) + k


@assert_hm("(k:int) -> int")
def test_sum_refine(k: Refine[int, V >= 0]):
    if k <= 0:
        return 0
    else:
        return test_sum_refine(k - 1) + k


@assert_hm("(k:int) -> int")
def test_sum_impl(k):
    if k <= 0:
        return 0
    else:
        return test_sum_impl(k - 1) + k


@assert_hm("(n:int) -> int")
def test_fib(n):
    if n <= 1:
        return 1
    else:
        return test_fib(n - 1) + test_fib(n - 2)


@assert_hm(
    "(n:int, b:'a, f:(arg0:int, arg1:'a) -> 'a) -> 'a",
)
def test_foldn(n, b, f):
    def loop(i, c):
        if i < n:
            return loop(i + 1, f(i, c))
        else:
            return c

    return loop(0, b)
