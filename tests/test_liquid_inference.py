import ast
import inspect

from solvent import parse, frontend
from solvent import syntax as syn
from solvent import V, _, Q


def assert_type(quals, expected):
    """
    A python annotatation that runs our end-to-end liquid type inference
    on a function definition and asserts that it has a particular type.
    """

    def inner(func):
        def repl():
            pyast = ast.parse(inspect.getsource(func))
            res = parse.parse(pyast)

            syn.NameGenerator.reset()
            assert str(frontend.check(res, quals, False)) == expected

        repl.__name__ = func.__name__

        return repl

    return inner


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
    ],
    "(x:int, y:int) -> {int | y <= V and x <= V}",
)
def test_max(x, y):
    if x > y:
        return x
    else:
        return y


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
    ],
    "(f:(arg0:'a, arg1:'a) -> 'a, x:'a) -> 'a",
)
def test_double(f, x):
    return f(f(x, x), f(x, x))


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
    ],
    "(k:int) -> {int | k <= V and 0 <= V}",
)
def test_sum(k):
    if k <= 0:
        return 0
    else:
        return test_sum(k - 1) + k


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
        (_ >= 0).implies(((_ * (_ + 1)) // 2) == V),
    ],
    "(k:int) -> {int | k <= V and 0 <= V and k >= 0 ==> k * k + 1 // 2 == V}",
)
def test_sum_impl(k):
    if k <= 0:
        return 0
    else:
        return test_sum_impl(k - 1) + k


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
    ],
    "(n:int) -> {int | 0 <= V}",
)
def test_fib(n):
    if n <= 1:
        return 1
    else:
        return test_fib(n - 1) + test_fib(n - 2)
