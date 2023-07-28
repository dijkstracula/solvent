from solvent import Q, Refine, V, _

from .utils import assert_type


@assert_type(
    [
        _ < V,
        V < _,
        _ <= V,
        V <= _,
        Q[0] <= V,
    ],
    "(x:int, y:int) -> {int | x <= V and y <= V}",
)
def test_max(x: Refine[int, True], y: Refine[int, True]):
    if x > y:
        return x
    else:
        return y


# @assert_type(
#     [
#         _ < V,
#         V < _,
#         _ <= V,
#         V <= _,
#         Q[0] <= V,
#     ],
#     "(f:(arg0:'a, arg1:'a) -> 'a, x:'a) -> 'a",
# )
# def test_double(f, x):
#     return f(f(x, x), f(x, x))


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
def test_sum(k: Refine[int, True]):
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
    ],
    "(k:{int | V >= 0}) -> {int | k <= V and 0 <= V}",
)
def test_sum_refine(k: Refine[int, V >= 0]):
    if k <= 0:
        return 0
    else:
        return test_sum_refine(k - 1) + k


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
def test_sum_impl(k: Refine[int, True]):
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
def test_fib(n: Refine[int, True]):
    if n <= 1:
        return 1
    else:
        return test_fib(n - 1) + test_fib(n - 2)


# @assert_type(
#     [
#         _ < V,
#         V < _,
#         _ <= V,
#         V <= _,
#         Q[0] <= V,
#     ],
#     "(n:int, b:'a, f:(arg0:{int | 0 <= V}, arg1:'a) -> 'a) -> 'a",
# )
# def test_foldn(n: Refine[int, True], b, f):
#     def loop(i, c):
#         if i < n:
#             return loop(i + 1, f(i, c))
#         else:
#             return c

#     return loop(0, b)


@assert_type([Q[0] <= V, V <= Q[0], _ <= V, V <= _], "() -> {int | 0 <= V and V <= 0}")
def test_assign_constant():
    v = 0
    return v
