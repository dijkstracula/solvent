from typing import List

from solvent import Q, Refine, V, _
from tests.utils import assert_type

quals = [
    _ < V,
    V < _,
    _ <= V,
    V <= _,
    Q[0] <= V,
    V <= Q[0],
]


@assert_type([Q[0] <= V, V <= Q[0]], "() -> List[{int | 0 <= V}]")
def test_list_literal():
    return [1, 1, 1, 1]


@assert_type([Q[0] <= V, V <= Q[0]], "() -> List[int]")
def test_list_append():
    return [0] + [1, -1]


@assert_type([Q[0] <= V, V <= Q[0]], "() -> List[{int | 0 <= V}]")
def test_list_append2():
    return [0] + [1]


@assert_type([_ <= V, V <= _], "(n:int) -> List[{int | V <= n}]")
def test_list(n: Refine[int, True]) -> List[int]:
    if n <= 0:
        return []
    else:
        return [n] + test_list(n - 1)
