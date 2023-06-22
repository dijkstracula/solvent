import pandas as pd

from solvent import Q, V, _
from tests.utils import assert_type

quals = [
    _ < V,
    V < _,
    _ <= V,
    V <= _,
    Q[0] <= V,
    V <= Q[0],
]


@assert_type(quals, "() -> Object{ max: () -> int, data: List[int] }")
def test_series_cstr():
    s = pd.Series([-1, 2, 3])
    return s


@assert_type(
    quals, "() -> Object{ max: () -> {int | 0 <= V}, data: List[{int | 0 <= V}] }"
)
def test_series_cstr_pos():
    s = pd.Series([1, 2, 3])
    return s


@assert_type(quals, "() -> {int | 0 <= V}")
def test_series_max():
    s = pd.Series([1, 2, 3])
    return s.max()


@assert_type(quals, "() -> {int | 0 <= V}")
def test_series_max_div_pos():
    s = pd.Series([1, 2, 3])
    return s.max() / 1  # type: ignore


@assert_type(quals, "() -> {int | V <= 0}")
def test_series_max_div_neg():
    s = pd.Series([1, 2, 3])
    return s.max() / -1  # type: ignore


@assert_type(
    quals, "() -> Object{ max: () -> {int | 0 <= V}, data: List[{int | 0 <= V}] }"
)
def test_series_div():
    s = pd.Series([1, 2, 3])
    return s / 2


@assert_type(
    quals, "() -> Object{ max: () -> {int | V <= 0}, data: List[{int | V <= 0}] }"
)
def test_series_div_neg():
    s = pd.Series([1, 2, 3])
    return s / -2
