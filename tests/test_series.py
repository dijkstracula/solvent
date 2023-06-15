from solvent import V, _, Q, Refine
from tests.utils import assert_type

import pandas as pd

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

@assert_type(quals, "() -> Object{ max: () -> {int | 0 <= V}, data: List[{int | 0 <= V}] }")
def test_series_cstr_pos():
    s = pd.Series([1, 2, 3])
    return s


@assert_type(quals, "() -> {int | 0 <= V}")
def test_series_max():
    s = pd.Series([1, 2, 3])
    return s
