from solvent import V, _, Q
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
