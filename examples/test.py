from __future__ import annotations
from solvent import frontend, V


@frontend.check
def test_max(x, y):
    return x + y
    # if x > y:
    #     return x
    # else:
    #     return y


def my_sum(k):
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k
