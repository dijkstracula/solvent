from __future__ import annotations
from solvent import frontend, V


# @frontend.infer_base_constraints
def my_max(x, y):
    if x > y:
        return x
    else:
        return y


def my_sum(k):
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k


@frontend.infer_base
def double(f, x):
    return f(f(x, x), f(x, x))
