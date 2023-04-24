from __future__ import annotations
import solvent
from solvent import V
from typing import Callable


@solvent.infer(["* <= V", "V <= *"])
def my_max(x, y):
    if x > y:
        return x
    else:
        return y


# @frontend.infer_base
def my_sum(k):
    if k < 0:
        return 0
    else:
        return my_sum(k - 1) + k


# @frontend.infer_base_constraints
def double(f, x):
    return f(f(x, x), f(x, x))
