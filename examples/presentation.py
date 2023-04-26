from __future__ import annotations
import solvent
from solvent import V, _, Q


quals = [_ < V, V < _, _ <= V, V <= _, Q[0] <= V]


@solvent.infer(quals, debug=False)
def my_max(x, y):
    if x > y:
        return x
    else:
        return y


@solvent.infer(quals)
def double(f, x):
    return f(f(x, x), f(x, x))


@solvent.infer(quals, debug=False)
def my_sum(k):
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k
