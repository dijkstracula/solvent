from __future__ import annotations
import solvent
from solvent import V, _, Q, Refine

quals = [
    _ < V,
    V < _,
    _ <= V,
    V <= _,
    Q[0] <= V,
]


@solvent.infer(quals)
def bogus(x: bool) -> int:
    return x + 1


@solvent.infer(quals)
def my_max(x, y):
    if x > y:
        return x
    else:
        return y


@solvent.infer(quals)
def double(f, x: Refine[int, V < 0]):
    return f(f(x, x), f(x, x))


@solvent.infer(quals + [(_ >= 0).implies(((_ * (_ + 1)) // 2) == V)])
def my_sum(k):
    if k <= 0:
        return 0
    else:
        return my_sum(k - 1) + k


@solvent.infer(quals)
def fib(n):
    if n <= 1:
        return 1
    else:
        return fib(n - 1) + fib(n - 2)
