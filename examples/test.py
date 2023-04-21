
from solvent import frontend


@frontend.check
def test_max(x, y: int):
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
