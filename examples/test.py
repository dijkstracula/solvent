
from solvent import frontend


@frontend.check
def test_max(x: int, y: int) -> int:
    if x > y:
        return x
    else:
        return y
