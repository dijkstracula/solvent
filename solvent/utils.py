from inspect import getframeinfo, stack
from typing import TypeVar


def debuginfo():
    # s = stack()
    # for i in range(10):
    #     print(s[i][0])
    # print("====")
    caller = getframeinfo(stack()[3][0])
    return caller.filename, caller.lineno


T = TypeVar("T")


def default(val: T | None, *, fallback: T) -> T:
    if val is None:
        return fallback
    else:
        return val
