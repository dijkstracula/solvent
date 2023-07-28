from inspect import getframeinfo, stack
from typing import Any, Dict, TypeVar


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


def unwrap(val: T | None) -> T:
    if val is None:
        raise Exception()
    return val


def dict_fmt(d: Dict[Any, Any]) -> str:
    if len(d) == 0:
        return "{}"

    ret = "{\n"
    for k, v in d.items():
        ret += f"  {k}: {v}\n"
    ret += "}"
    return ret
