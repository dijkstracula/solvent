from inspect import getframeinfo, stack


def debuginfo():
    # s = stack()
    # for i in range(10):
    #     print(s[i][0])
    # print("====")
    caller = getframeinfo(stack()[3][0])
    return caller.filename, caller.lineno
