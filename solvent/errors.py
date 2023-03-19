class BinopTypeMismatch(Exception):
    def __init__(self, lhs, rhs):
        super().__init__(f"Can't unify type {lhs.t} against value {rhs}")

class UnsupportedPyType(Exception):
    def __init__(self, pytype: type):
        super().__init__(f"Unsupported Python type: {pytype}")
