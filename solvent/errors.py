class BinopTypeMismatch(Exception):
    def __init__(self, lhs, op, rhs):
        super().__init__(f"Can't typecheck {lhs} {op} {rhs}")

class UnsupportedPyType(Exception):
    def __init__(self, pytype):
        super().__init__(f"Unsupported Python type: {pytype}")
