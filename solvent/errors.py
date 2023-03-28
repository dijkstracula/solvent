import ast


class UnaryTypeMismatch(Exception):
    def __init__(self, lhs, op):
        super().__init__(f"Can't typecheck {type(op).__name__}({lhs})")


class BinopTypeMismatch(Exception):
    def __init__(self, lhs, op, rhs):
        super().__init__(f"Can't typecheck {type(op).__name__}({lhs} {rhs})")


class UnsupportedPyType(Exception):
    def __init__(self, pytype):
        super().__init__(f"Unsupported Python type: {pytype}")


class MalformedAST(Exception):
    def __init__(self, tree: ast.AST, expected):
        super().__init__(f"At line {tree.lineno}:{tree.col_offset}: expected {expected}, got {type(tree)}")

class UnsupportedAST(Exception):
    def __init__(self, tree: ast.AST):
        super().__init__(f"At line {tree.lineno}:{tree.col_offset}: unsupported value {ast.dump(tree)}")
