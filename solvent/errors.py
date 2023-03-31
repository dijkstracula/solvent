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


# AST errors


class ASTError(Exception):
    def __init__(self, tree: ast.AST, msg: str):
        super().__init__(f"At line {tree.lineno}:{tree.col_offset}: {msg}")


class UnknownNameError(ASTError):
    def __init__(self, name: ast.Name):
        super().__init__(name, f"Name {name.id} not in scope")


class MalformedAST(ASTError):
    def __init__(self, tree: ast.AST, expected):
        super().__init__(tree, f"expected {expected}, got {type(tree)}")


class UnsupportedAST(ASTError):
    def __init__(self, tree: ast.AST):
        super().__init__(tree, f"unsupported value {ast.dump(tree)}")
