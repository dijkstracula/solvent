import ast
import copy

from solvent import errors
from solvent.syntax.terms import EvalT, Predicate

from dataclasses import dataclass
from typing import Generic, Optional, TypeVar, Type, Union

# Wrappers for a tiny, tiny subset of AST nodes

PyAst = TypeVar("PyAst", bound=ast.AST, covariant=True)

AstVals = Union["Constant", "Name"] # TODO: no lambdas, for sure, right; else FunctionDefs too?

Env = set[str]


def stmt_from_ast(tree: ast.AST) -> "AstWrapper":
    if isinstance(tree, ast.FunctionDef):
        return FunctionDef(tree)
    if isinstance(tree, ast.Return):
        return Return(tree)
    if isinstance(tree, ast.Assign):
        return Assign(tree)
    if isinstance(tree, ast.AnnAssign):
        raise Exception("TODO")
    if isinstance(tree, ast.If):
        return If(tree)
    return expr_from_ast(tree)


def expr_from_ast(tree: ast.AST) -> "Expr":
    if isinstance(tree, ast.Constant):
        return Constant(tree)
    if isinstance(tree, ast.Name):
        return Name(tree)
    if isinstance(tree, ast.BinOp):
        return ArithOp(tree)
    if isinstance(tree, ast.BoolOp):
        return BoolOp(tree)
    if isinstance(tree, ast.Compare):
        return Compare(tree)
    if isinstance(tree, ast.List):
        return List(tree)
    if isinstance(tree, ast.Call):
        return Call(tree)
    raise errors.UnsupportedAST(tree)


class AstWrapper(Generic[PyAst]):
    reified_ast_type: Type

    node: PyAst
    # base_type: Optional[Type[PyT]] = None # TODO: datatype for typevar constraint?
    liquid_type: Optional[Predicate] = None

    def __init__(self, node):
        if not isinstance(node, self.reified_ast_type):
            raise errors.MalformedAST(node, self.reified_ast_type)
        self.node = node


@dataclass(init=False)
class FunctionDef(AstWrapper[ast.FunctionDef]):
    reified_ast_type = ast.FunctionDef
    args: list["Name"]
    body: list[AstWrapper]

    def __init__(self, node: ast.AST):
        super().__init__(node)

        args: ast.arguments = self.node.args
        if args.vararg:
            raise errors.ASTError(self.node, "varargs not supported")
        if args.kwarg:
            raise errors.ASTError(self.node, "kwargs not supported")
        self.args = []
        for arg in args.args:
            aname = arg.arg
            self.args.append(Name(ast.Name(aname, ast.Load())))
        self.body = [stmt_from_ast(stmt) for stmt in self.node.body]



@dataclass(init=False)
class Return(AstWrapper[ast.Return]):
    reified_ast_type = ast.Return
    val: Optional["Expr"]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        if self.node.value:
            self.val = expr_from_ast(self.node.value)
        else:
            self.val = None


@dataclass(init=False)
class Assign(Generic[PyAst, EvalT], AstWrapper[ast.Assign]):
    reified_ast_type = ast.Assign
    lhs: "Name"
    rhs: "Expr"

    def __init__(self, node: ast.AST):
        super().__init__(node)
        if not isinstance(self.node.targets[0], ast.Name):
            raise errors.MalformedAST(self.node.targets[0], ast.Name)

        self.lhs = Name(self.node.targets[0])
        self.rhs = expr_from_ast(self.node.value)


@dataclass(init=False)
class AnnAssign(AstWrapper[ast.Assign]):
    pass


@dataclass(init=False)
class If(Generic[PyAst], AstWrapper[ast.If]):
    reified_ast_type = ast.If

    test: "Expr[PyAst, bool]"
    tru: list[AstWrapper]
    fls: list[AstWrapper]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        test = expr_from_ast(self.node.test)
        self.test = test

        # TODO: I'm not sure what the right thing to do with variable shadowing
        # in the environment should be.  With proper lexical scoping this wouldn't
        # be an issue, but since we "take both branches" during typechecking we kind
        # of need to unify across both arms of the branch?
        self.tru = [stmt_from_ast(stmt) for stmt in self.node.body]
        self.fls = [stmt_from_ast(stmt) for stmt in self.node.orelse]

@dataclass(init=False)
class Call(Generic[PyAst, EvalT], AstWrapper[ast.Call]):
    reified_ast_type = ast.Call
    fn_name: str
    args: list["Expr[PyAst, EvalT]"]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        #TODO

# Expressions


class Expr(Generic[PyAst, EvalT], AstWrapper[PyAst]):
    pass


@dataclass(init=False)
class Constant(Expr[ast.Constant, Union[bool, int]]):
    reified_ast_type = ast.Constant

    val: Union[bool, int]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        if type(self.node.value) not in [bool, int]:
            raise errors.UnsupportedAST(self.node)
        self.val = self.node.value


@dataclass(init=False)
class Name(Expr[ast.Name, EvalT]):
    reified_ast_type = ast.Name
    id: str

    def __init__(self, node: ast.AST):
        super().__init__(node)
        self.id = self.node.id


@dataclass(init=False)
class ArithOp(Expr[ast.BinOp, int]):
    reified_ast_type = ast.BinOp
    lhs: Expr
    rhs: Expr

    def __init__(self, node: ast.AST):
        super().__init__(node)
        self.lhs = expr_from_ast(self.node.left)
        self.rhs = expr_from_ast(self.node.right)

        ops = [ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Mod]
        if self.node.op.__class__ not in ops:
            raise errors.BinopTypeMismatch(self.lhs, self.node.op, self.rhs)


@dataclass(init=False)
class BoolOp(Expr[ast.BoolOp, bool]):
    reified_ast_type = ast.BoolOp
    subs = list[Expr[PyAst, bool]]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        self.subs = [expr_from_ast(e) for e in self.node.values]

        ops = [ast.Or, ast.And]
        if self.node.op.__class__ not in ops:
            raise errors.BinopTypeMismatch(self.subs[0], self.node.op, self.subs[1])


@dataclass(init=False)
class Compare(Generic[PyAst], Expr[ast.Compare, bool]):
    reified_ast_type = ast.Compare

    lhs: Expr[PyAst, bool]
    rhs: Expr[PyAst, bool]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        if len(self.node.ops) != 1:
            raise errors.UnsupportedAST(self.node)
        if len(self.node.comparators) != 1:
            raise errors.UnsupportedAST(self.node)

        ops = [ast.Lt, ast.LtE, ast.Eq, ast.NotEq, ast.Gt, ast.GtE]
        if self.node.ops[0].__class__ not in ops:
            raise errors.BinopTypeMismatch(self.node.left, self.node.ops[0], self.node.comparators[0])

        self.lhs = expr_from_ast(self.node.left)
        self.rhs = expr_from_ast(self.node.comparators[0])


@dataclass(init=False)
class List(Generic[PyAst, EvalT], Expr[ast.List, EvalT]):
    reified_ast_type = ast.List

    elements: list[Expr[PyAst, EvalT]]

    def __init__(self, node: ast.AST):
        super().__init__(node)
        if self.node.ctx.__class__ == ast.Store:
            raise errors.ASTError(self.node, "Can't use a list as an lval")
        self.elements = [expr_from_ast(subtree) for subtree in self.node.elts]