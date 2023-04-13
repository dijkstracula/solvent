import ast
import itertools

from solvent import errors
from solvent.syntax.quants import EvalT

from dataclasses import dataclass
from types import GenericAlias
from typing import Any, Callable, Generic, Iterable, Literal, Optional, TypeVar, Type, Union

from solvent.syntax.types import LiquidType, from_py_type
from solvent.typechecker.unification import Constraint, CVar

# Wrappers for a tiny, tiny subset of AST nodes

PyAst = TypeVar("PyAst", bound=ast.AST, covariant=True)


HMType = Type[int] | Type[bool] | Type[list] | Type[Callable] | CVar

Env = dict["Name", Union[Type, CVar]]


def stmt_from_pyast(tree: ast.AST) -> "AstWrapper":
    if isinstance(tree, ast.FunctionDef):
        return FunctionDef.from_pyast(tree)
    if isinstance(tree, ast.Return):
        return Return.from_pyast(tree)
    if isinstance(tree, ast.Assign):
        return Assign.from_pyast(tree)
    if isinstance(tree, ast.AnnAssign):
        return AnnAssign.from_pyast(tree)
    if isinstance(tree, ast.If):
        return If.from_pyast(tree)
    return expr_from_pyast(tree)


def expr_from_pyast(tree: ast.AST) -> "Expr":
    if isinstance(tree, ast.Constant):
        return Constant.from_pyast(tree)
    if isinstance(tree, ast.Name):
        return Name.from_pyast(tree)
    if isinstance(tree, ast.BinOp):
        return ArithOp.from_pyast(tree)
    if isinstance(tree, ast.BoolOp):
        return BoolOp.from_pyast(tree)
    if isinstance(tree, ast.Compare):
        return Compare.from_pyast(tree)
    if isinstance(tree, ast.List):
        return List.from_pyast(tree)
    if isinstance(tree, ast.Subscript):
        return Subscript.from_pyast(tree)
    if isinstance(tree, ast.Call):
        return Call.from_pyast(tree)
    raise errors.UnsupportedAST(tree)


class AstWrapper(Generic[PyAst]):
    def constraints(self, env: Env) -> Iterable[Constraint]:
        raise Exception(f"{type(self)}.constraints() not implemented")


@dataclass(frozen=True)
class FunctionDef(AstWrapper[ast.FunctionDef]):
    args: list["Name"]
    body: list[AstWrapper]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "FunctionDef":
        assert isinstance(node, ast.FunctionDef)

        pyargs: ast.arguments = node.args
        if pyargs.vararg:
            raise errors.ASTError(node, "varargs not supported")
        if pyargs.kwarg:
            raise errors.ASTError(node, "kwargs not supported")
        args = []
        for arg in pyargs.args:
            aname = arg.arg
            args.append(Name(aname))
        body = [stmt_from_pyast(stmt) for stmt in node.body]

        return FunctionDef(args, body)


@dataclass(frozen=True)
class Return(AstWrapper[ast.Return]):
    val: Optional["Expr"]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Return":
        assert isinstance(node, ast.Return)
        if node.value:
            val = expr_from_pyast(node.value)
        else:
            val = None

        return Return(val)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        return []


@dataclass(frozen=True)
class AnnAssign(Generic[PyAst, EvalT], AstWrapper[ast.AnnAssign]):
    lhs: "Name"
    rhs: "Expr"
    annotation: LiquidType

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "AnnAssign":
        assert isinstance(node, ast.AnnAssign)
        if not isinstance(node.target, ast.Name):
            raise errors.MalformedAST(node.target, ast.Name)

        lhs = Name(node.target.id)
        rhs = expr_from_pyast(node.value)

        return AnnAssign(lhs, rhs, from_ast(lhs, node.annotation))


@dataclass(frozen=True)
class Assign(Generic[PyAst, EvalT], AstWrapper[ast.Assign]):
    lhs: "Name"
    rhs: "Expr"

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Assign":
        assert isinstance(node, ast.Assign)
        if not isinstance(node.targets[0], ast.Name):
            raise errors.MalformedAST(node.targets[0], ast.Name)

        lhs = Name(node.targets[0].id)
        rhs = expr_from_pyast(node.value)

        return Assign(lhs, rhs)

@dataclass(frozen=True)
class If(Generic[PyAst], AstWrapper[ast.If]):
    test: "Expr[PyAst, bool]"
    tru: list[AstWrapper]
    fls: list[AstWrapper]


    @classmethod
    def from_pyast(cls, node: ast.AST) -> "If":
        assert isinstance(node, ast.If)
        test = expr_from_pyast(node.test)

        # TODO: I'm not sure what the right thing to do with variable shadowing
        # in the environment should be.  With proper lexical scoping this wouldn't
        # be an issue, but since we "take both branches" during typechecking we kind
        # of need to unify across both arms of the branch?
        tru = [stmt_from_pyast(stmt) for stmt in node.body]
        fls = [stmt_from_pyast(stmt) for stmt in node.orelse]
        return If(test, tru, fls)

# Expressions


class Expr(Generic[PyAst, EvalT], AstWrapper[PyAst]):
    def type(self, env: Env) -> Union[Type, CVar]:
        raise Exception(f"{type(self)}.type() not implemented")


@dataclass(frozen=True)
class Constant(Expr[ast.Constant, Union[bool, int]]):
    val: Union[bool, int]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Constant":
        assert isinstance(node, ast.Constant)

        if type(node.value) not in [bool, int]:
            raise errors.UnsupportedAST(node)
        val = node.value
        return Constant(val)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        return []

    def type(self, env: Env) -> Union[Type, CVar]:
        return type(self.val)


@dataclass(frozen=True)
class Name(Expr[ast.Name, EvalT]):
    id: str

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Name":
        assert isinstance(node, ast.Name)
        return Name(node.id)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        return []

    def type(self, env: Env) -> Union[Type, CVar]:
        return env[self]


@dataclass(frozen=True)
class Call(Generic[PyAst, EvalT], Expr[ast.Call, EvalT]):
    fn_name: str
    args: list[Expr[PyAst, EvalT]]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Call":
        assert isinstance(node, ast.Call)
        #TODO


@dataclass(frozen=True)
class ArithOp(Expr[ast.BinOp, int]):
    lhs: Expr
    op: Any # TODO
    rhs: Expr

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "ArithOp":
        assert isinstance(node, ast.BinOp)
        lhs = expr_from_pyast(node.left)
        rhs = expr_from_pyast(node.right)

        ops = [ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Mod]
        if node.op.__class__ not in ops:
            raise errors.BinopTypeMismatch(lhs, node.op, rhs)
        return ArithOp(lhs, node.op, rhs)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.lhs.constraints(env):
            yield c
        yield Constraint(self.type(env), self.lhs.type(env))

        for c in self.rhs.constraints(env):
            yield c
        yield Constraint(self.type(env), self.rhs.type(env))

    def type(self, env: Env) -> Union[Type, CVar]:
        return int  # TODO: array concat


@dataclass(frozen=True)
class BoolOp(Generic[PyAst], Expr[ast.BoolOp, bool]):
    reified_ast_type = ast.BoolOp
    subs: tuple[Expr[PyAst, bool], ...]
    op: Literal["Or"] | Literal["And"]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "BoolOp":
        assert isinstance(node, ast.BoolOp)
        subs = [expr_from_pyast(e) for e in node.values]

        opname = node.op.__class__.__name__
        if opname != "Or" and opname != "And":
            raise errors.BinopTypeMismatch(subs[0], node.op, subs[1])
        return BoolOp(tuple(subs), opname)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for sub in self.subs:
            for c in sub.constraints(env):
                yield c
            yield Constraint(self.type(env), sub.type(env))

    def type(self, env: Env) -> Union[Type, CVar]:
        return bool


@dataclass(frozen=True)
class Compare(Generic[PyAst], Expr[ast.Compare, bool]):
    lhs: Expr[PyAst, bool]
    op: Any  # TODO
    rhs: Expr[PyAst, bool]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Compare":
        assert isinstance(node, ast.Compare)
        if len(node.ops) != 1:
            raise errors.UnsupportedAST(node)
        if len(node.comparators) != 1:
            raise errors.UnsupportedAST(node)

        ops = [ast.Lt, ast.LtE, ast.Eq, ast.NotEq, ast.Gt, ast.GtE]
        op = node.ops[0]
        if op.__class__ not in ops:
            raise errors.BinopTypeMismatch(node.left, op, node.comparators[0])

        lhs = expr_from_pyast(node.left)
        rhs = expr_from_pyast(node.comparators[0])

        return Compare(lhs, op, rhs)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.lhs.constraints(env):
            yield c
        for c in self.rhs.constraints(env):
            yield c
        yield Constraint(self.lhs.type(env), self.rhs.type(env));

    def type(self, env: Env) -> Union[Type, CVar]:
        return bool


@dataclass(frozen=True)
class List(Generic[PyAst, EvalT], Expr[ast.List, EvalT]):
    elements: tuple[Expr[PyAst, EvalT], ...]
    empty_list_cvar = CVar.next()  # Only used if a list is polymorphic

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "List":
        assert isinstance(node, ast.List)
        if node.ctx.__class__ == ast.Store:
            raise errors.ASTError(node, "Can't use a list as an lval")
        elements = tuple([expr_from_pyast(subtree) for subtree in node.elts])
        return List(elements)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for e in self.elements:
            for c in e.constraints(env):
                yield c

        deduped_pairs = set()
        for e1, e2 in itertools.combinations(self.elements, 2):
            deduped_pairs.add(Constraint(e1.type(env), e2.type(env)))
        for c in deduped_pairs:
            yield c

    def type(self, env: Env) -> HMType:
        # An empty list needs to be polymorphic, I guess?
        if len(self.elements) > 0:
            return list[self.elements[0].type(env)]  # type: ignore
        else:
            return list[self.empty_list_cvar] # type: ignore


@dataclass(frozen=True)
class Subscript(Generic[PyAst, EvalT], Expr[ast.Subscript, EvalT]):
    arr: Expr[PyAst, list[EvalT]]
    idx: Expr[PyAst, int]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Subscript":
        assert(isinstance(node, ast.Subscript))
        if isinstance(node.slice, ast.Slice):
            raise errors.ASTError(node, "Can only extract a scalar from a list")
        arr = expr_from_pyast(node.value)
        idx = expr_from_pyast(node.slice)
        return Subscript(arr, idx)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.arr.constraints(env):
            yield c
        yield Constraint(int, self.idx.type(env))

    def type(self, env: Env) -> HMType:
        at = self.arr.type(env)
        assert isinstance(at, GenericAlias)
        return at.__args__[0]


def from_ast(var: Name, t: ast.AST) -> LiquidType:
    if isinstance(t, ast.Name):
        if t.id in ["int", "bool", "list"]:
            # A simple monomorphic type literal
            blob = ast.unparse(t)
            return from_py_type(eval(blob))  # Yee haw!
        # TODO: if it isn't, then it feels like the Name could be an in-scope variable.
    elif isinstance(t, ast.Subscript):
        if t.value.id == "list":
            # A polymorphic list
            blob = ast.unparse(t)
            return from_py_type(eval(blob))  # Yee haw!
    elif isinstance(t, ast.Call):
        # TODO: Hopefuly this is a call to a liquid type constructor, eek, what do??
        expr = Call.from_pyast(t)
        raise Exception("TODO")
    # Hm, okay, I guess what we have here is a program expression
    raise errors.UnsupportedAST(t)
