"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

import ast
import itertools

from solvent import errors
from solvent.syntax.quants import EvalT

from dataclasses import dataclass
from types import GenericAlias
from typing import Any, Generic, Iterable, Literal, TypeVar, Type, Union

from solvent.syntax.quants import RefinementType
from solvent.typechecker.unification import Constraint, CVar, UnificationEnv as Env, unifier

PyAst = TypeVar("PyAst", bound=ast.AST, covariant=True)


@dataclass(frozen=True)
class ArrowType:
    args: list["HMType"]
    ret: "HMType"


# These are what we expect H-M typechecking to spit out.
HMType = Type[int] | Type[bool] | Type[list] | ArrowType | CVar


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

    def all_returns(self) -> Iterable["Return"]:
        """ Produces all Return leaves that this AST node contains."""
        # TODO: this feels ad-hoc.  Feels like this should be all control flow exits or something?
        return []


@dataclass(frozen=True)
class FunctionDef(AstWrapper[ast.FunctionDef]):
    args: list["Name"]
    body: list[AstWrapper]
    argtypes: list[CVar]
    rettype: CVar

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

        return FunctionDef(args, body, [CVar.next() for _ in args], CVar.next())

    def constraints(self, env: Env) -> Iterable[Constraint]:
        env = env.copy()  # New scope, new env
        for name, typ in zip(self.args, self.argtypes):
            env[name] = typ
        for stmt in self.body:
            for c in stmt.constraints(env):
                yield c
        for ret in self.all_returns():
            yield Constraint(self.rettype, ret.val.type(env))

    def type(self, env: Env) -> HMType:
        return ArrowType(self.argtypes, self.rettype)

    def all_returns(self) -> Iterable["Return"]:
        for stmt in self.body:
            for r in stmt.all_returns():
                yield r

    def unify_type(self, env: Env) -> ArrowType:
        # I wonder if this should just be type()?
        cstrs = list(self.constraints(env))
        bindings = unifier(cstrs)
        unified_args = []
        for cvar in self.argtypes:
            if cvar in bindings:
                # We found a concrete type for this typevar
                unified_args.append(bindings[cvar])
            else:
                unified_args.append(cvar)
        return ArrowType(unified_args, bindings[self.rettype])


@dataclass(frozen=True)
class Return(AstWrapper[ast.Return]):
    val: "Expr"

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "Return":
        assert isinstance(node, ast.Return)
        if not node.value:
            raise errors.ASTError(node, "Returns must return a value")
        val = expr_from_pyast(node.value)
        return Return(val)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.val.constraints(env):
            yield c

    def all_returns(self) -> Iterable["Return"]:
        return [self]


@dataclass(frozen=True)
class AnnAssign(Generic[PyAst, EvalT], AstWrapper[ast.AnnAssign]):
    lhs: "Name"
    rhs: "Expr"
    annotation: Union[RefinementType, "Expr"]

    @classmethod
    def from_pyast(cls, node: ast.AST) -> "AnnAssign":
        assert isinstance(node, ast.AnnAssign)
        if not isinstance(node.target, ast.Name):
            raise errors.MalformedAST(node.target, ast.Name)

        lhs = Name(node.target.id)
        assert node.value
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

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.test.constraints(env):
            yield c
        for stmt in self.tru:
            for c in stmt.constraints(env):
                yield c
        for stmt in self.fls:
            for c in stmt.constraints(env):
                yield c

    def all_returns(self) -> Iterable[Return]:
        for stmt in self.tru:
            for r in stmt.all_returns():
                yield r
        for stmt in self.fls:
            for r in stmt.all_returns():
                yield r


# Expressions


class Expr(Generic[PyAst, EvalT], AstWrapper[PyAst]):
    def type(self, env: Env) -> Union[Type, CVar]:
        raise Exception(f"{type(self)}.type() not implemented")

    # TODO: Rondon's thesis calls the output of this function ConstType; am I conflating things
    def ConstType(self) -> RefinementType[EvalT]:
        raise Exception(f"{type(self)}.template() not implemented")


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

    def ConstType(self) -> RefinementType[bool]:
        # return L
        pass


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

        match op.__class__.__name__:
            case "Lt":
                opName = "<"
            case "LtE":
                opName = "<="
            case "Eq":
                opName = "="
            case "NotEq":
                opName = "!="  # TODO: Not sure that this is right (presumably this becomes part of a z3 expr)
            case "Gt":
                opName = ">"
            case "GtE":
                opName = ">="

        return Compare(lhs, opName, rhs)

    def constraints(self, env: Env) -> Iterable[Constraint]:
        for c in self.lhs.constraints(env):
            yield c
        for c in self.rhs.constraints(env):
            yield c
        if self.op in ["<", "<=", ">", ">="]:
            yield Constraint(self.lhs.type(env), int)
            yield Constraint(self.rhs.type(env), int)
        else:
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


def from_ast(var: Name, t: ast.AST) -> Union[Expr, RefinementType]:
    if isinstance(t, ast.Name):
        if t.id in ["int", "bool", "list"]:
            # A simple monomorphic type literal
            blob = ast.unparse(t)
            return RefinementType(eval(blob))  # Yee haw!
        # TODO: if it isn't, then it feels like the Name could be an in-scope variable.
    elif isinstance(t, ast.Subscript):
        if t.value.id == "list":
            # A polymorphic list
            blob = ast.unparse(t)
            return RefinementType(eval(blob))  # Yee haw!
    elif isinstance(t, ast.Call):
        # TODO: Hopefuly this is a call to a liquid type constructor, eek, what do??
        _expr = Call.from_pyast(t)
        raise Exception("TODO")

    # Hm, okay, I guess what we have here is a program expression
    elif isinstance(t, ast.expr):
        return expr_from_pyast(t)

    raise errors.UnsupportedAST(t)
