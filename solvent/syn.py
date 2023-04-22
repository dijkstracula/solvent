"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

from dataclasses import dataclass
from typing import Optional, List, Any

# ==========
# Base types
# ==========


@dataclass
class BaseType:
    pass


@dataclass
class Unit(BaseType):
    pass


@dataclass
class Int(BaseType):
    pass


@dataclass
class Bool(BaseType):
    pass


_cvar_counter = 0


@dataclass
class Type:
    pass


@dataclass
class TypeVar(Type):
    name: str

    @staticmethod
    def fresh(name=""):
        global _cvar_counter
        _cvar_counter += 1
        return TypeVar(f"{name}{_cvar_counter}")


@dataclass
class RType(Type):
    value: BaseType
    predicate: "Expr"

    @staticmethod
    def base(base_type: BaseType):
        return RType(value=base_type, predicate=BoolLiteral(value=True))

    @staticmethod
    def bool():
        return RType(value=Bool(), predicate=BoolLiteral(value=True))

    @staticmethod
    def int():
        return RType(value=Int(), predicate=BoolLiteral(value=True))


@dataclass
class ArrowType(Type):
    args: List[Type]
    ret: Type


@dataclass
class Expr:
    pass


@dataclass
class Variable(Expr):
    name: str


@dataclass
class IntLiteral(Expr):
    value: int


@dataclass
class ArithBinOp(Expr):
    lhs: Expr
    op: str
    rhs: Expr


@dataclass
class BoolLiteral(Expr):
    value: bool


@dataclass
class BoolOp(Expr):
    lhs: Expr
    op: Any
    rhs: Expr


@dataclass
class Call(Expr):
    function_name: str
    arglist: List[Expr]


@dataclass
class Argument:
    name: str
    annotation: Optional[str]


@dataclass
class Stmt:
    pass


@dataclass
class FunctionDef(Stmt):
    name: str
    args: List[Argument]
    return_annotation: Optional[str]
    body: List[Stmt]


@dataclass
class If(Stmt):
    test: Expr
    body: List[Stmt]
    orelse: List[Stmt]


@dataclass
class Return(Stmt):
    value: Expr
