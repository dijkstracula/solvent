"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

from dataclasses import dataclass
from typing import Optional, List, Any


@dataclass
class BaseType:
    def __str__(self):
        match self:
            case Int():
                return "int"
            case Bool():
                return "bool"
            case Unit():
                return "unit"
            case TypeVar(name=n):
                return f"'{n}"
            case x:
                print(x)
                raise NotImplementedError


@dataclass
class Unit(BaseType):
    pass


@dataclass
class Int(BaseType):
    pass


@dataclass
class Bool(BaseType):
    pass


class NameGenerator:
    names: dict[str, int] = dict()

    @staticmethod
    def fresh(name):
        if name in NameGenerator.names:
            count = NameGenerator.names[name]
            NameGenerator.names[name] += 1
        else:
            count = 0
            NameGenerator.names[name] = 1

        return f"{name}{count}"


@dataclass
class TypeVar(BaseType):
    name: str

    @staticmethod
    def fresh(name="t"):
        return TypeVar(NameGenerator.fresh(name))


@dataclass
class Predicate:
    def __str__(self):
        match self:
            case Conjoin(preds):
                return " and ".join([str(p) for p in preds])
            case PredicateVar(name=n):
                return f"'{n}"


@dataclass
class Conjoin(Predicate):
    conjuncts: List["Expr"]


@dataclass
class PredicateVar(Predicate):
    name: str

    @staticmethod
    def fresh(name="K"):
        return PredicateVar(NameGenerator.fresh(name))


@dataclass
class Type:
    def __str__(self):
        match self:
            case RType(base=base, predicate=Conjoin([BoolLiteral(value=True)])):
                return f"{base}"
            case RType(base=base, predicate=pred):
                return f"{{ {base} | {pred} }}"
            case ArrowType(args=args, ret=ret):
                return "({}) -> {}".format(", ".join([str(a) for a in args]), ret)
            case x:
                print(x)
                raise NotImplementedError


@dataclass
class RType(Type):
    base: BaseType
    predicate: Predicate

    @staticmethod
    def lift(base_type: BaseType):
        return RType(base=base_type, predicate=Conjoin([BoolLiteral(value=True)]))

    @staticmethod
    def template(base_type: BaseType):
        return RType(base=base_type, predicate=PredicateVar.fresh("K"))

    @staticmethod
    def bool():
        return RType(base=Bool(), predicate=Conjoin([BoolLiteral(value=True)]))

    @staticmethod
    def int():
        return RType(base=Int(), predicate=Conjoin([BoolLiteral(value=True)]))


@dataclass
class ArrowType(Type):
    args: List[Type]
    ret: Type


@dataclass
class Expr:
    def __str__(self):
        match self:
            case Variable(name=x):
                return f"{x}"
            case IntLiteral(value=v):
                return f"{v}"
            case BoolLiteral(value=v):
                return f"{v}"
            case ArithBinOp(lhs=l, op=op, rhs=r):
                return f"{l} {op} {r}"
            case BoolOp(lhs=l, op=op, rhs=r):
                return f"{l} {op} {r}"
            case Neg(expr=e):
                return f"-({e})"
            case V():
                return "V"
            case Call(function_name=fn, arglist=args):
                args = [str(a) for a in args]
                return f"{fn}({', '.join(args)})"
            case x:
                return f"`{x}`"


@dataclass
class V(Expr):
    """Represents the special v variable in a refinement."""

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
class Neg(Expr):
    expr: Expr


@dataclass
class Call(Expr):
    function_name: Expr
    arglist: List[Expr]


@dataclass
class Argument:
    name: str
    annotation: Optional[Type]


@dataclass
class Stmt:
    pass


@dataclass
class FunctionDef(Stmt):
    name: str
    args: List[Argument]
    return_annotation: Optional[Type]
    body: List[Stmt]


@dataclass
class If(Stmt):
    test: Expr
    body: List[Stmt]
    orelse: List[Stmt]


@dataclass
class Return(Stmt):
    value: Expr
