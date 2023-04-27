"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

from dataclasses import dataclass
from typing import Optional, List, Any, Dict
from copy import deepcopy


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
    """
    A unified name generator. Keeps separate counts
    for every name used so that we generally have lower numbers
    and different users can never generate the same name.
    """

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

    @staticmethod
    def reset():
        NameGenerator.names = dict()


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
                if len(preds) == 0:
                    return "True"
                else:
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
    # pending_subst: List[tuple[str, "Expr"]]
    pending_subst: Dict[str, "Expr"]

    def subst(self, pairs: List[tuple[str, "Expr"]]):
        ret = deepcopy(self)
        for k, v in pairs:
            ret.pending_subst[k] = v
        return ret

    def __str__(self):
        match self:
            case RType(base=base, predicate=Conjoin([BoolLiteral(value=True)])):
                return f"{base}"
            case RType(base=base, predicate=Conjoin([])):
                return f"{base}"
            # case RType(base=base, predicate=pred, pending_subst={}):
            #     return f"{{{base} | {pred}}}"
            case RType(base=base, predicate=pred, pending_subst=ps):
                ps_str = ",".join([f"{k}->({e})" for k, e in ps.items()])
                return f"{{{base} | {pred} [{ps_str}]}}"
            case ArrowType(args=args, ret=ret):
                return "({}) -> {}".format(
                    ", ".join([f"{name}:{t}" for name, t in args]), ret
                )
            case x:
                print(x)
                raise NotImplementedError


@dataclass
class RType(Type):
    base: BaseType
    predicate: Predicate

    @staticmethod
    def lift(base_type: BaseType):
        return RType({}, base_type, Conjoin([BoolLiteral(value=True)]))

    @staticmethod
    def template(base_type: BaseType):
        return RType({}, base_type, PredicateVar.fresh("K"))

    @staticmethod
    def bool():
        return RType({}, Bool(), Conjoin([BoolLiteral(value=True)]))

    @staticmethod
    def int():
        return RType({}, Int(), Conjoin([BoolLiteral(value=True)]))


@dataclass
class ArrowType(Type):
    args: List[tuple[str, Type]]
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
            case Star():
                return "*"
            case Call(function_name=fn, arglist=args):
                args = [str(a) for a in args]
                return f"{fn}({', '.join(args)})"
            case x:
                return f"`{repr(x)}`"


@dataclass
class V(Expr):
    """Represents the special v variable in a refinement."""

    pass


@dataclass
class Star(Expr):
    """Represents the special star variable in a qualifer."""

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
class Assign(Stmt):
    name: str
    value: Expr


@dataclass
class Return(Stmt):
    value: Expr
