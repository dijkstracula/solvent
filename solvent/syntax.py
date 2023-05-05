"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

import ast
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from solvent.position import Position


@dataclass(kw_only=True)
class Pos:
    """
    Describes things that can carry position information around
    """

    position: Position | None = None

    def ast(self, node: ast.AST):
        self.position = Position(
            lineno=node.lineno,
            end_lineno=node.end_lineno,
            col_offset=node.col_offset,
            end_col_offset=node.end_col_offset,
        )
        return self

    def pos(self, p: "Pos"):
        # if p.position is None:
        #     raise Exception(f"`{p}` had no position.")
        self.position = p.position
        return self


@dataclass
class BaseType(Pos):
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


@dataclass(kw_only=True)
class Type(Pos):
    pending_subst: Dict[str, "Expr"] = field(default_factory=dict)

    def subst(self, pairs: List[tuple[str, "Expr"]]):
        ret = deepcopy(self)
        for k, v in pairs:
            ret.pending_subst[k] = v
        return ret

    def __str__(self):
        match self:
            case HMType(base=base):
                return f"{base}"
            case RType(base=base, predicate=Conjoin([BoolLiteral(value=True)])):
                return f"{base}"
            case RType(base=base, predicate=Conjoin([])):
                return f"{base}"
            case RType(base=base, predicate=pred, pending_subst=ps):
                if len(ps) == 0:
                    return f"{{{base} | {pred}}}"
                else:
                    inner = ",".join([f"{k}->({e})" for k, e in ps.items()])
                    return f"{{{base} | {pred} [{inner}]}}"
            case ArrowType(args=args, ret=ret):
                return "({}) -> {}".format(
                    ", ".join([f"{name}:{t}" for name, t in args]), ret
                )
            case x:
                print(x)
                raise NotImplementedError

    def set_predicate(self, predicate: Predicate) -> "Type":
        match self:
            case ArrowType():
                raise NotImplementedError
            case RType(base=base, pending_subst=ps, position=pos):
                return RType(base, predicate, pending_subst=ps, position=pos)
            case x:
                raise Exception(f"`{x}` is not a Type.")


@dataclass
class HMType(Type):
    base: BaseType

    @staticmethod
    def bool():
        return HMType(Bool())

    @staticmethod
    def int():
        return HMType(Int())

    @staticmethod
    def fresh(name="t"):
        return HMType(TypeVar.fresh(name))


@dataclass
class RType(Type):
    base: BaseType
    predicate: Predicate

    @staticmethod
    def lift(base_type: BaseType):
        return RType(
            base_type, Conjoin([BoolLiteral(value=True)]), position=base_type.position
        )

    @staticmethod
    def template(base_type: BaseType):
        return RType(base_type, PredicateVar.fresh("K"), position=base_type.position)

    @staticmethod
    def bool():
        return RType(Bool(), Conjoin([BoolLiteral(value=True)]))

    @staticmethod
    def int():
        return RType(Int(), Conjoin([BoolLiteral(value=True)]))


@dataclass
class ArrowType(Type):
    args: List[tuple[str, Type]]
    ret: Type


@dataclass(kw_only=True)
class TypeAnnotation:
    typ: Type | None = None

    def annot(self, t: Type):
        self.typ = t
        return self


@dataclass
class Expr(Pos, TypeAnnotation):
    def __str__(self):
        e = ""
        match self:
            case Variable(name=x):
                e = f"{x}"
            case IntLiteral(value=v):
                e = f"{v}"
            case BoolLiteral(value=v):
                e = f"{v}"
            case ArithBinOp(lhs=l, op=op, rhs=r):
                e = f"{l} {op} {r}"
            case BoolOp(lhs=l, op=op, rhs=r):
                e = f"{l} {op} {r}"
            case Neg(expr=e):
                e = f"-({e})"
            case V():
                e = "V"
            case Star():
                e = "*"
            case Call(function_name=fn, arglist=args):
                args = [str(a) for a in args]
                e = f"{fn}({', '.join(args)})"
            case x:
                e = f"`{repr(x)}`"
        # if self.typ is not None:
        #     return f"({e} : {self.typ})"
        return e


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

    def __str__(self):
        if self.annotation is None:
            return self.name
        else:
            return f"{self.name}: {self.annotation}"


@dataclass
class Stmt(Pos, TypeAnnotation):
    def to_string(self, indent):
        align = " " * indent
        match self:
            case FunctionDef(
                name=name, body=stmts, typ=ArrowType(args=args, ret=retann)
            ):
                argstr = ", ".join([f"{x}:{t}" for x, t in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join([s.to_string(indent + 2) for s in stmts])
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"

            case FunctionDef(
                name=name, args=args, return_annotation=retann, body=stmts
            ):
                argstr = ", ".join([str(a) for a in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join([s.to_string(indent + 2) for s in stmts])
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"
            case If(test=test, body=body, orelse=orelse):
                bodystr = "\n".join([s.to_string(indent + 2) for s in body])
                elsestr = "\n".join([s.to_string(indent + 2) for s in orelse])
                res = "\n".join(
                    [
                        f"{align}if {test}:",
                        f"{bodystr}",
                        f"{align}else:",
                        f"{elsestr}",
                    ]
                )
                return res
            case Assign(name=name, value=value):
                return f"{align}{name} = {value}"
            case Return(value):
                return f"{align}return {value}"
            case x:
                return f"{align}{repr(x)}"

    def __str__(self):
        return self.to_string(0)


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
