"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

import ast
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional

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
            case x:
                raise NotImplementedError(x)


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

    def subst(self, pairs: Iterable[tuple[str, "Expr"]]):
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
            case Bottom():
                return "False"
            case ListType(inner_typ=inner_typ):
                return f"List[{inner_typ}]"
            case DictType():
                return "dict()"
            case DataFrameType(columns=c):
                tmp = [f"{k}: {v}" for k, v in c.items()]
                if len(tmp) > 0:
                    return f"DataFrame({tmp}, ..)"
                else:
                    return "DataFrame(..?)"
            case ObjectType(fields=fields):
                tmp = [f"{k}: {v}" for k, v in fields.items()]
                if len(tmp) > 0:
                    return f"Object{{ {tmp} }}"
                else:
                    return "Object"
            case x:
                print(type(x))
                raise Exception(x)

    def set_predicate(self, predicate: Predicate) -> "Type":
        match self:
            case ArrowType():
                raise NotImplementedError
            case RType(base=base, pending_subst=ps, position=pos):
                return RType(base, predicate, pending_subst=ps, position=pos)
            case x:
                raise Exception(f"`{x}` is not an RType.")


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


@dataclass
class ListType(Type):
    inner_typ: Type


@dataclass
class DictType(Type):
    # TODO: actually represent dictionary types
    # items: Dict[str, Type]
    pass


@dataclass
class DataFrameType(Type):
    columns: Dict[str, Type]


@dataclass
class ObjectType(Type):
    fields: Dict[str, Type]

    @staticmethod
    def series(inner_typ: Type):
        return ObjectType({"max": ArrowType([], inner_typ)})


@dataclass
class Bottom(Type):
    pass


def base_type_eq(t1: Type, t2: Type) -> bool:
    """
    Implements equality between base types.
    """

    match (t1, t2):
        case HMType(base=Int()), HMType(base=Int()):
            return True
        case HMType(base=Bool()), HMType(base=Bool()):
            return True
        case HMType(TypeVar(name=n1)), HMType(TypeVar(name=n2)):
            return n1 == n2
        case (ArrowType(args=args1, ret=ret1), ArrowType(args=args2, ret=ret2)):
            args_eq = all(
                map(lambda a: base_type_eq(a[0][1], a[1][1]), zip(args1, args2))
            )
            return args_eq and base_type_eq(ret1, ret2)
        case RType(base=Int()), RType(base=Int()):
            return True
        case RType(base=Bool()), RType(base=Bool()):
            return True
        case RType(base=TypeVar(name=n1)), RType(base=TypeVar(name=n2)):
            return n1 == n2
        case ListType(inner_typ1), ListType(inner_typ2):
            return base_type_eq(inner_typ1, inner_typ2)
        case DataFrameType(columns=c0), DataFrameType(columns=c1):
            # two dataframes are `base_type_eq` if they have the same
            # keys and all their values are `base_type_eq`.
            return list(c0.keys()) == list(c1.keys()) and all(
                [base_type_eq(v, c1[k]) for k, v in c0.items()]
            )
        case _:
            return False


@dataclass(kw_only=True)
class TypeAnnotation:
    typ: Type = field(default_factory=Bottom)

    def annot(self, t: Type):
        self.typ = t
        return self


@dataclass
class Expr(Pos, TypeAnnotation):
    def to_string(self, include_types=False) -> str:
        match self:
            case Variable(name=x):
                return f"{x}"
            case IntLiteral(value=v):
                return f"{v}"
            case BoolLiteral(value=v):
                return f"{v}"
            case ListLiteral(elts=elts):
                inner = ", ".join([e.to_string() for e in elts])
                if include_types:
                    return f"([{inner}] : {self.typ})"
                else:
                    return f"[{inner}]"
            case DictLit():
                return "{<opaque>}"
            case DataFrameLit():
                return "DataFrame(<opaque>)"
            case Subscript(value=v, idx=e):
                return f"{v}[{e}]"
            case Neg(expr=e):
                return f"-({e.to_string(include_types)})"
            case ArithBinOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string(include_types)} {op} {r.to_string(include_types)}"
            case BoolOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string(include_types)} {op} {r.to_string(include_types)}"
            case Not(expr=e):
                return f"!({e.to_string(include_types)})"
            case V():
                return "V"
            case Star():
                return "*"
            case Call(function_name=fn, arglist=args):
                args = [a.to_string(include_types) for a in args]
                return f"{fn}({', '.join(args)})"
            case GetAttr(name=obj, attr=attr):
                return f"{obj.to_string(include_types)}.{attr}"
            case x:
                return f"`{repr(x)}`"

    def __str__(self):
        return self.to_string()


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
class DataFrameLit(Expr):
    pass


@dataclass
class DictLit(Expr):
    """TODO: add real information to dictionaries."""

    pass


@dataclass
class Neg(Expr):
    expr: Expr


@dataclass
class ArithBinOp(Expr):
    lhs: Expr
    op: str
    rhs: Expr


@dataclass
class BoolLiteral(Expr):
    value: bool


@dataclass
class ListLiteral(Expr):
    elts: List[Expr]


@dataclass
class Subscript(Expr):
    value: Expr
    idx: Expr


@dataclass
class BoolOp(Expr):
    lhs: Expr
    op: Any
    rhs: Expr


@dataclass
class Not(Expr):
    expr: Expr


@dataclass
class Call(Expr):
    function_name: Expr
    arglist: List[Expr]


@dataclass
class GetAttr(Expr):
    name: Expr
    attr: str


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
    def to_string(self, indent=0, include_types=False):
        align = " " * indent
        match self:
            case FunctionDef(
                name=name, body=stmts, typ=ArrowType(args=args, ret=retann)
            ) if include_types:
                argstr = ", ".join([f"{x}:{t}" for x, t in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join(
                    [s.to_string(indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"

            case FunctionDef(
                name=name, args=args, return_annotation=retann, body=stmts
            ):
                argstr = ", ".join([str(a) for a in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join(
                    [s.to_string(indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"
            case If(test=test, body=body, orelse=orelse):
                bodystr = "\n".join(
                    [s.to_string(indent + 2, include_types) for s in body]
                )
                elsestr = "\n".join(
                    [s.to_string(indent + 2, include_types) for s in orelse]
                )
                typstr0 = "(" if include_types else ""
                typstr1 = f") : {self.typ}" if include_types else ""
                res = "\n".join(
                    [
                        f"{align}{typstr0}if {test.to_string(include_types)}:",
                        f"{bodystr}",
                        f"{align}else:",
                        f"{elsestr}{typstr1}",
                    ]
                )
                return res
            case Assign(name=name, value=value):
                typann = f": {self.typ}" if include_types else ""
                return f"{align}{name}{typann} = {value.to_string(False)}"
            case Return(value):
                return f"{align}return {value.to_string(include_types)}"
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
