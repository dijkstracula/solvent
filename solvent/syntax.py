"""
The internal DSL that we use for typechecking.  At parse time, the Python AST
is transformed into this more manageable sublanguage.
"""

import ast
from copy import deepcopy
from dataclasses import dataclass, field
from logging import debug
from typing import Any, Dict, Iterable, List, Optional, Self

from ansi.color import fg, fx

from solvent.position import Position
from solvent.utils import default, unwrap


class ID:
    next_id: int = 0

    @classmethod
    def next(cls):
        i = cls.next_id
        cls.next_id += 1
        return i


@dataclass(kw_only=True)
class Node:
    node_id: int = field(default_factory=ID.next)


@dataclass(kw_only=True)
class Pos:
    """
    Describes things that can carry position information around
    """

    position: Position = field(default_factory=Position, repr=False)

    def ast(self, node: ast.AST):
        self.position = Position(
            lineno=node.lineno,
            end_lineno=default(node.end_lineno, fallback=node.lineno),
            col_offset=node.col_offset,
            end_col_offset=default(node.end_col_offset, fallback=node.col_offset),
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
            case Str():
                return "str"
            case Unit():
                return "unit"
            case TypeVar(name=n):
                return f"'{n}"
            case x:
                raise NotImplementedError(x)


@dataclass
class Unit(BaseType):
    pass


@dataclass
class Int(BaseType):
    pass


@dataclass
class Bool(BaseType):
    pass


@dataclass
class Str(BaseType):
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
    pending_subst: Dict[str, "Expr"] = field(default_factory=dict, repr=False)

    def metadata(self, frm: "Type") -> Self:
        self.pending_subst = frm.pending_subst
        self.position = frm.position
        return self

    def subst(self, pairs: Iterable[tuple[str, "Expr"]]):
        ret = deepcopy(self)
        for k, v in pairs:
            ret.pending_subst[k] = v
        return ret

    def subst_typevar(self, typevar: str, tar: "Type | Predicate") -> Self:
        match self:
            case HMType(TypeVar(name=n)) if typevar == n:
                assert isinstance(tar, Type)
                return HMType(unwrap(tar.base_type())).metadata(self)
            case HMType():
                return self
            case RType(base=base, predicate=p, pending_subst=ps):
                if isinstance(base, TypeVar) and base.name == typevar:
                    assert isinstance(tar, Type)
                    base = unwrap(tar.base_type())

                if isinstance(p, PredicateVar) and p.name == typevar:
                    assert isinstance(tar, Predicate)
                    p = tar

                return RType(base, p, pending_subst=ps).metadata(self)

            case ArrowType(type_abs=abs, args=args, ret=ret):
                return ArrowType(
                    type_abs={k: abs[k] for k in abs if k != typevar},
                    args=[(x, t.subst_typevar(typevar, tar)) for x, t in args],
                    ret=ret.subst_typevar(typevar, tar),
                ).metadata(self)
            case ListType(inner_typ=inner):
                return ListType(inner.subst_typevar(typevar, tar)).metadata(self)
            case SelfType(generic_args=args):
                return SelfType([a.subst_typevar(typevar, tar) for a in args]).metadata(
                    self
                )
            case ObjectType(name=name, generic_args=args):
                return ObjectType(
                    name, [a.subst_typevar(typevar, tar) for a in args]
                ).metadata(self)
            case Class(name=name, type_abs=abs, constructor=cons, fields=fields):
                return Class(
                    name,
                    [a for a in abs if a != typevar],
                    cons.subst_typevar(name, tar),
                    {x: t.subst_typevar(name, tar) for x, t in fields.items()},
                ).metadata(self)
            case x:
                raise NotImplementedError(str(x), type(x))

    def shape(self) -> Self:
        """
        Implementation of the shape function from the paper.
        Removes a predicate from a RType.
        """

        match self:
            case ArrowType(type_abs=abs, args=args, ret=ret):
                return ArrowType(
                    type_abs=abs,
                    args=[(name, a.shape()) for name, a in args],
                    ret=ret.shape(),
                ).metadata(self)
            case RType(base=base):
                return HMType(base).metadata(self)
            case HMType():
                return self
            case ListType(inner_typ):
                return ListType(inner_typ.shape()).metadata(self)
            case Class(name=name, type_abs=abs, constructor=cons, fields=fields):
                return Class(
                    name=name,
                    type_abs=abs,
                    constructor=cons.shape(),
                    fields={name: ty.shape() for name, ty in fields.items()},
                ).metadata(self)
            case ObjectType(name=name, generic_args=args):
                return ObjectType(
                    name,
                    [a.shape() for a in args],
                ).metadata(self)
            case SelfType(generic_args=args):
                return SelfType(generic_args=[a.shape() for a in args]).metadata(self)
            case x:
                raise Exception(f"`{x}` is not a Type.")

    def base_type(self) -> BaseType | None:
        match self:
            case HMType(base=base):
                return base
            case RType(base=base):
                return base
            case _:
                return None

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
            case ArrowType(type_abs=abs, args=args, ret=ret):
                return "{}({}) -> {}".format(
                    "∀({}), ".format(", ".join(abs)) if len(abs) > 0 else "",
                    ", ".join([f"{name}:{t}" for name, t in args]),
                    ret,
                )
            case Unknown():
                return "Unknown"
            case Any():
                return "Any"
            case ListType(inner_typ=inner_typ):
                return f"List[{inner_typ}]"
            case DictType(items=items):
                names = ", ".join(map(str, items.keys()))
                return f"{{ {names} }}"
            case Class(name=name, type_abs=abs):
                arg_str = ", ".join(list(map(str, abs)))
                return f"class<{name}[{arg_str}]>"
            case ObjectType(name=name, generic_args=args):
                arg_str = ", ".join(map(str, args))
                return f"{name}[{arg_str}]"
            case SelfType(generic_args=args):
                arg_str = ", ".join(map(str, args))
                return f"Self[{arg_str}]"
            case x:
                raise Exception(x, type(x))

    def set_predicate(self, predicate: Predicate) -> "Type":
        match self:
            case ArrowType():
                raise NotImplementedError
            case RType(base=base):
                return RType(base, predicate).metadata(self)
            case HMType(base=base):
                return RType(base, predicate).metadata(self)
            case x:
                raise Exception(f"`{x}` is not an RType.")

    def resolve_name(self, new: str) -> Self:
        match self:
            case ObjectType(generic_args=args):
                return ObjectType(name=new, generic_args=args).metadata(self)
            case SelfType(generic_args=args):
                return ObjectType(name=new, generic_args=args).metadata(self)
            case Class(type_abs=abs, constructor=cons, fields=fields):
                return Class(
                    name=new, type_abs=abs, constructor=cons, fields=fields
                ).metadata(self)
            case _:
                return self


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
    def str():
        return HMType(Str())

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

    @staticmethod
    def str():
        return RType(Str(), Conjoin([BoolLiteral(value=True)]))


@dataclass
class ArrowType(Type):
    type_abs: Dict[str, str]
    args: List[tuple[str, Type]]
    ret: Type


@dataclass
class ListType(Type):
    inner_typ: Type


@dataclass
class DictType(Type):
    items: Dict[str, Type]


@dataclass
class Class(Type):
    name: str
    type_abs: List[str]
    constructor: ArrowType
    fields: Dict[str, Type] = field(default_factory=dict)


@dataclass
class ObjectType(Type):
    name: str
    generic_args: List[Type] = field(default_factory=list)


@dataclass
class SelfType(Type):
    generic_args: List[Type] = field(default_factory=list)


@dataclass
class Unknown(Type):
    pass


@dataclass
class Any(Type):
    pass


def base_type_eq(t1: Type, t2: Type) -> bool:
    """
    Implements equality between base types.
    """

    match (t1.shape(), t2.shape()):
        case HMType(TypeVar(name=n1)), HMType(TypeVar(name=n2)):
            return n1 == n2
        case HMType(base=x), HMType(base=y):
            return x == y
        case (ArrowType(args=args1, ret=ret1), ArrowType(args=args2, ret=ret2)):
            args_eq = all(
                map(lambda a: base_type_eq(a[0][1], a[1][1]), zip(args1, args2))
            )
            return args_eq and base_type_eq(ret1, ret2)
        case ListType(inner_typ1), ListType(inner_typ2):
            return base_type_eq(inner_typ1, inner_typ2)
        case ObjectType(name=n0, fields=f0), ObjectType(name=n1, fields=f1) if n0 == n1:
            return sorted(f0.keys()) == sorted(f1.keys()) and all(
                [base_type_eq(v, f1[k]) for k, v in f0.items()]
            )
        case _:
            return False


@dataclass(kw_only=True)
class TypeAnnotation:
    typ: Type = field(default_factory=Unknown)

    def annot(self, t: Type):
        self.typ = t
        return self


@dataclass
class Expr(Node, Pos):
    def to_string(
        self, types: Dict[int, Type] | None = None, include_types=False
    ) -> str:
        if types is not None:
            return self.to_string2(types, include_types)

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
                    return f"([{inner}] : [depr])"
                else:
                    return f"[{inner}]"
            case DictLit():
                return "{<opaque>}"
            case StrLiteral(value=v):
                return f'"{v}"'
            case Subscript(value=v, idx=e):
                return f"{v}[{e}]"
            case Neg(expr=e):
                return f"-({e.to_string(types, include_types)})"
            case ArithBinOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string(types, include_types)} {op} {r.to_string(types, include_types)}"
            case BoolOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string(types, include_types)} {op} {r.to_string(types, include_types)}"
            case Not(expr=e):
                return f"!({e.to_string(types, include_types)})"
            case V():
                return "V"
            case Star():
                return "*"
            case Call(function_name=fn, arglist=args):
                args = [a.to_string(types, include_types) for a in args]
                return f"{fn}({', '.join(args)})"
            case GetAttr(name=obj, attr=attr):
                return f"{obj.to_string(types, include_types)}.{attr}"
            case TypeApp(expr=e, arglist=args):
                arg_str = ", ".join([str(a) for a in args])
                return (
                    f"{e.to_string(types, include_types)}{fg.red}[{arg_str}]{fx.reset}"
                )
            case x:
                return f"`{repr(x)}`"

    def to_string2(self, types: Dict[int, Type], include_types=False) -> str:
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
                    return f"([{inner}] : {fg.yellow}{types[self.node_id]}{fx.reset})"
                else:
                    return f"[{inner}]"
            case DictLit():
                return "{<opaque>}"
            case StrLiteral(value=v):
                return f'"{v}"'
            case Subscript(value=v, idx=e):
                return f"{v}[{e}]"
            case Neg(expr=e):
                return f"-({e.to_string2(types, include_types)})"
            case ArithBinOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string2(types, include_types)} {op} {r.to_string2(types, include_types)}"
            case BoolOp(lhs=l, op=op, rhs=r):
                return f"{l.to_string2(types, include_types)} {op} {r.to_string2(types, include_types)}"
            case Not(expr=e):
                return f"!({e.to_string2(types, include_types)})"
            case V():
                return "V"
            case Star():
                return "*"
            case Call(function_name=fn, arglist=args):
                args = [a.to_string2(types, include_types) for a in args]
                return f"{fn.to_string2(types, include_types)}({', '.join(args)})"
            case GetAttr(name=obj, attr=attr):
                return f"{obj.to_string2(types, include_types)}.{attr}"
            case TypeApp(expr=e, arglist=args):
                arg_str = ", ".join([str(a) for a in args])
                return f"{e.to_string2(types, include_types)}{fg.yellow}[{arg_str}]{fx.reset}"
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
class StrLiteral(Expr):
    value: str


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
    op: str
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
class TypeApp(Expr):
    expr: Expr
    arglist: List[Type | Predicate]


@dataclass
class Argument:
    name: str
    annotation: Optional[Type]

    def __str__(self):
        if self.annotation is None:
            return self.name
        else:
            return f"{self.name}: {fg.yellow}{self.annotation}{fx.reset}"


@dataclass
class Stmt(Node, Pos):
    def to_string(
        self, types: Dict[int, Type] | None = None, indent=0, include_types=False
    ):
        align = " " * indent

        if types is not None:
            return self.to_string2(types, indent, include_types)

        match self:
            case FunctionDef(
                name=name, body=stmts, typ=ArrowType(args=args, ret=retann)
            ) if include_types:
                argstr = ", ".join([f"{x}:{fg.yellow}{t}{fx.reset}" for x, t in args])
                retstr = f" -> {fg.yellow}{retann}{fx.reset}:"
                bodystr = "\n".join(
                    [s.to_string(types, indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"

            case FunctionDef(
                name=name, args=args, return_annotation=retann, body=stmts
            ):
                argstr = ", ".join([str(a) for a in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join(
                    [s.to_string(types, indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"
            case If(test=test, body=body, orelse=orelse):
                bodystr = "\n".join(
                    [s.to_string(types, indent + 2, include_types) for s in body]
                )
                elsestr = "\n".join(
                    [s.to_string(types, indent + 2, include_types) for s in orelse]
                )
                typstr0 = "(" if include_types else ""
                typstr1 = f") : {fg.yellow}[depr]{fx.reset}" if include_types else ""
                res = "\n".join(
                    [
                        f"{align}{typstr0}if {test.to_string(types, include_types)}:",
                        f"{bodystr}",
                        f"{align}else:",
                        f"{elsestr}{typstr1}",
                    ]
                )
                return res
            case Assign(name=name, value=value):
                typann = f": {fg.yellow}[depr]{fx.reset}" if include_types else ""
                return f"{align}{name}{typann} = {value.to_string(types, False)}"
            case Return(value):
                return f"{align}return {value.to_string(types, include_types)}"
            case x:
                return f"{align}{repr(x)}"

    def to_string2(self, types: Dict[int, Type], indent=0, include_types=False):
        align = " " * indent

        match self:
            case FunctionDef(name=name, body=stmts) if include_types:
                typ = types[self.node_id]
                assert isinstance(typ, ArrowType)
                args = typ.args
                retann = typ.ret

                argstr = ", ".join([f"{x}: {fg.yellow}{t}{fx.reset}" for x, t in args])
                retstr = f" -> {fg.yellow}{retann}{fx.reset}:"
                bodystr = "\n".join(
                    [s.to_string2(types, indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"

            case FunctionDef(
                name=name, args=args, return_annotation=retann, body=stmts
            ):
                argstr = ", ".join([str(a) for a in args])
                retstr = f" -> {retann}:" if retann is not None else ":"
                bodystr = "\n".join(
                    [s.to_string2(types, indent + 2, include_types) for s in stmts]
                )
                return f"{align}def {name}({argstr}){retstr}\n{bodystr}"
            case If(test=test, body=body, orelse=orelse):
                bodystr = "\n".join(
                    [s.to_string2(types, indent + 2, include_types) for s in body]
                )
                elsestr = (
                    f"\n{align}else:\n"
                    + "\n".join(
                        [s.to_string2(types, indent + 2, include_types) for s in orelse]
                    )
                    if len(orelse) > 0
                    else ""
                )
                res = "\n".join(
                    [
                        f"{align}if ({test} : {fg.yellow}{types[test.node_id]}{fx.reset}):",
                        f"{bodystr}{elsestr}",
                    ]
                )
                return res
            case Assign(name=name, value=value):
                typann = (
                    f": {fg.yellow}{types[self.node_id]}{fx.reset}"
                    if include_types
                    else ""
                )
                return f"{align}{name}{typann} = {value.to_string2(types, True)}"
            case Return(value):
                return f"{align}return ({value} : {fg.yellow}{types[value.node_id]}{fx.reset})"
            case x:
                return f"{align}{repr(x)}"

    def __str__(self):
        return self.to_string()


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
