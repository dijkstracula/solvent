from typing import Dict, List

from solvent.constraints import SubType
from solvent.env import ScopedEnv
from solvent.syntax import (
    ArrowType,
    Assign,
    BoolOp,
    Call,
    Class,
    Conjoin,
    DictType,
    Expr,
    FunctionDef,
    HMType,
    IntLiteral,
    ListLiteral,
    ListType,
    Neg,
    ObjectType,
    PredicateVar,
    Return,
    RType,
    Type,
    V,
    Variable,
)
from solvent.visitor import Visitor

# def template_type(typ: Type, env: ScopedEnv) -> Type:
#     match typ:
#         case RType():
#             return typ
#         case HMType(base=base):
#             return RType.template(base)
#         case ArrowType(type_abs=abs, args=args, ret=ret):
#             argtypes = []
#             for name, t in args:
#                 if name not in env or env[name] is None:
#                     env[name] = template_type(t, env)

#                 argtypes += [(name, env[name])]


#             return ArrowType(
#                 abs,
#                 argtypes,
#                 template_type(ret, env),
#             )
#         case ListType(inner_typ):
#             return ListType(template_type(inner_typ, env))
#         case ObjectType(name=name, generic_args=args):
#             return ObjectType(name, [template_type(t, env) for t in args])
#         case x:
#             raise errors.Unreachable(x)
def template_type(typ: Type) -> Type:
    match typ:
        case RType():
            return typ
        case HMType(base=base):
            return RType.template(base)
        case ListType(inner_typ=inner):
            return ListType(template_type(inner)).metadata(typ)
        case DictType():
            return typ
        case Class():
            return typ
        case ArrowType(type_abs=abs, args=args, ret=_):
            pred_vars = [v for v, kind in abs.items() if kind == "pred"]
            new_fn_typ = typ
            for pv in pred_vars:
                fresh = PredicateVar.fresh(pv)
                new_fn_typ = new_fn_typ.subst_typevar(pv, fresh)
            return new_fn_typ
        case ObjectType(name=name, generic_args=args):
            return ObjectType(name, [template_type(a) for a in args]).metadata(typ)
        case x:
            raise NotImplementedError(str(x), repr(x))


class Templatizer(Visitor):
    def start(self, types: Dict[int, Type], env: ScopedEnv):
        self.types = types
        self.env = env
        self.constraints: List[SubType] = []

    def start_FunctionDef(self, fd: FunctionDef):
        this_typ = self.types[fd.node_id]
        assert isinstance(this_typ, ArrowType)

        self.ret_typ = template_type(this_typ.ret.shape())
        self.types[fd.node_id] = ArrowType(
            this_typ.type_abs, this_typ.args, self.ret_typ
        )

    def end_Return(self, ret: Return):
        self.constraints += [
            SubType(self.env, [], self.types[ret.value.node_id], self.ret_typ).pos(ret)
        ]

    def end_Assign(self, asgn: Assign):
        self.types[asgn.node_id] = self.types[asgn.value.node_id]
        self.env[asgn.name] = self.types[asgn.value.node_id]

    def end_Expr(self, expr: Expr):
        exclude = [IntLiteral, Variable]
        if any([isinstance(expr, cls) for cls in exclude]):
            return

        self.types[expr.node_id] = template_type(self.types[expr.node_id])

    def start_Variable(self, var: Variable):
        self.types[var.node_id] = self.env[var.name]

    def start_IntLiteral(self, lit: IntLiteral):
        typ = self.types[lit.node_id]
        self.types[lit.node_id] = typ.set_predicate(Conjoin([BoolOp(V(), "==", lit)]))

    def end_Neg(self, op: Neg):
        if isinstance(op.expr, IntLiteral):
            self.types[op.node_id] = self.types[op.node_id].set_predicate(
                Conjoin([BoolOp(V(), "==", op)])
            )

    def end_ListLiteral(self, lit: ListLiteral):
        """
        The types of all the children of a list literal should be subtypes
        of the type of this list.
        """

        list_typ = template_type(self.types[lit.node_id])
        assert isinstance(list_typ, ListType)
        for child in lit.elts:
            self.constraints += [
                SubType(
                    self.env, [], self.types[child.node_id], list_typ.inner_typ
                ).pos(child)
            ]
        self.types[lit.node_id] = list_typ

    def end_Call(self, op: Call):
        fn_typ = self.types[op.function_name.node_id]
        assert isinstance(fn_typ, ArrowType)
        self.types[op.node_id] = fn_typ.ret

        for passed_arg, (_, fn_arg_typ) in zip(op.arglist, fn_typ.args):
            self.constraints += [
                SubType(self.env, [], self.types[passed_arg.node_id], fn_arg_typ).pos(
                    op
                )
            ]
