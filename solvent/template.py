from typing import Dict, List

from solvent.constraints import SubType
from solvent.env import ScopedEnv
from solvent.initial_predicates import predicate_variables
from solvent.syntax import (
    ArithBinOp,
    ArrowType,
    Assign,
    Bool,
    BoolOp,
    Call,
    Class,
    Conjoin,
    DictType,
    Expr,
    FunctionDef,
    GetAttr,
    HMType,
    If,
    Int,
    IntLiteral,
    ListLiteral,
    ListType,
    Neg,
    Not,
    ObjectType,
    PredicateVar,
    Return,
    RType,
    Type,
    V,
    Variable,
)
from solvent.visitor import Visitor


def template_type(typ: Type) -> Type:
    match typ:
        case RType():
            return typ
        case HMType(base=Bool()):  # TODO: have proper support for predicates on bools
            return typ
        case HMType(base=base):
            return RType.template(base)
        case ListType(inner_typ=inner):
            return ListType(template_type(inner)).metadata(typ)
        case DictType() | Class() | ArrowType():
            return typ
        case ObjectType(name=name, generic_args=args):
            return ObjectType(name, [template_type(a) for a in args]).metadata(typ)
        case x:
            raise NotImplementedError(str(x), repr(x))


class Templatizer(Visitor):
    def start(self, types: Dict[int, Type], env: ScopedEnv):
        self.types = types
        self.env = env
        self.constraints: List[SubType] = []
        self.assumptions = []

    def start_FunctionDef(self, fd: FunctionDef):
        this_typ = self.types[fd.node_id]
        assert isinstance(this_typ, ArrowType)

        new_args = [(name, template_type(ty)) for name, ty in this_typ.args]

        self.ret_typ = template_type(this_typ.ret.shape())
        self.types[fd.node_id] = ArrowType(this_typ.type_abs, new_args, self.ret_typ)

        self.env[fd.name] = self.types[fd.node_id]
        self.env.push_scope_mut()
        for name, ty in new_args:
            self.env[name] = ty

    def end_FunctionDef(self, _: FunctionDef):
        self.env.pop_scope_mut()

    def end_Return(self, ret: Return):
        self.types[ret.node_id] = self.types[ret.value.node_id].set_predicate(
            Conjoin([BoolOp(V(), "==", ret.value)])
        )
        self.constraints += [
            SubType(
                self.env.clone(),
                self.assumptions[:],
                self.types[ret.node_id],
                self.ret_typ,
            ).pos(ret)
        ]

    def start_IfTrue(self, if_stmt: If):
        self.assumptions.append(if_stmt.test)

    def end_IfTrue(self, _: If):
        self.assumptions.pop()

    def start_IfFalse(self, if_stmt: If):
        self.assumptions.append(Not(if_stmt.test))

    def end_IfFalse(self, _: If):
        self.assumptions.pop()

    def end_Assign(self, asgn: Assign):
        self.types[asgn.node_id] = template_type(self.types[asgn.value.node_id].shape())
        self.env[asgn.name] = self.types[asgn.value.node_id]
        self.constraints += [
            SubType(
                self.env.clone(),
                self.assumptions[:],
                self.types[asgn.value.node_id],
                self.types[asgn.node_id],
            ).pos(asgn)
        ]

    def end_Expr(self, expr: Expr):
        exclude = [IntLiteral, Variable, ArithBinOp, Call, Assign]
        if any([isinstance(expr, cls) for cls in exclude]):
            return

        self.types[expr.node_id] = template_type(self.types[expr.node_id])

    def end_ArithBinOp(self, abo: ArithBinOp):
        lhs_typ = self.types[abo.lhs.node_id]
        rhs_typ = self.types[abo.rhs.node_id]

        match (lhs_typ, abo.op, rhs_typ):
            case (ListType(), "+", ListType()):
                ret_typ = template_type(self.types[abo.node_id])
                self.constraints += [
                    SubType(self.env.clone(), self.assumptions, lhs_typ, ret_typ),
                    SubType(self.env.clone(), self.assumptions, rhs_typ, ret_typ),
                ]
                self.types[abo.node_id] = ret_typ
            case (lhs, _, rhs) if lhs.base_type() == Int() and rhs.base_type() == Int():
                self.types[abo.node_id] = RType(
                    Int(), Conjoin([BoolOp(V(), "==", abo)])
                )
            case _:
                self.types[abo.node_id] = template_type(self.types[abo.node_id])

    def start_Variable(self, var: Variable):
        self.types[var.node_id] = self.env[var.name].set_predicate(
            Conjoin([BoolOp(V(), "==", var)])
        )

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

        list_typ = template_type(self.types[lit.node_id].shape())
        assert isinstance(list_typ, ListType)
        for child in lit.elts:
            self.constraints += [
                SubType(
                    self.env.clone(),
                    self.assumptions,
                    self.types[child.node_id],
                    list_typ.inner_typ,
                ).pos(child)
            ]
        self.types[lit.node_id] = list_typ

    def end_Call(self, op: Call):
        fn_typ = self.types[op.function_name.node_id]
        assert isinstance(fn_typ, ArrowType)

        if len(fn_typ.args) > 0 and fn_typ.args[0][0] == "self":
            assert isinstance(op.function_name, GetAttr)
            args = [self.types[op.function_name.name.node_id]]
        else:
            args = []

        fn_typ = unify_predvars(
            fn_typ,
            args + [self.types[o.node_id] for o in op.arglist],
        )

        self.types[op.node_id] = fn_typ.ret.subst(
            zip([name for name, _ in fn_typ.args], op.arglist)
        )

        for passed_arg, (_, fn_arg_typ) in zip(op.arglist, fn_typ.args):
            self.constraints += [
                SubType(
                    self.env.clone(),
                    self.assumptions[:],
                    self.types[passed_arg.node_id],
                    fn_arg_typ,
                ).pos(passed_arg)
            ]


def unify_predvars(fn_typ: ArrowType, args: List[Type]) -> ArrowType:
    for name, _ in filter(lambda x: x[1] == "pred", fn_typ.type_abs.items()):
        for i, (_, ty_arg) in enumerate(fn_typ.args):
            if name in predicate_variables(ty_arg):
                # lookup arg
                # TODO: this won't work for arguments that have filled
                # in predicates
                arg_pvar = predicate_variables(args[i])
                assert len(arg_pvar) == 1
                fn_typ = fn_typ.subst_typevar(name, PredicateVar(arg_pvar[0]))

    return fn_typ
