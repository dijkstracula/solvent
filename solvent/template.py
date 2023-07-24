from logging import debug
from typing import Dict, List

from solvent import errors
from solvent import syntax as syn
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
    Stmt,
    Type,
    TypeApp,
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
        case ArrowType(type_abs=abs, args=args, ret=ret):
            pred_vars = [v for v, kind in abs.items() if kind == "pred"]
            new_fn_typ = typ
            for pv in pred_vars:
                fresh = PredicateVar.fresh(pv)
                new_fn_typ = new_fn_typ.subst_typevar(pv, fresh)
            return new_fn_typ
            # return ArrowType(
            #     abs, [(name, template_type(t)) for name, t in args], template_type(ret)
            # )
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

        self.ret_typ = template_type(this_typ.ret)
        self.types[fd.node_id] = ArrowType(
            this_typ.type_abs, this_typ.args, self.ret_typ
        )

    def end_Return(self, ret: Return):
        self.constraints += [
            SubType(self.env, [], self.types[ret.value.node_id], self.ret_typ)
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
                SubType(self.env, [], self.types[child.node_id], list_typ.inner_typ)
            ]
        self.types[lit.node_id] = list_typ

    def end_Call(self, op: Call):
        fn_typ = self.types[op.function_name.node_id]
        assert isinstance(fn_typ, ArrowType)
        self.types[op.node_id] = fn_typ.ret

        for op_ty, fn_arg_typ in zip(
            [self.types[o.node_id] for o in op.arglist], [ty for _, ty in fn_typ.args]
        ):
            self.constraints += [SubType(self.env, [], op_ty, fn_arg_typ)]


# class Templatizer(Visitor):
#     def start(self, initial_types: Dict[int, Type], initial_env: ScopedEnv | None = None):
#         self.types = initial_types

#         if initial_env is None:
#             initial_env = ScopedEnv.empty()

#         self.env = initial_env

#         # super().start(initial_env)
#         # TODO: template_type for whatever is in the env
#         for name, typ in list(self.env.items()):
#             self.env[name] = template_type(typ, self.env)

#     def start_Stmt(self, stmt: Stmt):
#         super().start_Stmt(stmt)

#         if isinstance(stmt, FunctionDef) or isinstance(stmt, Assign):
#             return

#         tt = template_type(stmt.typ, self.env)
#         stmt.annot(tt)

#     def end_Assign(self, stmt: syn.Assign):
#         super().end_Assign(stmt)

#         stmt.annot(stmt.value.typ)
#         self.env[stmt.name] = stmt.value.typ

#     def start_FunctionDef(self, fd: FunctionDef):
#         # super().start_FunctionDef(fd)
#         assert isinstance(fd.typ, ArrowType)

#         args = []
#         for arg, (base_name, base_typ) in zip(fd.args, fd.typ.args):
#             if arg.annotation is not None:
#                 args += [(arg.name, arg.annotation)]
#             else:
#                 args += [(base_name, template_type(base_typ, self.env))]

#         if fd.return_annotation is not None:
#             ret = fd.return_annotation
#         else:
#             ret = template_type(fd.typ.ret, self.env)

#         fd.annot(ArrowType(fd.typ.type_abs, args, ret))

#         # we want to add our newly templated type to the scoped env
#         # so we call our superclass after we have created the template types
#         super().start_FunctionDef(fd)

#     def start_Expr(self, expr: Expr):
#         super().start_Expr(expr)

#         if (
#             isinstance(expr, Variable)
#             or isinstance(expr, Neg)
#             or isinstance(expr, IntLiteral)
#         ):
#             return

#         tt = template_type(expr.typ, self.env)
#         expr.annot(tt)

#     def start_Variable(self, var: Variable):
#         super().start_Variable(var)

#         if var.name in self.env:
#             var.annot(self.env[var.name])
#         else:
#             raise errors.Unreachable(f"{var} is undefined")

#     def start_IntLiteral(self, lit: IntLiteral):
#         super().start_IntLiteral(lit)

#         lit.annot(RType(syn.Int(), Conjoin([BoolOp(syn.V(), "==", lit)])))

#     def start_Neg(self, expr: Neg):
#         super().start_Neg(expr)

#         expr.annot(RType(syn.Int(), Conjoin([BoolOp(syn.V(), "==", expr)])))
