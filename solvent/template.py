from logging import debug
from typing import Dict

from solvent import errors
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.syntax import (
    ArrowType,
    Assign,
    BoolOp,
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
    RType,
    Stmt,
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
        case ArrowType():
            return typ
        case ObjectType():
            return typ
        case x:
            raise NotImplementedError(str(x), repr(x))


class Templatizer(Visitor):
    def start(self, types: Dict[int, Type], env: ScopedEnv):
        self.types = types
        self.env = env

    def start_IntLiteral(self, lit: IntLiteral):
        typ = self.types[lit.node_id]
        self.types[lit.node_id] = typ.set_predicate(Conjoin([BoolOp(V(), "==", lit)]))

    def end_Assign(self, asgn: Assign):
        self.types[asgn.node_id] = self.types[asgn.value.node_id]
        self.env[asgn.name] = self.types[asgn.value.node_id]

    def end_Expr(self, expr: Expr):
        if isinstance(expr, Variable):
            return

        self.types[expr.node_id] = template_type(self.types[expr.node_id])

    def start_Variable(self, var: Variable):
        self.types[var.node_id] = self.env[var.name]


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
