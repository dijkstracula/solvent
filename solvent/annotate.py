from logging import debug
from typing import Dict

from solvent.env import ScopedEnv
from solvent.errors import Unreachable
from solvent.syntax import (
    ArithBinOp,
    ArrowType,
    Assign,
    Bottom,
    Call,
    Expr,
    FunctionDef,
    GetAttr,
    HMType,
    Int,
    IntLiteral,
    ListLiteral,
    ListType,
    Neg,
    ObjectType,
    PredicateVar,
    Stmt,
    Str,
    Type,
    TypeApp,
    TypeVar,
    Variable,
)
from solvent.utils import default
from solvent.visitor import Visitor


class Annotate(Visitor):
    def start(self, initial_env: ScopedEnv | None = None):
        if initial_env is not None:
            self.env = initial_env

        self.id_map: Dict[int, Type] = {}

        super().start()

    def end_Stmt(self, stmt: Stmt):
        if stmt.node_id not in self.id_map:
            self.id_map[stmt.node_id] = Bottom()
        return super().end_Stmt(stmt)

    def start_FunctionDef(self, fd: FunctionDef):
        """
        Add arguments to the environment.
        """

        arglist = []
        for arg in fd.args:
            arglist += [(arg.name, default(arg.annotation, fallback=Bottom()))]

        # add the type of fd to the environment
        self.env[fd.name] = ArrowType(
            {}, arglist, default(fd.return_annotation, fallback=Bottom())
        )
        self.env.push_scope_mut()

        for name, typ in arglist:
            self.env[name] = typ

        return super().start_FunctionDef(fd)

    def end_Assign(self, asgn: Assign):
        self.env[asgn.name] = self.id_map[asgn.value.node_id]
        self.id_map[asgn.node_id] = self.id_map[asgn.value.node_id]

        return super().end_Assign(asgn)

    def end_FunctionDef(self, fd: FunctionDef):
        """
        Add a type annotation for this function definition.
        """

        self.env.pop_scope_mut()

        typ_args = []
        for a in fd.args:
            if a.annotation is not None:
                typ_args += [(a.name, a.annotation)]
            else:
                typ_args += [(a.name, Bottom())]

        ret_typ = Bottom()
        if fd.return_annotation is not None:
            ret_typ = fd.return_annotation

        self.id_map[fd.node_id] = ArrowType({}, typ_args, ret_typ)
        return super().end_FunctionDef(fd)

    def end_Expr(self, expr: Expr):
        if expr.node_id not in self.id_map:
            self.id_map[expr.node_id] = Bottom()
        return super().end_Expr(expr)

    def start_IntLiteral(self, lit: IntLiteral):
        self.id_map[lit.node_id] = HMType.int()
        return super().start_IntLiteral(lit)

    def start_Variable(self, var: Variable):
        super().start_Variable(var)
        self.id_map[var.node_id] = self.env[var.name]

    def end_ArithBinOp(self, abo: ArithBinOp):
        lhs_typ = self.id_map[abo.lhs.node_id]
        rhs_typ = self.id_map[abo.rhs.node_id]

        match (lhs_typ.base_type(), abo.op, rhs_typ.base_type()):
            case (None, "/", _) if isinstance(
                lhs_typ, ObjectType
            ) and "__div__" in lhs_typ.fields and isinstance(
                lhs_typ.fields["__div__"], ArrowType
            ):
                self.id_map[abo.node_id] = lhs_typ.fields["__div__"].ret
            case (None, _, _):
                self.id_map[abo.node_id] = Bottom()
            case (Int(), "+", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case (Int(), "-", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case (Int(), "/", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case x:
                raise NotImplementedError(x)

        return super().end_ArithBinOp(abo)

    def end_ListLiteral(self, lit: ListLiteral):
        # TODO: compute least upper bound of types in list

        # check if every element in the list literal has the same type
        inner_typ: Type | None = None
        for elt in lit.elts:
            elt_typ = self.id_map[elt.node_id]
            if inner_typ is None:
                inner_typ = elt_typ
            elif inner_typ != elt_typ:
                inner_typ = Bottom()

        if inner_typ is None:
            inner_typ = Bottom()

        self.id_map[lit.node_id] = ListType(inner_typ)

        return super().end_ListLiteral(lit)

    def end_GetAttr(self, lit: GetAttr) -> Expr | None:
        obj_typ = self.id_map[lit.name.node_id]
        if not isinstance(obj_typ, ObjectType):
            raise Exception(f"We must know that {lit.name} is an object at this point.")

        if lit.attr not in obj_typ.fields:
            # TODO: make nicer error message
            raise Exception(f"{lit.attr} not in {obj_typ.name}")

        self.id_map[lit.node_id] = obj_typ.fields[lit.attr]

        return super().end_GetAttr(lit)

    def end_Neg(self, op: Neg):
        op_typ = self.id_map[op.expr.node_id]
        if op_typ.base_type() == Int():
            self.id_map[op.node_id] = HMType.int()
        return super().end_Neg(op)

    def end_Call(self, op: Call) -> Expr | None:
        fn_typ = self.id_map[op.function_name.node_id]
        if isinstance(fn_typ, ArrowType):
            if fn_typ.type_abs == {}:
                assert len(fn_typ.args) == len(op.arglist)  # TODO: real error message

                for (_, typ), exp in zip(fn_typ.args, op.arglist):
                    assert typ == self.id_map[exp.node_id]

                self.id_map[op.node_id] = fn_typ.ret
            else:
                new_vars = []
                for v, kind in fn_typ.type_abs.items():
                    if kind == "type":
                        new_vars += [HMType(TypeVar.fresh(v))]
                    elif kind == "pred":
                        pass
                        # new_vars += [PredicateVar.fresh(v)]
                    else:
                        raise Unreachable(kind)

                type_app = TypeApp(
                    op.function_name,
                    new_vars,
                ).pos(op.function_name)

                self.id_map[type_app.node_id] = HMType(Str())

                return Call(
                    type_app,
                    op.arglist,
                    node_id=op.node_id,
                ).pos(op)
