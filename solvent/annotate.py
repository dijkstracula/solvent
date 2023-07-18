"""
Implements a forward type checking pass.
"""

from logging import debug, warning
from typing import Dict, List

from solvent.env import ScopedEnv
from solvent.errors import Unreachable
from solvent.syntax import (
    Any,
    ArithBinOp,
    ArrowType,
    Assign,
    BoolLiteral,
    BoolOp,
    Call,
    Class,
    DictType,
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
    RType,
    SelfType,
    Stmt,
    Type,
    TypeApp,
    TypeVar,
    Unit,
    Unknown,
    Variable,
)
from solvent.utils import default
from solvent.visitor import Visitor


def lookup_path(path: List[str], thing: Type) -> Type:
    match path:
        case []:
            return thing
        case [x, *rest]:
            match thing:
                case Class(fields=fields):
                    return lookup_path(rest, fields[x])
                case DictType(items=items):
                    return lookup_path(rest, items[x])
                case x:
                    raise NotImplementedError(type(x))
        case _:
            raise Unreachable()


def resolve_class(obj: ObjectType, env: ScopedEnv) -> Class:
    match obj.name.split("."):
        case [name]:
            cls_def = env[name]
        case [name, *rest]:
            cls_def = lookup_path(rest, env[name])
        case _:
            raise Unreachable()

    assert isinstance(cls_def, Class)

    for cls_tyv, conc_tyv in zip(cls_def.type_abs, obj.generic_args):
        cls_def = cls_def.subst_typevar(cls_tyv, conc_tyv)

    return cls_def


class Annotate(Visitor):
    def start(
        self,
        initial_env: ScopedEnv | None = None,
        initial_id_map: Dict[int, Type] | None = None,
    ):
        if initial_env is None:
            initial_env = ScopedEnv.empty()

        self.env = initial_env

        if initial_id_map is None:
            initial_id_map = {}

        self.id_map: Dict[int, Type] = initial_id_map

        super().start()

    def end_Stmt(self, stmt: Stmt):
        if stmt.node_id not in self.id_map:
            self.id_map[stmt.node_id] = HMType(Unit())

    def start_FunctionDef(self, fd: FunctionDef):
        """
        Add arguments to the environment.
        """

        arglist = []
        for arg in fd.args:
            arglist += [(arg.name, default(arg.annotation, fallback=HMType.fresh("a")))]

        # add the type of fd to the environment
        if fd.node_id in self.id_map:
            this_typ = self.id_map[fd.node_id]
        else:
            this_typ = ArrowType(
                {}, arglist, default(fd.return_annotation, fallback=HMType.fresh("ret"))
            )

        self.env[fd.name] = this_typ
        self.id_map[fd.node_id] = this_typ
        self.env.push_scope_mut()

        for name, typ in arglist:
            self.env[name] = typ

        return super().start_FunctionDef(fd)

    def end_FunctionDef(self, _: FunctionDef):
        self.env.pop_scope_mut()

    def end_Assign(self, asgn: Assign):
        self.env[asgn.name] = self.id_map[asgn.value.node_id]
        self.id_map[asgn.node_id] = self.id_map[asgn.value.node_id]

        return super().end_Assign(asgn)

    def end_Expr(self, expr: Expr):
        if expr.node_id not in self.id_map:
            raise NotImplementedError(f"{expr} {expr!r}")
            # self.id_map[expr.node_id] = Unknown()

    def start_IntLiteral(self, lit: IntLiteral):
        self.id_map[lit.node_id] = HMType.int()

    def start_BoolLiteral(self, lit: BoolLiteral):
        self.id_map[lit.node_id] = HMType.bool()

    def start_Variable(self, var: Variable):
        super().start_Variable(var)
        self.id_map[var.node_id] = self.env[var.name]

    def end_ArithBinOp(self, abo: ArithBinOp):
        lhs_typ = self.id_map[abo.lhs.node_id]
        rhs_typ = self.id_map[abo.rhs.node_id]

        if isinstance(lhs_typ, ObjectType):
            # find the class that this object refers to
            cls_def = resolve_class(lhs_typ, self.env)
            match abo.op:
                case "*":
                    if "__mul__" in cls_def.fields:
                        method = cls_def.fields["__mul__"]
                        assert isinstance(method, ArrowType)
                        warning("not doing any type checking here")  # TODO: fix this
                        # substs = [
                        #     (name, expr)
                        #     for ((name, _), expr) in zip(
                        #         method.args, [abo.lhs, abo.rhs]
                        #     )
                        # ]

                        # self.id_map[abo.node_id] = method.ret.resolve_name(
                        #     lhs_typ.name
                        # ).subst(substs)
                        self.id_map[abo.node_id] = method.ret.resolve_name(
                            lhs_typ.name
                        ).shape()
                        return
                case _:
                    pass

        match (lhs_typ.base_type(), abo.op, rhs_typ.base_type()):
            # case (None, "/", _) if isinstance(
            #     lhs_typ, ObjectType
            # ) and "__div__" in lhs_typ.fields and isinstance(
            #     lhs_typ.fields["__div__"], ArrowType
            # ):
            #     self.id_map[abo.node_id] = lhs_typ.fields["__div__"].ret
            case (None, _, _):
                self.id_map[abo.node_id] = Unknown()
            case (TypeVar(_), _, _):
                self.id_map[abo.node_id] = HMType.fresh("abo")
            case (Int(), "+", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case (Int(), "-", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case (Int(), "/", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case (Int(), "*", Int()):
                self.id_map[abo.node_id] = HMType.int()
            case x:
                raise NotImplementedError(x)

    def end_BoolOp(self, op: BoolOp):
        lhs_typ = self.id_map[op.lhs.node_id]
        rhs_typ = self.id_map[op.rhs.node_id]

        match (lhs_typ.base_type(), op.op, rhs_typ.base_type()):
            case (TypeVar(_), _, _):
                self.id_map[op.node_id] = HMType.fresh("bo")
            case x:
                raise NotImplementedError(x)

    def end_ListLiteral(self, lit: ListLiteral):
        # TODO: compute least upper bound of types in list

        # check if every element in the list literal has the same type
        inner_typ: Type | None = None
        for elt in lit.elts:
            elt_typ = self.id_map[elt.node_id]
            if inner_typ is None:
                inner_typ = elt_typ
            elif inner_typ != elt_typ:
                inner_typ = Any()

        if inner_typ is None:
            inner_typ = Unknown()

        self.id_map[lit.node_id] = ListType(inner_typ)

        return super().end_ListLiteral(lit)

    def end_GetAttr(self, lit: GetAttr) -> Expr | None:
        obj_typ = self.id_map[lit.name.node_id]

        match obj_typ:
            case DictType(items=items) if lit.attr in items:
                # HACK: change the name of the item so that it carries
                # along the full path. This lets us resolve the
                # name later by just looking at the type.
                self.id_map[lit.node_id] = items[lit.attr].resolve_name(
                    f"{lit.name}.{lit.attr}"
                )
            case DictType():
                # TODO: make nicer error message
                raise Exception(f"{lit.attr} not in {lit.name}")
            case ObjectType(generic_args=args):
                # find the class that this object refers to
                cls_def = resolve_class(obj_typ, self.env)

                # get the method from the class
                method = cls_def.fields[lit.attr]

                # then, subst all the typevars defined
                # at the class level using the arg list
                # that we have
                for a, tyv in zip(args, cls_def.type_abs):
                    method = method.subst_typevar(tyv, a)

                self.id_map[lit.node_id] = method
            case x:
                raise NotImplementedError(x)

        # if not isinstance(obj_typ, ObjectType):
        #     raise Exception(
        #         f"We must know that {lit.name} is an object at this point.\n{obj_typ}"
        #     )

        # if lit.attr not in obj_typ.fields:
        #     raise Exception(f"{lit.attr} not in {obj_typ.name}")

        # self.id_map[lit.node_id] = obj_typ.fields[lit.attr]

    def end_Neg(self, op: Neg):
        op_typ = self.id_map[op.expr.node_id]
        if op_typ.base_type() == Int():
            self.id_map[op.node_id] = HMType.int()
        return super().end_Neg(op)

    def end_Call(self, op: Call) -> Expr | None:
        lookup_typ = self.id_map[op.function_name.node_id]
        match lookup_typ:
            case ArrowType():
                fn_typ = lookup_typ
            case Class(
                name=name, constructor=ArrowType(type_abs=abs, args=args, ret=ret)
            ):
                fn_typ = ArrowType(abs, args, ret.resolve_name(name))
            case _:
                raise Exception(f"You can't call a {lookup_typ}")

        assert isinstance(fn_typ, ArrowType)

        # start by checking that the arg types are consistent
        # with what we expect.
        # gather types, ignoring a self type if it comes first
        match fn_typ.args:
            case [(_, SelfType()), *rest]:
                fn_args_to_chk = [ty for (_, ty) in rest]
            case rest:
                fn_args_to_chk = [ty for (_, ty) in rest]

        assert len(fn_args_to_chk) == len(op.arglist)  # TODO: real error message
        for arg_typ, passed_arg in zip(fn_args_to_chk, op.arglist):
            passed_typ = self.id_map[passed_arg.node_id]
            if not type_consistent_with(arg_typ, passed_typ):
                raise Exception(f"{arg_typ} != {passed_typ}")

        if fn_typ.type_abs != {}:
            new_fn_type = fn_typ
            # make a list of fresh type variables
            new_vars = []
            for v, kind in fn_typ.type_abs.items():
                if kind == "type":
                    fresh = HMType(TypeVar.fresh(v))
                    new_vars += [fresh]
                elif kind == "pred":
                    fresh = PredicateVar.fresh(v)
                    new_vars += [fresh]
                else:
                    raise Unreachable(kind)
                new_fn_type = new_fn_type.subst_typevar(v, fresh)

            # construct a new type application node using this list of variables
            type_app = TypeApp(
                op.function_name,
                new_vars,
            ).pos(op.function_name)

            self.id_map[type_app.node_id] = new_fn_type
            self.id_map[op.node_id] = new_fn_type.ret

            # construct a new call node that calls the type app instead of the
            # function
            return Call(
                type_app,
                op.arglist,
                node_id=op.node_id,
            ).pos(op)

        # match fn_typ:
        #     # if we already know that it is a function type, we can be
        #     # more precise in the type we assign right now
        #     case ArrowType(type_abs=type_abs, args=args, ret=ret):
        #     case Class(constructor=cons) if len(cons.type_abs) == 0:
        #         assert len(cons.args) == len(op.arglist)
        #         for (_, typ), exp in zip(cons.args, op.arglist):
        #             if self.id_map[exp.node_id] != Unknown() and typ != Unknown():
        #                 assert typ == self.id_map[exp.node_id]

        #         self.id_map[op.node_id] = cons.ret
        #     case Class(
        #         name=name, constructor=ArrowType(type_abs=type_abs, args=args, ret=ret)
        #     ):
        #         assert isinstance(ret, SelfType)
        #         self.id_map[op.node_id] = ret.resolve_name(name)

        #         raise NotImplementedError(fn_typ)
        #     case x:
        #         raise NotImplementedError(x)


def type_consistent_with(t0: Type, t1: Type) -> bool:
    match (t0, t1):
        case (Unknown(), _) | (_, Unknown()):
            return True
        case (Any(), _) | (_, Any()):
            return True
        case (HMType(TypeVar()), _) | (_, HMType(TypeVar())):
            return True
        case (HMType(base=b1), HMType(base=b2)) | (
            RType(
                base=b1,
            ),
            RType(base=b2),
        ):
            return b1 == b2
        case (HMType(base=b1), RType(base=b2)) | (RType(base=b1), HMType(base=b2)):
            return b1 == b2
        case (ListType(inner_typ=i0), ListType(inner_typ=i1)):
            return type_consistent_with(i0, i1)
        case (ArrowType(args=args0, ret=ret0), ArrowType(args=args1, ret=ret1)):
            return all(
                [type_consistent_with(a0, a1) for (_, a0), (_, a1) in zip(args0, args1)]
            ) and type_consistent_with(ret0, ret1)
        case (DictType(items=items0), DictType(items=items1)):
            return all([type_consistent_with(t, items1[x]) for x, t in items0.items()])
        case (Class(), _) | (ObjectType(), _) | (SelfType(), _):
            raise NotImplementedError(t0, t1)
        case x:
            warning(f"Not handling {x}")
            return False
