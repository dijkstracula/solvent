from solvent.env import ScopedEnvVisitor
from solvent.errors import Unreachable
from solvent.syntax import (
    ArrowType,
    Call,
    GetAttr,
    HMType,
    ObjectType,
    PredicateVar,
    TypeApp,
    TypeVar,
    Variable,
)


class TypeApplication(ScopedEnvVisitor):
    def end_Call(self, op: Call):
        super().end_Call(op)

        obj_type = op.function_name.typ
        if isinstance(obj_type, ArrowType):
            if len(obj_type.type_abs) > 0:
                new_vars = []
                for v, kind in obj_type.type_abs.items():
                    if kind == "type":
                        new_vars += [HMType(TypeVar.fresh(v))]
                    elif kind == "pred":
                        new_vars += [PredicateVar.fresh(v)]
                    else:
                        raise Unreachable(kind)
                return Call(
                    TypeApp(op.function_name, new_vars).pos(op.function_name),
                    op.arglist,
                ).pos(op)

    def start_Variable(self, var: Variable):
        if var.name in self.env:
            var.annot(self.env[var.name])
        super().start_Variable(var)

    def end_GetAttr(self, lit: GetAttr):
        super().end_GetAttr(lit)

        if isinstance(lit.name.typ, ObjectType):
            lit.annot(lit.name.typ.fields[lit.attr])

        return lit
