from typing import Dict

from solvent.errors import Unreachable
from solvent.syntax import (
    ArrowType,
    Call,
    GetAttr,
    HMType,
    ObjectType,
    PredicateVar,
    Type,
    TypeApp,
    TypeVar,
    Variable,
)
from solvent.visitor import Visitor


class TypeApplication(Visitor):
    def start(self, types: Dict[int, Type]):
        self.types = types

    def end_Call(self, call: Call):
        fn_typ = self.types[call.function_name.node_id]

        # if we know that the fn typ is an arrow type at this point
        if isinstance(fn_typ, ArrowType) and len(fn_typ.type_abs) != 0:
            new_vars = []
            for v, kind in fn_typ.type_abs.items():
                if kind == "type":
                    new_vars += [HMType(TypeVar.fresh(v))]
                elif kind == "pred":
                    new_vars += [PredicateVar.fresh(v)]
                else:
                    raise Unreachable(kind)
            return Call(
                TypeApp(
                    call.function_name, new_vars, node_id=call.function_name.node_id
                ).pos(call.function_name),
                call.arglist,
                node_id=call.node_id,
            ).pos(call)

        # super().end_Call(op)

        # obj_type = op.function_name.typ
        # if isinstance(obj_type, ArrowType):
        #     if len(obj_type.type_abs) > 0:
        #         new_vars = []
        #         for v, kind in obj_type.type_abs.items():
        #             if kind == "type":
        #                 new_vars += [HMType(TypeVar.fresh(v))]
        #             elif kind == "pred":
        #                 new_vars += [PredicateVar.fresh(v)]
        #             else:
        #                 raise Unreachable(kind)
        #         return Call(
        #             TypeApp(op.function_name, new_vars).pos(op.function_name),
        #             op.arglist,
        #         ).pos(op)

    # def start_Variable(self, var: Variable):
    #     if var.name in self.env:
    #         var.annot(self.env[var.name])
    #     super().start_Variable(var)

    # def end_GetAttr(self, lit: GetAttr):
    #     super().end_GetAttr(lit)

    #     if isinstance(lit.name.typ, ObjectType):
    #         lit.annot(lit.name.typ.fields[lit.attr])

    #     return lit
