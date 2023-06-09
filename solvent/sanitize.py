from solvent import constraints
from solvent.env import ScopedEnv
from solvent.syntax import ArrowType, Expr, HMType, ListType, Stmt, Type, TypeAnnotation
from solvent.visitor import Visitor


class HmExists(Exception):
    def __init__(self, msg):
        # msg = f"{node.typ}\n{node}\n{node.position}"
        super().__init__(msg)

    @staticmethod
    def node(node) -> "HmExists":
        msg = f"{node.typ}\n{node}\n{node.position}"
        return HmExists(msg)


class AssertNoHmTypes(Visitor):
    def check_typ(self, src: TypeAnnotation | str, typ: Type):
        match typ:
            case ArrowType(args=args, ret=ret):
                for _, aty in args:
                    self.check_typ(src, aty)
                self.check_typ(src, ret)
            case ListType(inner_typ=inner):
                self.check_typ(src, inner)
            case HMType():
                if isinstance(src, TypeAnnotation):
                    raise HmExists.node(src)
                else:
                    raise HmExists(src)
            case _:
                raise Exception(f"No type annotation: {src}")

    def start_Stmt(self, stmt: Stmt):
        super().start_Stmt(stmt)

        self.check_typ(stmt, stmt.typ)

    def start_Expr(self, expr: Expr):
        super().start_Expr(expr)

        self.check_typ(expr, expr.typ)

    def check_context(self, ctx: ScopedEnv) -> tuple[str, Type] | None:
        for _, ty in ctx.items():
            self.check_typ(f"{ctx}", ty)
        return None

    def check_constraint(self, constr: constraints.SubType):
        match constr:
            case constraints.SubType(context=ctx):
                self.check_context(ctx)
