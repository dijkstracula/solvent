from solvent import errors
from solvent import syntax as syn
from solvent.env import ScopedEnv, ScopedEnvVisitor
from solvent.syntax import (
    ArrowType,
    BoolOp,
    Bottom,
    Conjoin,
    HMType,
    IntLiteral,
    RType,
    Stmt,
    Type,
    Variable,
)


def template_type(typ: Type, env: ScopedEnv) -> Type:
    match typ:
        case RType():
            return typ
        case HMType(base=base):
            return RType.template(base)
        case ArrowType(args=args, ret=ret):
            argtypes = []
            for name, t in args:
                if name not in env or env[name] is None:
                    env[name] = template_type(t, env)

                argtypes += [(name, env[name])]

            return ArrowType(
                argtypes,
                template_type(ret, env),
            )

        case x:
            raise errors.Unreachable(x)


class Templatizer(ScopedEnvVisitor):
    def start_Stmt(self, stmt: Stmt):
        super().start_Stmt(stmt)

        if stmt.typ != Bottom():
            tt = template_type(stmt.typ, self.env)
            stmt.annot(tt)

    # def start_Expr(self, expr: syn.Expr):
    #     super().start_Expr(expr)

    #     if expr.typ != Bottom():
    #         expr.annot(template_type(expr.typ, self.env))

    def start_Variable(self, var: Variable):
        super().start_Variable(var)

        if var.name in self.env:
            var.annot(self.env[var.name])

    def start_IntLiteral(self, lit: IntLiteral):
        super().start_IntLiteral(lit)

        lit.annot(RType(syn.Int(), Conjoin([BoolOp(syn.V(), "==", lit)])))
