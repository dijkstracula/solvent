from solvent import errors
from solvent import syntax as syn
from solvent.env import ScopedEnv, ScopedEnvVisitor
from solvent.syntax import (
    ArrowType,
    Assign,
    BoolOp,
    Conjoin,
    DataFrameType,
    Expr,
    FunctionDef,
    HMType,
    IntLiteral,
    ListType,
    ObjectType,
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
        case ListType(inner_typ):
            return ListType(template_type(inner_typ, env))
        case DataFrameType(columns=c):
            return DataFrameType({name: template_type(t, env) for name, t in c.items()})
        case ObjectType(fields=fields):
            return ObjectType(
                {name: template_type(t, env) for name, t in fields.items()}
            )
        case x:
            raise errors.Unreachable(x)


class Templatizer(ScopedEnvVisitor):
    def start(self):
        super().start()
        # TODO: template_type for whatever is in the env
        for name, typ in list(self.env.items()):
            self.env[name] = template_type(typ, self.env)
            print(self.env[name])

    def start_Stmt(self, stmt: Stmt):
        super().start_Stmt(stmt)

        if isinstance(stmt, FunctionDef) or isinstance(stmt, Assign):
            return

        tt = template_type(stmt.typ, self.env)
        stmt.annot(tt)

    def end_Assign(self, stmt: syn.Assign):
        super().end_Assign(stmt)

        stmt.annot(stmt.value.typ)
        self.env[stmt.name] = stmt.value.typ

    def start_FunctionDef(self, fd: FunctionDef):
        # super().start_FunctionDef(fd)
        assert isinstance(fd.typ, ArrowType)

        args = []
        for arg, (base_name, base_typ) in zip(fd.args, fd.typ.args):
            if arg.annotation is not None:
                args += [(arg.name, arg.annotation)]
            else:
                args += [(base_name, template_type(base_typ, self.env))]

        if fd.return_annotation is not None:
            ret = fd.return_annotation
        else:
            ret = template_type(fd.typ.ret, self.env)

        fd.annot(ArrowType(args, ret))

        # we want to add our newly templated type to the scoped env
        # so we call our superclass after we have created the template types
        super().start_FunctionDef(fd)

    def start_Expr(self, expr: Expr):
        super().start_Expr(expr)

        if isinstance(expr, Variable) or isinstance(expr, IntLiteral):
            return

        tt = template_type(expr.typ, self.env)
        expr.annot(tt)

    def start_Variable(self, var: Variable):
        super().start_Variable(var)

        if var.name in self.env:
            var.annot(self.env[var.name])
        else:
            raise errors.Unreachable()

    def start_IntLiteral(self, lit: IntLiteral):
        super().start_IntLiteral(lit)

        lit.annot(RType(syn.Int(), Conjoin([BoolOp(syn.V(), "==", lit)])))
