"""
Generate the initial candidate predicates for a program by walking
over an annotated program and including all qualifiers that use in
scope variables.
"""

from typing import Dict, List

from solvent import qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnv, ScopedEnvVisitor
from solvent.syntax import Expr

Solution = Dict[str, syn.Conjoin]


def predicate_variables(t: syn.Type) -> List[str]:
    match t:
        case syn.RType(predicate=syn.PredicateVar(name=name)):
            return [name]
        case syn.ArrowType(args=args, ret=ret):
            return sum(
                [predicate_variables(t) for _, t in args], []
            ) + predicate_variables(ret)
        case syn.ListType(inner_typ=inner):
            return predicate_variables(inner)
        case _:
            return []


class InitialPredicatesVisitor(ScopedEnvVisitor):
    def start(self, quals):
        super().start()
        self.solution: Solution = {}
        self.quals = quals

    def calculate(self, typ: syn.Type, env: ScopedEnv, quals):
        pvars = predicate_variables(typ)
        if len(pvars) == 0:
            return

        for pvar in pvars:
            # only consider the first time a predicate is computed
            # this is a slightly hacky way to get at the notion of
            # only considering variables that are in scope at definition
            # time. At some point, we probably want a more robust solution
            # than this
            if pvar not in self.solution:
                self.solution[pvar] = qualifiers.predicate(env, quals)

    def start_Stmt(self, stmt: syn.Stmt):
        super().start_Stmt(stmt)

        if isinstance(stmt, syn.FunctionDef):
            return

        self.calculate(stmt.typ, self.env, self.quals)

    def start_FunctionDef(self, fd: syn.FunctionDef):
        assert isinstance(fd.typ, syn.ArrowType)

        new_env = self.env.clone()
        for x, t in fd.typ.args:
            self.calculate(t, self.env, self.quals)
            new_env = new_env.add(x, t)

        self.calculate(fd.typ.ret, new_env, self.quals)

        # Call super after calculating this so that the arguments
        # aren't added to the environment yet
        super().start_FunctionDef(fd)

    def start_Expr(self, expr: Expr):
        super().start_Expr(expr)

        self.calculate(expr.typ, self.env, self.quals)
