"""
Generate the initial candidate predicates for a program by walking
over an annotated program and including all qualifiers that use in
scope variables.
"""

from typing import Dict, List

from solvent import qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.syntax import Expr
from solvent.visitor import Visitor

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
        case syn.ObjectType(generic_args=args):
            return sum([predicate_variables(t) for t in args], [])
        case _:
            return []


class InitialPredicatesVisitor(Visitor):
    def start(
        self,
        quals: List[qualifiers.Qualifier],
        types: Dict[int, syn.Type],
        initial_env: ScopedEnv | None = None,
    ):
        self.solution: Solution = {}
        self.quals = quals
        self.types = types

        if initial_env is None:
            initial_env = ScopedEnv.empty()

        self.env = initial_env

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
        if isinstance(stmt, syn.FunctionDef):
            return

        self.calculate(self.types[stmt.node_id], self.env, self.quals)

    def start_FunctionDef(self, fd: syn.FunctionDef):
        fn_typ = self.types[fd.node_id]
        assert isinstance(fn_typ, syn.ArrowType)

        self.env[fd.name] = fn_typ
        self.env.push_scope_mut()
        for x, t in fn_typ.args:
            self.calculate(t, self.env, self.quals)
            self.env[x] = t

        self.calculate(fn_typ.ret, self.env, self.quals)

    def end_FunctionDef(self, _: syn.FunctionDef):
        self.env.pop_scope_mut()

    def end_Assign(self, asgn: syn.Assign):
        self.env[asgn.name] = self.types[asgn.node_id]

    def start_Expr(self, expr: Expr):
        self.calculate(self.types[expr.node_id], self.env, self.quals)
