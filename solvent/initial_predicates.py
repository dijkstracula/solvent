"""
Generate the initial candidate predicates for a program by walking
over an annotated program and including all qualifiers that use in
scope variables.
"""

from typing import Dict, List

from solvent import qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnvVisitor

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

    def start_Stmt(self, stmt: syn.Stmt):
        super().start_Stmt(stmt)

        print("== here ==")
        print(list(self.env.keys()))
        pred = qualifiers.predicate(self.env, self.quals)
        print(pred)

        for pvar in predicate_variables(stmt.typ):
            print("  pvar:", pvar)
            self.solution[pvar] = pred
