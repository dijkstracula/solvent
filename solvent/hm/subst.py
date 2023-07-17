from logging import debug
from typing import List

from solvent import syntax as syn
from solvent.syntax import Expr, HMType, Stmt, TypeApp, TypeVar
from solvent.visitor import Visitor

from .unification import Solution, free_vars, subst_one


class Subst(Visitor):
    def start(self, solution: Solution):
        self.solution = solution

    def end_TypeApp(self, op: TypeApp) -> TypeApp:
        new_args = []
        for a in op.arglist:
            match a:
                case HMType(TypeVar(name=n)) if n in self.solution:
                    new_args += [self.solution[n]]
                case x:
                    new_args += [x]

        return TypeApp(op.expr, new_args).pos(op)
