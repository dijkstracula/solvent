from logging import debug
from typing import List

import solvent.syntax as syn
from solvent.env import ScopedEnv

from .check import check_stmts
from .subst import subst_stmts
from .unification import apply, free_vars, unify  # type: ignore


def solve(stmts: List[syn.Stmt], env: ScopedEnv | None = None) -> syn.Type:
    if env is None:
        env = ScopedEnv.default()

    typ, constrs, context = check_stmts(env, stmts)

    debug(f"Initial type: {typ}")
    debug("== Constraints ==")
    debug("\n".join([str(c) for c in constrs]))
    debug("== Context ==")
    for k, v in context.items():
        debug(f"{k} := {v}")

    debug("== Unification ==")

    constrs, solution = unify(constrs)

    debug("== Solution ==")
    for k, v in solution.items():
        debug(f"{k} := {v}")

    solved_type = apply(typ, solution)
    subst_stmts(solution, stmts)
    return solved_type
