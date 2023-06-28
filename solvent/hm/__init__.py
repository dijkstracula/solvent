from logging import info
from typing import Dict, List

import solvent.syntax as syn
from solvent.env import ScopedEnv

from .check import check_stmts
from .subst import Subst, subst_stmts
from .unification import apply, free_vars, unify  # type: ignore


def solve(
    stmts: List[syn.Stmt], env: ScopedEnv | None = None
) -> tuple[List[syn.Stmt], Dict[str, syn.Type]]:
    if env is None:
        env = ScopedEnv.empty()

    typ, constrs, context = check_stmts(env, stmts)

    info(f"Initial type: {typ}")
    info("== Constraints ==")
    info("\n".join([str(c) for c in constrs]))
    info("== Context ==")
    for k, v in context.items():
        info(f"{k} := {v}")

    info("== Unification ==")
    constrs, solution = unify(constrs)

    info("== Solution ==")
    for k, v in solution.items():
        info(f"{k} := {v}")

    _ = apply(typ, solution)
    # subst_stmts(solution, stmts)
    stmts = Subst(solution).visit_stmts(stmts)

    for s in stmts:
        info(s.to_string(True))

    function_types = {}
    for s in stmts:
        if isinstance(s, syn.FunctionDef):
            function_types[s.name] = s.typ

    return (stmts, function_types)
