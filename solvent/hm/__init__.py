from logging import debug, warn
from typing import Dict, List

import solvent.syntax as syn
from solvent.env import ScopedEnv

from .check import check_stmts
from .subst import subst_stmts
from .unification import apply, free_vars, unify  # type: ignore


def solve(stmts: List[syn.Stmt], env: ScopedEnv | None = None) -> Dict[str, syn.Type]:
    if env is None:
        env = ScopedEnv.empty()

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

    _ = apply(typ, solution)
    subst_stmts(solution, stmts)

    function_types = {}
    for s in stmts:
        if isinstance(s, syn.FunctionDef):
            function_types[s.name] = s.typ

    return function_types
