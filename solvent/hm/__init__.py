from typing import List

import solvent.syntax as syn
from solvent.env import ScopedEnv

from .check import check_stmts
from .subst import subst_stmts
from .unification import apply, free_vars, unify  # type: ignore


def solve(stmts: List[syn.Stmt], debug=False) -> syn.Type:
    typ, constrs, context = check_stmts(ScopedEnv.default(), stmts)

    if debug:
        print(f"Initial type: {typ}")
        print("== Constraints ==")
        print("\n".join([str(c) for c in constrs]))
        print("== Context ==")
        for k, v in context.items():
            print(f"{k} := {v}")

    if debug:
        print("== Unification ==")

    constrs, solution = unify(constrs, show_work=debug)

    if debug:
        print("== Solution ==")
        for k, v in solution.items():
            print(f"{k} := {v}")

        print("Normalized Program:")
        for s in stmts:
            print(s.to_string(include_types=True))
        print("======")

    solved_type = apply(typ, solution)
    subst_stmts(solution, stmts)
    return solved_type
