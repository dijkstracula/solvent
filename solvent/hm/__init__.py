from logging import debug, info
from typing import Dict, List

import solvent.syntax as syn
from solvent import visitor
from solvent.annotate import Annotate
from solvent.env import ScopedEnv
from solvent.qualifiers import predicate

from .constraints import HindleyMilner, check_stmts
from .subst import Subst  # type: ignore
from .unification import apply, free_vars, unify  # type: ignore


def solve(
    stmts: List[syn.Stmt], types: Dict[int, syn.Type], env: ScopedEnv | None = None
) -> tuple[List[syn.Stmt], Dict[int, syn.Type]]:
    if env is None:
        env = ScopedEnv.empty()

    info("New Hindley Milner")
    hm = HindleyMilner(types, env)
    hm.visit_stmts(stmts)
    info("\n".join([str(c) for c in hm.constrs]))
    info("====== end ======")

    # raise Exception()

    # typ, constrs, context = check_stmts(types, env, stmts)

    # info(f"Initial type: {typ}")
    # info("== Constraints ==")
    # info("\n".join([str(c) for c in constrs]))
    # info("== Context ==")
    # for k, v in context.items():
    #     info(f"{k} := {v}")

    info("== Unification ==")
    _, solution = unify(hm.constrs)

    info("== Solution ==")
    for k, v in solution.items():
        info(f"{k} := {v}")

    def replace(t: syn.Type) -> syn.Type:
        match t:
            case syn.HMType(syn.TypeVar(name=n)) if n in solution:
                return solution[n]
            case syn.RType(base=syn.TypeVar(name=n), predicate=p) if n in solution:
                return solution[n].set_predicate(p)
            case _:
                return t

    new_types: Dict[int, syn.Type] = {
        id: t.mapper(replace) for id, t in hm.types.items()
    }

    annotator2 = Annotate(env.clone(), initial_id_map=new_types)
    stmts = annotator2.visit_stmts(stmts)
    new_types: Dict[int, syn.Type] = annotator2.id_map

    # _ = apply(typ, solution)
    # subst_stmts(solution, stmts)
    stmts = Subst(solution).visit_stmts(stmts)

    for s in stmts:
        info(s.to_string(new_types, include_types=True))

    # function_types = {}
    # for s in stmts:
    #     if isinstance(s, syn.FunctionDef):
    #         function_types[s.name] = s.typ

    return (stmts, new_types)
