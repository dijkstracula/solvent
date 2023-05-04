from typing import List

from solvent import hm, normalize, qualifiers
from solvent import syntax as syn
from solvent import unification
from solvent.constraints import Env
from solvent.syntax import Type


def infer_base(stmts: List[syn.Stmt], debug=False) -> Type:
    norm_stmts = normalize.normalize(stmts)

    if debug:
        print("Normalized Program:")
        for s in norm_stmts:
            print(s)
        print("======")

    typ, constrs, context = hm.check_stmts(Env.empty(), norm_stmts)

    if debug:
        print(f"Initial type: {typ}")
        print("== Constraints ==")
        print("\n".join([str(c) for c in constrs]))
        print("== Context ==")
        for k, v in context.items:
            print(f"{k} := {v}")

    if debug:
        print("== Unification ==")

    constrs, solution = unification.unify(constrs, show_work=debug)

    if debug:
        print("== Solution ==")
        for k, v in solution.items():
            print(f"{k} := {v}")

    solved_type = unification.apply(typ, solution)
    return alpha_rename(solved_type)


def check(stmts: List[syn.Stmt], quals: List[qualifiers.Qualifier], debug=False):
    """
    Run Liquid-type inference and checking.
    """

    inferred_base_typ = infer_base(stmts, debug)

    if debug:
        print("== Inferred Base Type ==")
        print(f"{inferred_base_typ}")

    return inferred_base_typ  # TODO: now do liquid type inference
    # predvar_solution = liquid.solve(constrs, quals, show_work=debug)

    # if debug:
    #     print("== Predicate Variable Solution ==")
    #     for k, v in predvar_solution.items():
    #         print(f"{k} := {v}")

    # return alpha_rename(liquid.apply(inferred_base_typ, predvar_solution))


NAMES = "abcdefghijklmnopqrstuvwxyz"


def alpha_rename(typ: syn.Type) -> syn.Type:
    """
    Renames type variables in `typ'.
    """

    rename_map = {}
    for i, var in enumerate(set(unification.free_vars(typ))):
        if i < len(NAMES):
            rename_map[var] = syn.TypeVar(NAMES[i])
        else:
            raise NotImplementedError

    return unification.apply(typ, rename_map)
