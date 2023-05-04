from typing import List

from solvent import hm, normalize, qualifiers
from solvent import syntax as syn
from solvent.syntax import Type


def infer_base(stmts: List[syn.Stmt], debug=False) -> Type:
    norm_stmts = normalize.normalize(stmts)
    solved_type = hm.solve(norm_stmts, debug)

    if debug:
        print("Normalized Program:")
        for s in norm_stmts:
            print(s)
        print("======")

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
    for i, var in enumerate(set(hm.free_vars(typ))):
        if i < len(NAMES):
            rename_map[var] = syn.TypeVar(NAMES[i])
        else:
            raise NotImplementedError

    return hm.apply(typ, rename_map)
