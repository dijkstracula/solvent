from typing import List

from solvent import constraints, hm, liquid, normalize, qualifiers
from solvent import syntax as syn
from solvent.env import Env
from solvent.syntax import Type
from solvent.template import Templatizer


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

    stmts = normalize.normalize(stmts)
    inferred_base_typ = hm.solve(stmts, False)
    Templatizer().visit_stmts(stmts)

    if debug:
        print("== Inferred Base Type ==")
        print(f"{inferred_base_typ}")

    if debug:
        print("Templated program:")
        for s in stmts:
            print(s.to_string(include_types=True))
        print("======")

    typ, constrs, context = constraints.check_stmts(Env.empty(), [], stmts)

    predvar_solution = liquid.solve(constrs, quals, show_work=debug)

    if debug:
        print("== Predicate Variable Solution ==")
        for k, v in predvar_solution.items():
            print(f"{k} := {v}")

    return alpha_rename(liquid.apply(inferred_base_typ, predvar_solution))


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
