from solvent import qualifiers, syntax as syn, constraints, unification, liquid

from typing import List, cast


def check(stmts: List[syn.Stmt], quals: List[qualifiers.Qualifier], debug=False):
    """
    Run Liquid-type inference and checking.
    """

    typ, constrs, context = constraints.check_stmts({}, [], stmts)

    if debug:
        print(f"Initial type: {typ}")
        print("== Constraints ==")
        print("\n".join([str(c) for c in constrs]))
        print("== Context ==")
        for k, v in context.items():
            print(f"{k} := {v}")

    if debug:
        print("== Unification ==")

    constrs, solution = unification.unify(constrs, show_work=debug)

    if debug:
        print("== Solution ==")
        for k, v in solution.items():
            print(f"{k} := {v}")

    inferred_base_typ = unification.apply(typ, solution)
    context = unification.apply_context(context, solution)

    subtype_eqs = cast(
        List[constraints.SubType],
        list(filter(lambda x: isinstance(x, constraints.SubType), constrs)),
    )
    predvar_solution = liquid.solve(context, subtype_eqs, quals, show_work=debug)

    if debug:
        for k, v in predvar_solution.items():
            print(f"{k} := {v}")

    return alpha_rename(liquid.apply(inferred_base_typ, predvar_solution))


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
