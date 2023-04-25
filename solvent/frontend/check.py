from solvent import syn, constraints, unification

from typing import List, cast


def check(stmts: List[syn.Stmt], quals: List[str], debug=False):
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

    base_eqs = cast(
        List[constraints.BaseEq],
        list(filter(lambda x: isinstance(x, constraints.BaseEq), constrs)),
    )
    solution = unification.unify(base_eqs, show_work=debug)

    if debug:
        print("== Solution ==")
        for k, v in solution.items():
            print(f"{k} := {v}")

    inferred_base_typ = unification.apply(typ, solution)
    return inferred_base_typ
