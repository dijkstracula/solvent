from solvent import syn, constraints

from typing import List


def check(stmts: List[syn.Stmt], quals: List[str]):
    """
    Run Liquid-type inference and checking.
    """

    typ, constrs, context = constraints.check_stmts({}, [], stmts)

    print(typ)
    print("\n".join([str(c) for c in constrs]))
    print(context)

    pass
