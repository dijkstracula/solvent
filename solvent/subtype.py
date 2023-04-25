"""
Implement decidable subypting from the liquid type paper.
"""

from solvent import syntax as syn, smt

import z3
from functools import reduce


def subtype(assumes, typ1, typ2, show_work=False):
    match (typ1, typ2):
        case (
            syn.RType(base=t1, predicate=syn.Conjoin(cs1)),
            syn.RType(base=t2, predicate=syn.Conjoin(cs2)),
        ) if t1 == t2:
            assumes_smt = reduce(
                lambda a, b: z3.And(a, b), [smt.from_expr(e) for e in assumes], True
            )

            to_check = z3.Implies(
                z3.And(assumes_smt, smt.from_exprs(cs1)), smt.from_exprs(cs2)
            )

            # print(f"    {to_check}")

            s = z3.Solver()
            s.add(z3.Not(to_check))

            if s.check() == z3.unsat:
                return True
            else:
                if show_work:
                    print(f"fail with model: {s.model()}")

                return False

        case (syn.ArrowType(), syn.ArrowType()):
            print(typ1, typ2)
            raise NotImplementedError
        case x:
            print(x)
            return False
