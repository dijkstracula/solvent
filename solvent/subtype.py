"""
Implement decidable subypting from the liquid type paper.
"""

from solvent import syn
from solvent.smt import expr_to_smt

import z3
from functools import reduce


def subtype(assumes, typ1, typ2):

    assumes_smt = reduce(
        lambda a, b: z3.And(a, b),
        [expr_to_smt(e) for e in assumes],
        True
    )

    match (typ1, typ2):
        case (syn.RType(value=t1, predicate=p1),
              syn.RType(value=t2, predicate=p2)) if t1 == t2:
            to_check = z3.Implies(
                z3.And(assumes_smt, expr_to_smt(p1)),
                expr_to_smt(p2)
            )

            # print(f"    {to_check}")

            s = z3.Solver()
            s.add(z3.Not(to_check))

            if s.check() == z3.unsat:
                return True
            else:
                print(s.model())
                return False
            
        case x:
            print(x)
            raise NotImplementedError
            

