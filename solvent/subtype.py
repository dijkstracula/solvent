"""
Implement decidable subypting from the liquid type paper.
"""

from solvent import syn
from solvent.smt import expr_to_smt

import z3
from functools import reduce


def subtype(assumes, typ1, typ2):

    assumes_smt = reduce(lambda a, b: z3.And(a, b), [expr_to_smt(e) for e in assumes])

    match (typ1, typ2):
        case (syn.RType(value=t1, predicate=p1), syn.RType(value=t2, predicate=p2)) if t1 == t2:
            to_check = z3.Implies(
                z3.And(assumes_smt, expr_to_smt(p1)),
                expr_to_smt(p2)
            )

            print(to_check)

            s = z3.Solver()
            s.add(to_check)

            print(s.check())
            
        case x:
            print(x)
            raise NotImplementedError
            

