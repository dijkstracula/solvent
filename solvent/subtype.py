"""
Implement decidable subypting from the liquid type paper.
"""

from functools import reduce
from logging import info
from typing import Dict

import z3

from solvent import constraints as constr
from solvent import env, smt
from solvent import syntax as syn


def check(
    context: env.ScopedEnv, types: Dict[int, syn.Type], assumes, typ1, typ2
) -> bool:
    match (typ1, typ2):
        case (
            syn.RType(base=t1, predicate=syn.Conjoin(cs1)),
            syn.RType(base=t2, predicate=syn.Conjoin(cs2)),
        ) if t1 == t2:
            to_smt = smt.ToSmt(context, types)

            ctx_smt = z3.simplify(
                reduce(
                    lambda a, b: z3.And(a, b),
                    [to_smt.from_type(x, t) for x, t in context.items()],
                    True,
                )
            )

            to_check = z3.Implies(
                z3.And(
                    ctx_smt,
                    z3.And(to_smt.from_exprs(assumes), to_smt.from_exprs(cs1)),
                ),
                to_smt.from_exprs(cs2),
            )

            info("SMT:", to_check)

            s = z3.Solver()
            s.add(z3.Not(to_check))

            if s.check() == z3.unsat:
                return True
            else:
                info(f"fail with model: {s.model()}")

                return False

        case (syn.ArrowType(), syn.ArrowType()):
            raise NotImplementedError(typ1, typ2)
        case x:
            raise Exception(f"We are not handling this case: {x}")
            # return False


def check_constr(c: constr.SubType, types: Dict[int, syn.Type]) -> bool:
    return check(c.context, types, c.assumes, c.lhs, c.rhs)
