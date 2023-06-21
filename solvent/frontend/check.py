from logging import debug
from typing import List

from solvent import constraints, hm, liquid, normalize, qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.sanitize import AssertHavePosition, AssertNoHmTypes
from solvent.syntax import Type
from solvent.template import Templatizer


def infer_base(stmts: List[syn.Stmt]) -> Type:
    norm_stmts = normalize.normalize(stmts)
    solved_type = hm.solve(norm_stmts)

    debug("Normalized Program:")
    for s in norm_stmts:
        debug(s)
    debug("======")

    return alpha_rename(solved_type)


def number(blob: str) -> str:
    lines = blob.split("\n")
    ret = []
    total = len(lines)
    width = len(str(total))
    for lineno, l in enumerate(lines, 1):
        padding = " " * (width - len(str(lineno)))
        ret += [f"{lineno}{padding}|{l}"]
    return "\n".join(ret)


def check(stmts: List[syn.Stmt], quals: List[qualifiers.Qualifier]):
    """
    Run Liquid-type inference and checking.
    """

    stmts = normalize.normalize(stmts)
    debug("Normalized Program")
    for s in stmts:
        debug(number(s.to_string()))

    inferred_base_typ = hm.solve(stmts)
    debug("HmType program:")
    for s in stmts:
        debug(number(s.to_string(include_types=True)))
    debug("======")

    stmts = Templatizer().visit_stmts(stmts)
    AssertHavePosition().visit_stmts(stmts)
    debug("Template program:")
    for s in stmts:
        debug(number(s.to_string(include_types=True)))
    debug("======")
    AssertNoHmTypes().visit_stmts(stmts)

    debug("== Inferred Base Type ==")
    debug(f"{inferred_base_typ}")

    typ, constrs, _ = constraints.check_stmts(ScopedEnv.default(), [], stmts)
    for c in constrs:
        AssertNoHmTypes().check_constraint(c)

    predvar_solution = liquid.solve(stmts, constrs, quals)

    debug("== Predicate Variable Solution ==")
    for k, v in predvar_solution.items():
        debug(f"{k} := {v}")

    return alpha_rename(liquid.apply(typ, predvar_solution))


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
