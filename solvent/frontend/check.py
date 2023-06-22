from logging import debug
from typing import Dict, List

from ansi.color import fg, fx

from solvent import constraints, hm, liquid, normalize, qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.sanitize import AssertHavePosition, AssertNoHmTypes
from solvent.syntax import Type
from solvent.template import Templatizer


def infer_base(stmts: List[syn.Stmt]) -> Dict[str, Type]:
    norm_stmts = normalize.normalize(stmts)
    solved_type = hm.solve(norm_stmts)

    debug("Normalized Program:")
    for s in norm_stmts:
        debug(s)
    debug("======")

    return {k: alpha_rename(v) for k, v in solved_type.items()}


def number(blob: str) -> str:
    lines = blob.split("\n")
    ret = []
    total = len(lines)
    width = len(str(total))
    for lineno, l in enumerate(lines, 1):
        padding = " " * (width - len(str(lineno)))
        ret += [f"{fg.darkgray}{lineno}{fx.reset}{padding} {l}"]
    return "\n".join(ret)


def debug_stmts(stmts: List[syn.Stmt], include_types=False):
    gather = "\n\n".join([number(s.to_string(include_types)) for s in stmts])
    debug(gather)


def check(stmts: List[syn.Stmt], quals: List[qualifiers.Qualifier]) -> Dict[str, Type]:
    """
    Run Liquid-type inference and checking.
    """

    stmts = normalize.normalize(stmts)
    debug("Normalized Program:")
    debug_stmts(stmts, True)

    base_types = hm.solve(stmts)
    debug("HmType program:")
    debug_stmts(stmts, True)

    debug("== Inferred Base Types ==")
    debug(
        "\n".join(
            [f"{fn_name}: {alpha_rename(typ)}" for fn_name, typ in base_types.items()]
        )
    )

    stmts = Templatizer().visit_stmts(stmts)
    AssertHavePosition().visit_stmts(stmts)
    debug("Template program:")
    debug_stmts(stmts, True)
    AssertNoHmTypes().visit_stmts(stmts)

    _, constrs, ctx = constraints.check_stmts(ScopedEnv.default(), [], stmts)
    for c in constrs:
        AssertNoHmTypes().check_constraint(c)

    debug("context:")
    msg = ""
    for scope in ctx.scopes:
        for k, v in scope.items():
            msg += f"{k}: {v}\n"
        msg += "== scope ==\n"
    debug(msg)

    predvar_solution = liquid.solve(stmts, constrs, quals)

    debug("== Predicate Variable Solution ==")
    for k, v in predvar_solution.items():
        debug(f"{k} := {v}")

    return {
        k: alpha_rename(liquid.apply(v, predvar_solution))
        for k, v in ctx.scopes[0].items()
    }


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
