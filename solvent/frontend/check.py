from logging import info
from typing import Dict, List

from ansi.color import fg, fx

from solvent import constraints, hm, liquid, normalize, qualifiers
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.sanitize import AssertHavePosition, AssertNoHmTypes
from solvent.syntax import Type
from solvent.template import Templatizer
from solvent.type_applications import TypeApplication


def infer_base(stmts: List[syn.Stmt]) -> Dict[str, Type]:
    norm_stmts = normalize.normalize(stmts)
    _, solved_type = hm.solve(norm_stmts)

    info("Normalized Program:")
    for s in norm_stmts:
        info(s)
    info("======")

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


def info_stmts(stmts: List[syn.Stmt], include_types=False):
    gather = "\n\n".join(
        [number(s.to_string(include_types=include_types)) for s in stmts]
    )
    info(gather)


def check(
    stmts: List[syn.Stmt],
    quals: List[qualifiers.Qualifier],
    env: ScopedEnv | None = None,
) -> Dict[str, Type]:
    """
    Run Liquid-type inference and checking.
    """

    if env is None:
        env = ScopedEnv.empty()

    stmts = normalize.normalize(stmts)
    info("Normalized Program:")
    info_stmts(stmts)

    info("Inserting type applications")
    stmts = TypeApplication(env.clone()).visit_stmts(stmts)
    info_stmts(stmts)

    stmts, base_types = hm.solve(stmts, env=env)
    info("HmType program:")
    info_stmts(stmts, True)

    info("== Inferred Base Types ==")
    info(
        "\n".join(
            [f"{fn_name}: {alpha_rename(typ)}" for fn_name, typ in base_types.items()]
        )
    )

    stmts = Templatizer(env).visit_stmts(stmts)
    AssertHavePosition().visit_stmts(stmts)
    info("Template program:")
    info_stmts(stmts, True)
    AssertNoHmTypes().visit_stmts(stmts)

    _, constrs, ctx = constraints.check_stmts(ScopedEnv.empty(), [], stmts)
    for c in constrs:
        AssertNoHmTypes().check_constraint(c)

    info("context:")
    msg = ""
    for scope in ctx.scopes:
        for k, v in scope.items():
            msg += f"{k}: {v}\n"
        msg += "== scope ==\n"
    info(msg)

    predvar_solution = liquid.solve(stmts, constrs, quals)

    info("== Predicate Variable Solution ==")
    for k, v in predvar_solution.items():
        info(f"{k} := {v}")

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
