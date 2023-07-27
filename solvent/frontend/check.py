from logging import debug, info
from typing import Dict, List

from ansi.color import fg, fx

from solvent import hm, liquid, normalize, qualifiers
from solvent import syntax as syn
from solvent.annotate import Annotate
from solvent.env import ScopedEnv
from solvent.syntax import Type
from solvent.template import Templatizer


def infer_base(fd: syn.FunctionDef) -> Type:
    stmts = normalize.normalize([fd])
    annotator = Annotate()
    stmts = annotator.visit_stmts(stmts)
    stmts, types = hm.solve(stmts, annotator.id_map)

    print(fd.node_id)
    for id, ty in types.items():
        print(f"{id}: {ty}")

    return alpha_rename(types[fd.node_id])


def number(blob: str) -> str:
    lines = blob.split("\n")
    ret = []
    total = len(lines)
    width = len(str(total))
    for lineno, l in enumerate(lines, 1):
        padding = " " * (width - len(str(lineno)))
        ret += [f"{fg.darkgray}{lineno}{fx.reset}{padding} {l}"]
    return "\n".join(ret)


def info_stmts(stmts: List[syn.Stmt], types=None, include_types=False):
    gather = "\n\n".join(
        [number(s.to_string(types=types, include_types=include_types)) for s in stmts]
    )
    info(gather)


def check(
    stmts: List[syn.Stmt],
    quals: List[qualifiers.Qualifier],
    env: ScopedEnv | None = None,
) -> Dict[int, Type]:
    """
    Run Liquid-type inference and checking.
    """

    if env is None:
        env = ScopedEnv.empty()

    stmts = normalize.normalize(stmts)
    info("Normalized Program:")
    info_stmts(stmts)

    annotator = Annotate(env.clone())
    stmts = annotator.visit_stmts(stmts)
    types: Dict[int, Type] = annotator.id_map

    debug(
        "Forward type annotation",
        "\n".join([f"{id}: {ty}" for id, ty in types.items()]),
    )

    info_stmts(stmts, types=types, include_types=True)

    stmts, types = hm.solve(stmts, types, env=env)

    templatizer = Templatizer(types, env.clone())
    stmts = templatizer.visit_stmts(stmts)
    debug(
        "Template program types",
        "\n".join([f"{id}: {ty}" for id, ty in templatizer.types.items()]),
    )
    info_stmts(stmts, types=templatizer.types, include_types=True)

    # _, constrs, ctx = constraints.check_stmts(ScopedEnv.empty(), [], stmts)
    # for c in constrs:
    #     AssertNoHmTypes().check_constraint(c)

    # info("context:")
    # msg = ""
    # for scope in ctx.scopes:
    #     for k, v in scope.items():
    #         msg += f"{k}: {v}\n"
    #     msg += "== scope ==\n"
    # info(msg)

    predvar_solution = liquid.solve(
        stmts, templatizer.constraints, quals, templatizer.types
    )

    info("== Predicate Variable Solution ==")
    for k, v in predvar_solution.items():
        info(f"{k} := {v}")

    types = {
        id: liquid.apply(ty, predvar_solution) for id, ty in templatizer.types.items()
    }

    info_stmts(stmts, types, include_types=True)

    return types


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
