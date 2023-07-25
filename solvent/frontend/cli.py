import ast
from logging import info

import click

from solvent import Q, V, _, frontend, parse, prelude
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.frontend import log
from solvent.position import Context

# TODO: add a proper mechanism for adding qualifiers
QUALS = [
    _ < V,
    V < _,
    _ <= V,
    V <= _,
    Q[0] <= V,
    V <= Q[0],
    Q[0] < V,
    V < Q[0],
]


@click.command()
@click.argument("files", type=click.File("r"), nargs=-1)
@click.option("--not-strict", is_flag=True)
@click.option("--debug", is_flag=True)
def cli(files, not_strict, debug):
    log.install(debug)

    for f in files:
        lines = f.read()
        pyast = ast.parse(lines)
        p = parse.Parser({}, strict=not not_strict)
        stmts = p.parse(pyast)

        env = ScopedEnv.empty()
        for prog_name, resolved_name in p.modules.items():
            typ = prelude.lookup(resolved_name)
            if typ is not None:
                env[prog_name] = typ
        env.push_scope()

        syn.NameGenerator.reset()
        with Context(lines=lines.split("\n")):
            types = frontend.check(stmts, QUALS, env)
            for name, typ in types.items():
                info(f"{name}: {typ}")
