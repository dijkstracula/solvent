import ast
from logging import info

import click

from solvent import Q, V, _, frontend, parse
from solvent import syntax as syn
from solvent.frontend import log
from solvent.position import Context

# from typing import get_type_hints

# TODO: add a proper mechanism for adding qualifiers
QUALS = [
    _ < V,
    V < _,
    _ <= V,
    V <= _,
    Q[0] <= V,
    V <= Q[0],
]


# coloredlogs.DEFAULT_LOG_FORMAT =
# coloredlogs.DEFAULT_FIELD_STYLES = {
#     "levelname": {"bold": True},
#     "name": {"color": "blue"},
#     "programname": {"color": "cyan"},
#     "username": {"color": "yellow"},
# }


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

        syn.NameGenerator.reset()
        with Context(lines=lines.split("\n")):
            typ = frontend.check(stmts, QUALS)
            info(typ)
