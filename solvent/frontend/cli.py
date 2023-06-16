import ast

import click

from solvent import parse

# from typing import get_type_hints


@click.command()
@click.argument("files", type=click.File("r"), nargs=-1)
def cli(files):
    for f in files:
        print(f)
        pyast = ast.parse(f.read())
        # type_hints = get_type_hints(pyast, include_extras=True)
        # print(type_hints)
        stmts = parse.Parser({}, strict=False).parse(pyast)
        for s in stmts:
            print(s.to_string(include_types=True))
