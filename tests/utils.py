import ast
import inspect
from typing import Dict, get_type_hints

from solvent import frontend, parse, prelude
from solvent import syntax as syn
from solvent.env import ScopedEnv
from solvent.position import Context


def assert_type(quals, expected, modules: Dict[str, str] | None = None):
    """
    A python annotatation that runs our end-to-end liquid type inference
    on a function definition and asserts that it has a particular type.
    """

    def inner(func):
        def repl():
            lines = inspect.getsource(func)
            pyast = ast.parse(lines)
            res = parse.Parser(get_type_hints(func, include_extras=True)).parse(pyast)

            fd = res[0]
            assert isinstance(fd, syn.FunctionDef)

            env = ScopedEnv.empty()
            if modules is not None:
                for prog_name, resolved_name in modules.items():
                    typ = prelude.lookup(resolved_name)
                    if typ is not None:
                        env[prog_name] = typ
                if len(modules) != 0:
                    env.push_scope_mut()

            syn.NameGenerator.reset()
            with Context(lines=lines.split("\n")):  # type: ignore
                types = frontend.check([fd], quals, env)
                assert str(types[fd.node_id]) == expected

        repl.__name__ = func.__name__

        return repl

    return inner
