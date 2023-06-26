from logging import debug

from solvent.env import ScopedEnvVisitor
from solvent.syntax import Call


class TypeApplication(ScopedEnvVisitor):
    def start_Call(self, op: Call):
        # the thing that I want here is whether the type of `op.function_name`
        # has any type arguments
        debug(repr(op.function_name))
        super().start_Call(op)
