from solvent.env import ScopedEnv, ScopedEnvVisitor


class Annotate(ScopedEnvVisitor):

    def __init__(self, *args, **kwargs):
        super().__init__(args, kwargs)
        self.id_map = {}

    def start(self, initial_env: ScopedEnv | None = None):
        super().start(initial_env)

    def end_
