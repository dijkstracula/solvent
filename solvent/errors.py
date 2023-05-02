class TypeError(Exception):
    def __init__(self, c):
        msg = f"{c.lhs} is incompatible with {c.rhs}"
        self.msg = msg
        self.constraint = c
        super().__init__(msg)
