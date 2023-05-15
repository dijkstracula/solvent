from typing import Annotated

import solvent.syntax
from solvent.frontend.annotations import infer
from solvent.qualifiers import Magic, MagicQ

_ = Magic(solvent.syntax.Star())
V = Magic(solvent.syntax.V())
Q = MagicQ()


Refine = Annotated
