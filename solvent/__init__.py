from typing import Annotated

import solvent.syntax
from solvent.frontend.annotations import infer  # type: ignore
from solvent.qualifiers import Magic, MagicQ

_ = Magic(solvent.syntax.Star())
V = Magic(solvent.syntax.V())
Q = MagicQ()


Refine = Annotated


class Pred(solvent.syntax.PredicateVar):
    """
    Allows specifying predicates as the generic values of python types.
    """

    def __class_getitem__(cls, _):
        pass
