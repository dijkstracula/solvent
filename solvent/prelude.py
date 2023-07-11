"""
Standard type definitions that may be included in the context
of programs type-checked with solvent.
"""

import typing as py
from typing import Dict, Generic, Self

from solvent.syntax import (
    ArrowType,
    HMType,
    ListType,
    ObjectType,
    PredicateVar,
    RType,
    Type,
    TypeVar,
)

PYTHON_STANDARD_LIBRARIES: Dict[str, Type] = {
    "typing": ObjectType(
        "typing",
        {},
        {"TypeVar": ArrowType({}, [("name", RType.str())], ObjectType("TypeVar"))},
    ),
    "pandas": ObjectType(
        "pandas",
        {},
        {
            "Series": ArrowType(
                type_abs={"T": "type", "K": "pred"},
                args=[("l", ListType(RType(TypeVar("T"), PredicateVar("K"))))],
                ret=ObjectType(
                    "Series",
                    {},
                    {
                        "max": ArrowType(
                            {}, [], RType(TypeVar("T"), PredicateVar("K"))
                        ),
                        "data": ListType(RType(TypeVar("T"), PredicateVar("K"))),
                    },
                ),
            ),
        },
    ),
    "test": Class(
        name="Series",
        type_abs=["T"],
    ),
}

T = py.TypeVar("T")
K = py.TypeVar("K")
K1 = py.TypeVar("K1")


class Test(Generic[T, K]):
    def __init__(self, data: py.List[py.Annotated[T, K]]):
        self.data: py.List[py.Annotated[T, K]] = data

    def max(self: Self) -> py.Annotated[T, K]:
        ...

    def __div__(self, other: int) -> "Test[T, K1]":
        ...


def lookup(name: str) -> Type | None:
    if name in PYTHON_STANDARD_LIBRARIES:
        return PYTHON_STANDARD_LIBRARIES[name]
    else:
        return None
