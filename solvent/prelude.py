"""
Standard type definitions that may be included in the context
of programs type-checked with solvent.
"""

from typing import Dict

from solvent.syntax import (
    ArrowType,
    Int,
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
        [],
        {"TypeVar": ArrowType([("name", RType.str())], ObjectType("TypeVar"))},
    ),
    # HACK: hardcoding the predicate var and not using fresh
    "pandas": ObjectType(
        "pandas",
        [],
        {
            "Series": ArrowType(
                args=[("l", ListType(RType(base=Int(), predicate=PredicateVar("K"))))],
                ret=ObjectType(
                    "Series",
                    ["T"],
                    {
                        "max": ArrowType([], RType(TypeVar("T"), PredicateVar("K"))),
                        "data": ListType(RType(TypeVar("T"), PredicateVar("K"))),
                    },
                ),
            )
        },
    ),
}


def lookup(name: str) -> Type | None:
    if name in PYTHON_STANDARD_LIBRARIES:
        return PYTHON_STANDARD_LIBRARIES[name]
    else:
        return None
