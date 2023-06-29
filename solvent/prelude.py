"""
Standard type definitions that may be included in the context
of programs type-checked with solvent.
"""

from typing import Dict

from solvent.syntax import (
    ArrowType,
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
            )
        },
    ),
}


def lookup(name: str) -> Type | None:
    if name in PYTHON_STANDARD_LIBRARIES:
        return PYTHON_STANDARD_LIBRARIES[name]
    else:
        return None
