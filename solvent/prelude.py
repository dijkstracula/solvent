"""
Standard type definitions that may be included in the context
of programs type-checked with solvent.
"""

from typing import Dict

from solvent.syntax import (
    ArithBinOp,
    ArrowType,
    BoolOp,
    Call,
    Class,
    Conjoin,
    DictType,
    GetAttr,
    HMType,
    ListType,
    PredicateVar,
    RType,
    SelfType,
    Str,
    Type,
    TypeVar,
    V,
    Variable,
)

PYTHON_STANDARD_LIBRARIES: Dict[str, Type] = {
    "typing": DictType(
        {
            "TypeVar": Class(
                "TypeVar",
                [],
                ArrowType({}, [("name", HMType(Str()))], SelfType()),
            )
        }
    ),
    "pandas": DictType(
        {
            "Series": Class(
                name="Series",
                type_abs=["T"],
                constructor=ArrowType(
                    {"T": "type", "K": "pred"},
                    [("l", ListType(RType(TypeVar("T"), PredicateVar("K"))))],
                    SelfType([RType(TypeVar("T"), PredicateVar("K"))]),
                ),
                fields={
                    "max": ArrowType(
                        {"K": "pred"},
                        [("self", SelfType([RType(TypeVar("T"), PredicateVar("K"))]))],
                        RType(TypeVar("T"), PredicateVar("K")),
                    ),
                    "el": ArrowType(
                        {"K": "pred"},
                        [("self", SelfType([RType(TypeVar("T"), PredicateVar("K"))]))],
                        RType(TypeVar("T"), PredicateVar("K")),
                    ),
                    "__mul__": ArrowType(
                        {},
                        [
                            (
                                "self",
                                SelfType([HMType(TypeVar("T"))]),
                            ),
                            ("other", HMType.int()),
                        ],
                        SelfType(
                            [
                                RType(
                                    TypeVar("T"),
                                    Conjoin(
                                        [
                                            BoolOp(
                                                V(),
                                                "==",
                                                ArithBinOp(
                                                    Call(
                                                        GetAttr(Variable("self"), "el"),
                                                        [],
                                                    ),
                                                    "*",
                                                    Variable("other"),
                                                ),
                                            )
                                        ]
                                    ),
                                )
                            ]
                        ),
                    ),
                },
            ),
        },
    ),
}


def lookup(name: str) -> Type | None:
    if name in PYTHON_STANDARD_LIBRARIES:
        return PYTHON_STANDARD_LIBRARIES[name]
    else:
        return None
