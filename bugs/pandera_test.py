import pandas as pd
import numpy as np
import pandera as pa
from pandera.typing import Series


def example2():
    """
    A pandera specification that rules out both Name and Tag
    being both null. This seems maybe hard to specify with
    Refinement types.
    """

    data = [
        ["Alex", 10, "t1"],
        ["Bob", 12, None],
        ["Clarke", 13, "t3"],
        [None, 14, "t3"],
        [None, 15, None],
    ]
    df = pd.DataFrame(data, columns=["Name", "Age", "Tag"])
    schema = pa.DataFrameSchema(
        checks=pa.Check(
            lambda df: ~(df["Name"].isnull() & df["Tag"].isnull()), ignore_na=False
        )
    )

    try:
        schema.validate(df)
    except pa.errors.SchemaErrors as err:
        print("Schema errors and failure cases:")
        print(err.failure_cases)


def preprocess(df: pd.DataFrame) -> pd.DataFrame:
    """
    Some unstructured 'normalization' code that doesn't encode any
    information about what the columns are.
    """

    df = df.copy()
    c1_min, c1_max = df["col1"].min(), df["col1"].max()
    df["col1"] = 0 if c1_min == c1_max else (df["col1"] - c1_min) / (c1_max - c1_min)
    df["month"] = df["date"].dt.month
    df["comment"] = df["comment"].str.lower()
    return df


def pandera2():
    """
    Solvent type:
      DataFrame[
        "column1": {int | V <= 10}],
        "column2": {float | V < -1.2}
        "column3": {str | V.starts_with('value_')}
      ]

    """

    # data to validate
    df = pd.DataFrame(
        {
            "column1": [1, 4, 0, 10, 9],
            "column2": [-1.3, -1.4, -2.9, -10.1, -20.4],
            "column3": ["value_1", "value_2", "value_3", "value_2", "value_1"],
        }
    )

    class Schema(pa.DataFrameModel):
        column1: Series[int] = pa.Field(le=10)
        column2: Series[float] = pa.Field(lt=-1.2)
        column3: Series[str] = pa.Field(str_startswith="value_")

        @pa.check("column3")
        def column_3_check(cls, series: Series[str]) -> Series[bool]:
            """Check that column3 values have two elements after being split with '_'"""
            return series.str.split("_", expand=True).shape[1] == 2

    Schema.validate(df)


def norm_example():
    df = pd.DataFrame(np.random.randint(0, 100, size=(4, 2)), columns=list("AB"))
    # DataFrame["A": {int | 0 <= V <= 100}, "B": {int | O <= V < 100}]
    print(df.to_string())
    df["norm"] = df["A"] / df["A"].max()
    print(df.to_string())
    # DataFrame[.., "norm": {float | 0 <= V <= 1.0}]
    return df


def reindexing():
    """
    Reindexing a dataframe can cause the types of columns to change
    because there is only allowed to be a single fill value. If two
    columns need filling of different types, then the type of one of
    the columns will be cast to 'object'. Besides causing bugs, this
    can lead to degraded performance.
    """

    df = pd.DataFrame.from_records(
        (("a", 1, True), ("b", 2, False)), columns=tuple("xyz")
    )
    df2 = df.reindex((1, 0, 2))
    print(df.to_string())
    print(df2.to_string())
    print(df.dtypes.tolist(), df2.dtypes.tolist())
    assert df.dtypes.tolist() == df2.dtypes.tolist()


norm_example()
