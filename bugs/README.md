# A List of Bug Types for Pandas

## Typed Dataframe libraries

- [pandera](https://pandera.readthedocs.io/en/stable/)
- [opulent-pandas](https://github.com/danielvdende/opulent-pandas)
- [PandasSchema](https://github.com/TMiguelT/PandasSchema)
- [pandas-validator](https://github.com/c-data/pandas-validator)
- [table\_enforcer](https://github.com/xguse/table_enforcer)
- [dataenforce](https://github.com/CedricFR/dataenforce)
- [strictly typed pandas](https://github.com/nanne-aben/strictly_typed_pandas)
- [marshmallow-dataframe](https://github.com/facultyai/marshmallow-dataframe)

There are a bunch of these. Pandera seems to be the most popular (as ascertained by the amount of Github stars). However, they all take basically the same approach. They just differ in their APIs (and even then, not by very much).

You define a schema that specifies a "base-type" and a predicate that data must satisfy for each column. You can then validate the data at run-time. Some libraries play pretty nicely with typed Python syntax. You can define a type for each schema, and then the type of a particular DataFrame has the type of that Schema. This allows python static checkers to verify basic type properties such as not passing in a dataframe of the wrong type (wrong/unvalidated schema) to a function that asks for a dataframe of a particular schema.

### Pandera

Pandera supports some fancier things too, like being useful for synthesizing data that passes a particular predicate. This can be used for hypothesis based testing.

### Table-enforcer

Supports "recoders" which are basically coercing functions that convert arbitrary data into a form that passes the validators. This is basically a nice API convenience.

### Dataenforce

Has some nice python type syntax. You can write `Dataset["id", "name", "location"]` to represent a table with those columns. You can write `Dataset["id": int, "name", "location"]` to indicate that the `id` column should have type `int`.

Also comes with a `@validator` annotation.

## Examples

### Pandera

Simple example from the pandera docs:

```python
from pandera.typing import Series

class Schema(pa.DataFrameModel):

    column1: Series[int] = pa.Field(le=10)
    column2: Series[float] = pa.Field(lt=-1.2)
    column3: Series[str] = pa.Field(str_startswith="value_")

    @pa.check("column3")
    def column_3_check(cls, series: Series[str]) -> Series[bool]:
        """Check that column3 values have two elements after being split with '_'"""
        return series.str.split("_", expand=True).shape[1] == 2

Schema.validate(df)
```

## Signatures of Pandas functions

### `max`
`Series[{t | R}] -> Series[{t | R}]`

This is what I want for this input.

`Series[{int | 0 <= V <= 100}] -> Series[{t | V <= 100}]`

This blog post is relevant.
https://ucsd-progsys.github.io/liquidhaskell/blogposts/2013-06-03-abstracting-over-refinements.lhs/#

## Open Questions

### How should we handle missing values?

If a dataframe has type `DataFrame[.., A: {int | 0 <= V}]`, what values are allowed in column A? Should it just be non-negative values? Are NaNs allowed? Allowing NaNs are slightly more aligned with the semantics of Pandas dataframes, however it also makes the types less useful.

Do we want predicates across the values in a column?

```python
df["mean"] = df["A"].mean()

# DataFrame[.., mean: {float | V == self["A"].mean()}]
```
