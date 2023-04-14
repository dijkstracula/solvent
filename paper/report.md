## Overview

Type systems are arguably the branch of formal methods that software developers
are most likely to exploit in order to reason about the behaviour of their
programs.  Even the "simple" type systems enjoyed by conventional imperative
languages like Java or C# provide a powerful mechanism to soundly reason about
programs operating on arbitrary-sized data structures like linked lists,
statically rejecting invalid programs such as the one in Figure 1.  In so
doing, the old canard that _"well-typed programs don't go
wrong"_[@milner-type-poly] has entered the popular lexicon.

```python
def avg(xs):
    return sum(xs) / len(xs)
avg(42) # Runtime error: 42
```
_Figure 1: an ill-typed program that goes wrong._

However, as a form of abstract interpretation[@CousotCousot], this statement is
really circumscribed by how much information is lost in the abstract transformer:
in particular, we have retained the _shape_ of the datatype (morally, an iterable,
indexable structure) but abstracted away facts about _particular_ `list[int]`s:
Since at the type level we can't encode the requirement that the list is nonempty.

```python
def avg(xs: list[int]) -> int
    return sum(xs) / len(xs)
avg(42) # Type-checking error
avg([]) # Runtime error
```
_Figure 2: a well-typed program that nevertheless goes wrong._

### Towards types that depend on terms

By contrast, liquid types[@LiquidTypesPLDI08] owns, dude.

```python
def avg(xs: List(Int) | len(xs) > 0) -> int
    return sum(xs) / len(xs)
avg(42) # Type-checking error
avg([]) # Type-checking error
```
_Figure 3: a dependently-typed program that does not go wrong._


## Historical overview and context

## 
