# Solvent

An experiment in mapping [liquid types][pldi08] with [type annotation][pep3107]
syntax, in order to elucidate the technique.  Implemented in service of the
final presentation for [C S 395T: The Model Checking Paradigm][mcmilcourse] at
UT Austin.

## Authors:

```
Nathan Taylor <ntaylor@cs.utexas.edu>
Sam Thomas <sgt@cs.utexas.edu>
```

## Setup

```
$ poetry install
$ poetry run pytest
```

## Development

Solvent uses `pre-commit` to ensure that committed code is formatted
and type-checked. Install the pre-commit hook with:

```
$ poetry run pre-commit install
```

If you want to manually run the pre-commit, use the following command.
Note that this only runs on committed files.

```
$ poetry run pre-commit run
```

## Presentation

To edit the presentation: `poetry run jupyter notebook paper/Presentation.ipynb`

## Overview

A liquid type is a type system that refines a conventional base type with
logical predicates over program terms.  Solvent is an experment to both
understand the technique but also to see how far we can push conventional
Python annotation syntax to accommodate a rich dependent type system like
this.

Explicit goals include:

* Backwards execution compatibility with the stock Python interpreter - we explicitly
  do not want a preprocessing step that modifies input source before CPython
  is able to start reading it in.
* Whenever possible, leveraging pythonic idioms and builtins - Solvent should appear
  to be a natural extension of the language unless absolutely necessary.
* Implementing enough of a subset of the core liquid types paper in order to 
  walk through at least some of the paper's examples end-to-end.  In particular,
  this covers H-M type inference, refinement inference, VC generation, and discharging
  to an SMT solver.

## Limitations

* Valid pytypes are whitelisted and minimal
* No mutation in function bodies (TODO: check subsequent literature on this)

[mcmilcourse]: https://mcmil.net/wordpress/2021/01/22/cs-395t-the-model-checking-paradigm/
[pep3107]: https://peps.python.org/pep-3107/
[pldi08]: https://ranjitjhala.github.io/static/liquid_types.pdf
