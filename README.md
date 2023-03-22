# Solvent

An experiment in mapping [liquid types][pldi08] with [type annotation][pep3107]
syntax, in order to elucidate the technique.  Implemented in service of the
final presentation for [C S 395T: The Model Checking Paradigm][mcmilcourse] at
UT Austin.

## Authors:

```
Nathan Taylor <ntaylor@cs.utexas.edu>
```

## Setup

```
$ poetry install
$ poetry run pytest
```

## Limitations

* Valid pytypes are whitelisted and minimal
* No mutation in function bodies (TODO: check subsequent literature on this)

[mcmilcourse]: https://mcmil.net/wordpress/2021/01/22/cs-395t-the-model-checking-paradigm/
[pep3107]: https://peps.python.org/pep-3107/
[pldi08]: https://ranjitjhala.github.io/static/liquid_types.pdf
