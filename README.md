# Solvent

An experiment in mapping [liquid types][pldi08] to PEP-484 syntax, in order to
eludicate the technique.  Implemented as part of the final presentation for [C
S 395T: The Model Checking Paradigm][mcmilcourse] at UT Austin.

## Setup

```
$ poetry install
$ poetry run pytest
```

## Limitations

* Valid pytypes are whitelisted and minimal
* No mutation in function bodies (TODO: check subsequent literature on this)

[mcmilcourse]: https://mcmil.net/wordpress/2021/01/22/cs-395t-the-model-checking-paradigm/
[pldi08]: https://ranjitjhala.github.io/static/liquid_types.pdf
