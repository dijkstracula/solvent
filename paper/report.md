## Overview and Motivation

Type systems are inarguably the branch of formal methods that software
developers exploit to reason about the behaviour of their programs.  Even the
"simple" type systems enjoyed by conventional imperative languages like Java or
C# provide a powerful mechanism to soundly reason about programs operating on
arbitrary-sized data structures like linked lists, statically rejecting invalid
programs such as the following:

```python
def avg(xs):
    return sum(xs) / len(xs)
avg(42) # Runtime error: int is not iterable
```
_Figure 1: an ill-typed program that goes wrong._


In so doing, the old canard that _"well-typed programs don't go
wrong"_[@milner-type-poly] has entered the popular lexicon.

However, as a form of abstract interpretation[@CousotCousot], this statement is
really circumscribed by how much information is lost in the abstract transformer:
in particular, we have retained the _shape_ of the datatype (morally, an
iterable, indexable structure) but lost facts about _particular_ `list[int]`s:
Since at the type level an empty list is indistinguishable from a non-empty
one, it's impossible to reject a program that requires a _non-empty_ list as
input:

```python
def avg(xs: list[int]) -> int
    return sum(xs) / len(xs)
avg([]) # Runtime error: ZeroDivisionError
```
_Figure 2: a well-typed program that nevertheless goes wrong._

### TODO: what's hard about doing this with model-checking

TODO: At first blush, model checking offers us a solution: logical statements
over program variables seem straightforward to state in first-order logic.
Something something model checking is great at exploring the state space of
program execution (btw, something that types at best only help indirectly with)
but reasoning about inductive data structures is tricky.  You have to either invent
custom logics for a particular data structure[@LinkedListVerification] or give up
automation.  OR SOMETHING MAN IDK


### Towards relating types and terms

While this particular soundness hole can be patched with traditional
subtyping[@ScalaCatsNonEmptyList], indexed types[@ZengerIndexedTypes], or
generalized algebraic datatypes[@InductiveFamilies], it illustrates the need to
_refine_ types via some particular _constraint domain_.  In our case, our
domain would need to be rich enough to encode and solve for the nonemptiness
constraint on the input list `xs`.

A constraint domain may simply be the existing type system.  For instance, a
typelevel definition of the Peano naturals as a sum type `Nat` with data
constructors `Z` and `S[N <: Nat]` would permit adding a type parameter `L <:
Nat` to encode a list's length.  Under this scheme, `[1,2]` might be typed as
`List[S[S[Z], Int]`, and `cons(x, xs)` might be typed as `𝛼 → List[l, 𝛼] →
List[S[l], 𝛼]`.  While some may consider contorting an existing type system in
this way to be a hack, the benefits are clear: as we have not introduced any
new mechanism into an ordinary parametrically-polymorphic type system, we know
that constraints of this form are sound and "constraint solving" (that is,
ordinary typechecking!) will terminate.  Just as clear, however, are the
downsides: it's not difficult to imagine needing constraints over the naturals
that are wildly impractical to state with simply the Peanos.

More expressive constraints may be encoded by enriching the constraint domain
beyond what may be expressed directly in the type system.  At the far end of
the spectrum are the full dependent type systems of 

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
