## Overview and Motivation

Type theory is inarguably the branch of formal methods that software developers
most commonly exploit to reason about the behaviour of their programs.  While
inexpressive relative to their counterparts in research languages, even
"simple" type systems[^1] enjoyed by conventional industrial languages like Java or
C# provide a powerful mechanism to statically reject invalid programs, such as
the one in Figure 1.  Such type systems also enjoy strong metatheoretic
properties.  Soundness (that is, invalid programs will always be rejected),
reconstruction (that is, types can be inferred via terms' usage without human
annotation), and termination are guaranteed, even when type-checking programs
whose behaviour depends on runtime user input or data structures of unknown or
unbounded size.  

In so doing, Milner's old canard
that _"well-typed programs don't go wrong"_[@milner-type-poly] has entered the
programmer's popular lexicon.

```python
def avg(xs):
    return sum(xs) / len(xs)
avg(42) # Runtime error: int is not iterable
```
_Figure 1: an ill-typed program that goes wrong._

However, as a form of abstract interpretation[@CousotCousot], this statement is
in reality circumscribed by how much information is lost in the abstract
transformer: in particular, the program in Figure 2 can, indeed, go wrong - the
type system proves the _shape_ of the input datatype (morally, an iterable,
indexable structure) but lost facts about _particular_ well-typed terms.
Concretely: Since at the type level an empty list is indistinguishable from a
non-empty one, it's impossible  to reject a program that requires a _non-empty_
list as input.

```python
def avg(xs: list[int]) -> int
    return sum(xs) / len(xs)
avg([]) # Runtime error: ZeroDivisionError
```
_Figure 2: a well-typed program that nevertheless goes wrong._

### Towards a type-theoretic approach

This particular soundness hole can be approached from the world of types, too.
Be it via refactoring the subtyping hierarchy for `List`,
[@ScalaCatsNonEmptyList], indexed types[@ZengerIndexedTypes], or generalized
algebraic datatypes[@InductiveFamilies], we need to place constraints on terms
of type `List[T]` by a statement in some particular _constraint domain_. In our
case, our domain would need to be rich enough to encode and solve for the
nonemptiness constraint on the input list `xs`.

A constraint domain may simply be the existing type system.  For instance, the
typelevel definition of the Peano naturals as a type `Nat` with type
constructors `Z` and `S[N <: Nat]` would allow encoding natural numbers _within
the type system_.  In contrast to the _term_ `3` (of type `int` and kind `★`),
`S[S[S[Z]]]` is itself a _type_ (of kind `★`) with no inherent runtime
semantics[@Shapeless].  This encoding would let us embed a second type parameter
`L <: Nat` to `List[T]`, tracking the length of the list .  Under this scheme,
`[1,2]` might be typed as `List[S[S[Z], Int]`, and `cons` as `𝛼 → List[l, 𝛼] →
List[S[l], 𝛼]`.  While some may consider contorting an existing type system in
this way to be a hack, the benefits are clear: as we have not introduced any
new mechanism into an ordinary parametrically-polymorphic type system, we know
that our type-metatheoretic properties of soundness, inference, and termination
remain - after all, we are only reusing existing mechanism.  Just as clear,
however, are the downsides: it's not difficult to imagine needing constraints
over the naturals that are wildly impractical to state in such a restricted
"type language".

TODO: Alternative: higher-order theorem proving lets us express all sorts of
nice properties (even with, under curry-howard, quantifiers!) but now humans
have to step in and help with the proof discharge, and program execution is
sometimes constrained to e.g. provably terminate, fit into Calculus of
Constructions-compliant datatypes, or whatever.  Sammy: since you're the real
Type Enjoyer maybe can you flesh this bit out?

### Towards a model-theoretic approach

Certainly, the logical statement `at no point will len(xs) be zero` feels very
much a temporal safety property, suggesting a straightforward "throw a tool for
temporal model checking like Slam[@SlamProject] or Saturn[@Saturn] at it"
solution.  Much like our non-higher order type systems, model checking
techniques are sound, push-button in their human-in-the-loop requirements, and
can scale up to tackle the practicalities of exploring the execution space in
real-world software.

Indeed, enumerating paths through a program is a property of model-checking
that is not well-covered in the type theory space.  Type systems are typically
_path-insensitive_ as most typechecking algorithms act on a bottom-up traversal
of the syntax tree.  TODO: yes, this might be true, but what does this buy us?
Presuambly a more interesting counterexample can follow from following a full
execution path?

TODO: but reasoning about inductive data structures is tricky.  You have to
either invent custom logics for a particular data
structure[@LinkedListVerification] or give up automation[@Dafny]. OR
SOMETHING MAN IDK

### Unifying the two approaches with logically-qualified types

A _refinement type_[@RefinementTypesForML] is the a pairing of a type (called
the _base type_) and some predicate 

```python
def avg(xs: List(Int) | len(xs) > 0) -> int
    return sum(xs) / len(xs)
avg(42) # Type-checking error
avg([]) # Type-checking error
```
_Figure 3: a dependently-typed program that does not go wrong._


By contrast, liquid types[@LiquidTypesPLDI08] owns, dude.

<---


## Historical overview and context

## 

[^1]: In particular, those derived from the Hindley-Milner subset of System F.
