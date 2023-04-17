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

In so doing, Milner's old canard that _"well-typed programs don't go
wrong"_[@milner-type-poly] has entered the programmer's popular lexicon.

However, as a form of abstract interpretation[@CousotCousot], this statement is
in reality circumscribed by how much information is lost by the abstract
transformation: in particular, the program in Figure 2 can, indeed, go wrong -
the type system proves the _shape_ of the input datatype (morally, an iterable,
indexable structure) but lost facts about _particular_ well-typed terms.
Concretely: Since at the type level an empty list is indistinguishable from a
non-empty one, it's impossible to reject a program that requires a _non-empty_
list as input.

```{.python .numberLines}
def avg(xs):
    return sum(xs) / len(xs)
avg(42) # Runtime error: int is not iterable

def avg(xs: list[int]) -> int
    return sum(xs) // len(xs)
avg([]) # Runtime error: ZeroDivisionError
```
_Figure 1: an ill-typed program that goes wrong, and a well-typed one that also
goes wrong._

### Towards a type-theoretic approach

This particular soundness hole can be tackled by making the typelevel
definition of a list more precise. Be it via refactoring the subtyping
hierarchy for `List`, [@ScalaCatsNonEmptyList], indexed
types[@ZengerIndexedTypes], or generalized algebraic
datatypes[@InductiveFamilies], we need to place constraints on terms of type
`List[T]` by a statement in some particular _constraint domain_. In our case,
our domain would need to be rich enough to encode and solve for an nonemptiness
constraint.  In general, the richer the constraint domain, the richer and more
general qualifications we can place on a type, but the higher the proof burden
on the humans and proof systems in the loop.

A constraint domain may simply be the existing type system.  For instance, the
typelevel definition of the Peano naturals as a type `Nat` with type
constructors `Z` and `S[N <: Nat]` would allow a new encoding of natural
numbers _within the type system_.  In contrast to the _term_ `3` (of type
`int`), `S[S[S[Z]]]` is itself a _type_ (namely, a subtype of `Nat`) with no
inherent runtime semantics[@Shapeless].  

```{.python .numberLines}
from typing import Any, Generic, TypeVar

class Nat: pass
M,N = TypeVar("M", bound=Nat), TypeVar("N", bound=Nat)

class Z(Nat): pass
class S(Nat, Generic[N]): pass

Two: type = S[S[Z]]
Four: type = S[S[Two]]
```
_Figure 2: A typelevel encoding of the natural numbers._

Representing numbers this way would let us embed a second type parameter `L <:
Nat` to a collection type `Vec[L, T]`, the vector of `L` elements of type `T`.
As a concrete example, `[1,2]` might be typed as `List[S[S[Z], Int]`, and
`cons` as `𝛼 → List[l, 𝛼] → List[S[l], 𝛼]`.  In so doing, we say that `Vec` is
_indexed_ by the type `Nat`, and a fuller implementation of `Vec` (see Figure 3).  

Notice that this is not the same as being indexed by _values_ of type `Nat`; we
cannot write `List[2, Int]` as the term 2 and type `S[S[Z]]` occupy different
syntactic domains.

```{.python .numberLines startFrom="12"}
T = TypeVar("T")
@dataclass
class Vec(Generic[N,T]): # A Vector of N elements of type T
    l: list[T]

    @staticmethod
    def nil() -> "Vec[Z, T]": return Vec([])
    @staticmethod
    def cons(t: T, l: "Vec[N, T]") -> "Vec[S[N], T]": return Vec([t] + l.l)

empty: Vec[Z, int] = Vec.nil()
one_two:  Vec[Two, int]  = Vec.cons(1, Vec.cons(2, Vec.nil()))
one_four: Vec[Four, int] = Vec.cons(1, Vec.cons(4, Vec.nil())) # error: Expression of type "Vec[S[S[S[S[Z]] | Z]], int]" cannot be assigned to declared type "Vec[S[S[S[S[Z]]]], int]"; TypeVar "N@Vec" is covariant; TypeVar "N@S" is covariant; TypeVar "N@S" is covariant; Type "S[S[Z]] | Z" cannot be assigned to type "S[S[Z]]"; "Z" is incompatible with "S[S[Z]]"

def avg(l: Vec[S[N], int]) -> int:
    return sum(l.l) // len(l.l)

avg(one_two)
avg(empty) # error: Argument of type "Vec[Z, int]" cannot be assigned to parameter "l" of type "Vec[S[N@avg], int]" in function "avg"; TypeVar "N@Vec" is covariant; "Z" is incompatible with "S[N@avg]"
```
_Figure 3: A vector of elements whose length is indexed by the type system, and
an implementation of `avg` that rejects an empty `Vec` with a difficult to
understand error._

While some may consider contorting an existing type system in this way to be a
hack, the benefits are clear: as we have not introduced any new mechanism into
an ordinary type system, we know that our existing type-metatheoretic
properties of soundness, inference, and termination remain.  Also, most
typechecking algorithms run in polynomial -- if not linear -- time.  In this
way, once written, we get our proofs from our type system for free, and the
procedure in which they are generated is decidedly non-magical.

Just as clear, however, are the downsides: that typecheckers operate on program
fragments definitionally restrict us to shallow propositions: it's not
difficult to imagine needing constraints over the naturals that are wildly
impractical, if not impossible, to state entirely in the metalanguage of
parametrically-polymorphic types.  For instance, while we can prove the length
of a Vec is nonzero, we cannot state that elements _contained within the Vec_
are themselves nonzero, nor could we specify a constraint over the index type
itself (such as enforcing a list of even length), so we have to adjust
expectations accordingly.

Further, ergonomic issues abound: a type error should be treated as a form 
of counterproof, but often reported errors are at the wrong level of abstraction;
for instance, decoding the two error-producing expressions in Figure 3 requires
exposes implementation details of `Nat` and `Vec` while obscuring relevent
ones, making applying the "counterproof" a frictive experience.

_TODO: Alternative: higher-order theorem proving lets us express all sorts of
nice properties (even with, under curry-howard, quantifiers!) but now humans
have to step in and help with the proof discharge, and program execution is
sometimes constrained to e.g. provably terminate, fit into Calculus of
Constructions-compliant datatypes, or whatever.  Definition of a dependent
type should go here too.  Sammy: since you're the real Type Enjoyer maybe can
you flesh this bit out?_

### Towards a model-theoretic approach

Certainly, the logical statement `at no point will len(xs) be zero` feels very
much a safety property, suggesting a straightforward "throw a tool for model
checking like Slam[@SlamProject] or Saturn[@Saturn] at it" solution. Much like
our non-higher order type systems, model checking techniques are sound,
push-button in their human-in-the-loop requirements, and can scale up to tackle
the practicalities of exploring the execution space in real-world software.

Indeed, enumerating paths through a program is a property of model-checking
that is not well-covered in the type theory space.  Type systems are typically
_path-insensitive_ as most typechecking algorithms act upon program
fragments, and then compose to operate over the program as a whole.  This
"context-free" nature means the typechecker knows where it's going, but it
doesn't know where it's been[@RoadtoNowhere], limiting the richness of the
space of counterproofs that it can generate.

The model checking approach is not strictly optimal, however.  Hidden within
our straightforward type `List[T]` is in fact something problematic for model
checkers: under Curry-Howard, a type variable corresponds to universal
quantification in constructive logic.  In that way, a natural reading of the
polymorphic list type is: _for all elements in the list, that element types to
`T`_ Meanwhile, the encoding schemes for symbolically abstracting states into
statesets such as BDDs and subsets of first-order logic, typically eschew
quantifiers altogether.  

Generally, therefore, reasoning about inductive data structures, something
trivial for a type-checker, can cause a model checker to wander into the realm
of undecidability.  Either users are therefore forced to either give up full
automation in their models[@Dafny], or model checker implementers are required
to add new axioms on a per-data structure basis[@LinkedListVerification] or
hope that their system's heuristics[@TriggerSelection] will not cause verification
to spiral out of control.

## Unifying the two approaches with logically-qualified types

Ideally, we would be able to pick and choose parts from both the model- and
type-theoretic approaches to get the benefits of each.

A _refinement type_[@RefinementTypesForML] is the a pairing of an ordinary,
potentially polymorphic type (called the _base type_) and some logical
predicate that _refines_ it.  For example, `{v: int | 0 <= v ∧ v < n}` refines
the base type of the integers to be bound between 0 and some other program
value `n`.  Since `n` is a program-level term, a refinement type is also a
dependent type (in particular, the finite dependent sum type `Fin n`).  As
before, the expressiveness of a refinement type depends on the expressiveness
of the refining predicate's constraint domain.

```python
def avg(xs: List(Int) | len(xs) > 0) -> int
    return sum(xs) // len(xs)
avg(42) # Type-checking error
avg([]) # Type-checking error
```
_Figure 4: a logically qualified program that does not go wrong._

By contrast, liquid types[@LiquidTypesPLDI08] owns, dude.


## Historical overview and context

## The technique

### From program expressions to base types

### Lifting base types into refined types

### Subtyping through implications

### Predicate abstraction and the journey home

## Limitations and Subsequent Work

[^1]: In particular, those derived from the Hindley-Milner subset of System F,
  which we can intuit as being more or less equivalent in expressiveness to
  Java's Generics[@JavaGenerics].
