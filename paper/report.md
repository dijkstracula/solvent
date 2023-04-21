## Overview and Motivation

Enterprising formal methods researchers could do worse than position their
work in the type-theoretic space.  While inexpressive relative to their
counterparts in research languages, even "simple" type systems[^1] enjoyed by
conventional industrial languages like Java or C# provide a powerful mechanism
to statically reject invalid programs. Type systems also enjoy strong
metatheoretic properties.  Soundness (that is, invalid programs will always be
rejected), reconstruction (that is, types can be inferred via terms' usage
without human annotation), and termination are guaranteed, even when
typechecking programs whose behaviour depends on runtime user input or data
structures of unknown or unbounded size.  In so doing, Milner's old canard that
_"well-typed programs don't go wrong"_[@milner-type-poly] has entered the
programmer's popular lexicon [@LiquidHaskellTutorial]; after all, type theory
is inarguably the branch of formal methods that software developers most
commonly exploit to reason about the behaviour of their programs.  

However, as a form of abstract interpretation[@CousotCousot], Milner's _bon
mot_ is in reality circumscribed by how much information is lost by the
abstract transformation: in particular, the program in Figure 1 can, indeed, go
wrong - the type system proves the _shape_ of the input datatype (morally, an
iterable, indexable structure) but lost facts about _particular_ well-typed
terms. Concretely: Since at the type level an empty list is indistinguishable
from a non-empty one, it's impossible to reject a program that requires a
_non-empty_ list as input.

```{.python .numberLines}
def avg(xs):
    return sum(xs) / len(xs)
avg(42) # Runtime error: int is not iterable

def avg(xs: list[int]) -> int
    return sum(xs) // len(xs)
avg([]) # Runtime error: ZeroDivisionError
```
_Figure 1: an ill-typed program that goes wrong, and a well-typed one that also
goes wrong.[@LiquidHaskellTutorial]._

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
on the humans and proof systems in the loop.  In the words of Rondon et al,
_type checking [over a constraint domain] is shown to be decidable modulo the
decidability of the domain_.

A constraint domain may simply be the existing type system.  For instance, the
typelevel definition of the Peano naturals as a type `Nat` with type
constructors `Z` and `S[N <: Nat]` would allow a new encoding of natural
numbers _within the type system_.  In contrast to the _term_ `3` (of type
`int`), `S[S[S[Z]]]` is itself a _type_ (namely, a subtype of `Nat`) with no
inherent runtime semantics (for a more complete example, see [@Shapeless]).  

```{.python .numberLines}
from typing import Any, Generic, TypeVar
N,T = TypeVar("N", bound="Nat"), TypeVar("T")

class Nat: pass
class Z(Nat): pass
class S(Nat, Generic[N]): pass

Two: type = S[S[Z]]
Four: type = S[S[Two]]
```
_Figure 2: A typelevel encoding of the natural numbers._

Representing numbers this way would let us embed a second type parameter `L <:
Nat` to a collection type `Vec[L, T]`, the vector of `L` elements of type `T` (see Figure 3).
As a concrete example, `[1,2]` might be typed as `List[S[S[Z], Int]`, and
`cons` as `𝛼 → List[l, 𝛼] → List[S[l], 𝛼]`.  The two constructors `nat` and
`cons` enforce the invariant that the typelevel value of `L` always conforms to
the length of the list.  In so doing, we say that `Vec` is _indexed_ by `Nat`.
Notice that this is not the same as being indexed by _values_ of type `Nat` or
`int`; terms and types in non-dependently typed programming languages occupy
different syntactic domains and are not interchangable in this way.

```{.python .numberLines startFrom="11"}
@dataclass
class Vec(Generic[N,T]): # A Vector of N elements of type T
    l: list[T]
def nil() -> Vec[Z, T]: return Vec([])
def cons(t: T, l: Vec[N, T]) -> Vec[S[N], T]: return Vec([t] + l.l)

empty: Vec[Z, int] = nil()
one_three:  Vec[Two, int] = cons(1, cons(3, nil()))
four_four: Vec[Four, int] = cons(4, cons(4, nil())) # error: Expression of type "Vec[S[S[S[S[Z]] | Z]], int]" cannot be assigned to declared type "Vec[S[S[S[S[Z]]]], int]"; TypeVar "N@Vec" is covariant; TypeVar "N@S" is covariant; TypeVar "N@S" is covariant; Type "S[S[Z]] | Z" cannot be assigned to type "S[S[Z]]"; "Z" is incompatible with "S[S[Z]]"

def avg(l: Vec[S[N], int]) -> int:
    return sum(l.l) // len(l.l)

avg(42) # error: # error: Argument of type "Literal[42]" cannot be assigned to parameter "l" of type "Vec[S[N@avg], int]" in function "avg"   "Literal[42]" is incompatible with "Vec[S[N@avg], int]"
avg(empty) # error: Argument of type "Vec[Z, int]" cannot be assigned to parameter "l" of type "Vec[S[N@avg], int]" in function "avg"; TypeVar "N@Vec" is covariant; "Z" is incompatible with "S[N@avg]"
assert(avg(one_three) == 2)
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
ones, making applying the "counterproof" a frictive experience.  The type error
on [line 7 of Figure 1](#cb1-7) is far shorter and more descriptive than its
equivalent on [line 24 of Figure 3](#cb3-24).


type error on line 24 of Figure 3, where a non-list value is passed to `avg()`,
with its equivalent in Figure 1.

_TODO: Alternative: higher-order theorem proving lets us express all sorts of
nice properties (even with, under curry-howard, quantifiers!) but now humans
have to step in and help with the proof discharge, and program execution is
sometimes constrained to e.g. provably terminate, fit into Calculus of
Constructions-compliant datatypes, or whatever.  Definition of a dependent
type should go here too, and ideally an example that requires something more
expressive than liquid types.  Sammy: since you're the real Type Enjoyer maybe
can you flesh this bit out?_

### Towards a model-theoretic approach

Certainly, the logical statement `at no point will len(xs) be zero` feels very
much a safety property, suggesting a straightforward "throw a tool for model
checking like SLAM[@SlamProject], BLAST[@BLAST] or Houdini[@Houdini] at it"
solution.  As it happens, each of the above tools use _predicate
abstraction_[@PredicateAbstraction] as their computational workhorse; _TODO:
add text about what's interesting about predicate abstraction, with an eye
towards why it's useful for liquid type reconstruction_.  Much like our
non-higher order type systems, model checking techniques are sound, push-button
in their human-in-the-loop requirements, and can scale up to tackle the
practicalities of exploring the execution space in real-world software.  

Indeed, enumerating paths through a program is a property of model-checking
that is not well-covered in the type theory space.  Type systems are typically
_path-insensitive_ as most typechecking algorithms act upon program fragments,
and then compose to operate over the program as a whole.  This "context-free"
nature means the typechecker knows where it's going, but it doesn't know where
it's been[@RoadtoNowhere], limiting the richness of the space of counterproofs
that it can generate.

The model checking approach is not strictly optimal, however.  Hidden within
our straightforward type `List[T]` is in fact something problematic for model
checkers: under Curry-Howard, a type variable corresponds to quantifying over
propositions in constructive logic[@TaPL].  In that way, the reading of this
a polymorphic type is: `for all propositions T, the proposition List(T) holds`.
Meanwhile, the encoding schemes for symbolically abstracting states into
statesets such as BDDs and subsets of first-order logic, typically eschew
quantifiers altogether.  

Generally, therefore, reasoning about inductive data structures, something
trivial for a typechecker, can cause a model checker to wander into the realm
of undecidability.  Either users are therefore forced to either give up full
automation in their models[@Dafny], or model checker implementers are required
to add new axioms on a per-data structure basis[@LinkedListVerification] or
hope that their system's heuristics[@TriggerSelection] will not cause verification
to spiral out of control.

## Unifying the two approaches with logically-qualified types

A _refinement type_[@RefinementTypesForML] is the a pairing of an ordinary,
nominally-polymorphic type (called the _base type_) and some logical
predicate that _refines_ it.  For example, `{v: int | 0 <= v ∧ v < n}` refines
the base type of the integers to be bound between 0 and some other value `n`.
Since `n` is a program-level term, a refinement type is also a dependent type
(in particular, type zoologists will recognise a familiar sight: this is the
dependent type `Fin n`).  A type definition like this, for instance, could
allow the (partial) function `select: List[𝛼] -> int -> 𝛼` to become the
dependent total function `select: Vec[n, 𝛼] -> Fin n -> 𝛼`,
statically-rejecting out-of-bounds indices. In addition to safety improvements,
prior work[@DependentML] showed the clear performance benefits of being able to
elide runtime bounds checks.

As before, the expressiveness of a refinement type depends on the
expressiveness of the refining predicate's constraint domain.  Critically: If
the constraint domain is made up of _conjunctions of boolean predicates_ over
program terms, we can call such a refinement type a _logically-qualified
(LiQuid) type_[@LiquidTypesPLDI08].  Ideally, we would be able to pick and
choose parts from both the model- and type-theoretic approaches to get the
benefits of each. In particular, we'd like to exploit the structure of a
refinement type: given the base type and refinement predicate are expressed in
different constraint domains, the hope is that we can apply pure type-theoretic
mechanisms to the former and model-checking mechanisms to the latter, gain the
advantages of both, and avoid destructive interference between them.

```python
@solvent.check
def avg(xs: List(Int) | len(xs) > 0) -> int
    return sum(xs) // len(xs)
avg(42) # Type-checking error
avg([]) # Type-checking error
```
_Figure 4: a logically-qualified program, checked with the
[Solvent](https://github.com/dijkstracula/solvent) liquid typechecker for
Python, that does not go wrong._

The procedure described in the authors' initial work[@LiquidTypesPLDI08] is
primarily motivated by the type _reconstruction_ problem: given a program
absent type annotations, infer "the best" annotation for program
expressions[^2].  For instance, we'd like to say more about an unannotated
function `max x y = if x > y then x else y` than what we can infer from the
base types, which is that `x:int → y:int → int`.  

One could imagine a few reasonable choices for an inferred refinement of the
return type: perhaps `max` could be typed as `x:int → y:int → { i: int | i == x
∨ i == y }`?  Is the return type's refinement more or less difficult to infer,
or more or less _useful for the programmer_, than, say, `{ i: int | i >= x ∧ i >= y }`, 
or, if we had an oracle that told us that `max` can only be called with
arguments 31 and 99, the singleton type `{i : int | i == 99}`? The authors must
aim for the best of both worlds: a dependent type system rich enough to prove
useful safety properties, while _not_ being so expressive that reconstruction
becomes impossible.

### From program expressions to base types

In the paper, the only valid base types are `int`, `bool`, and `list[int]`.
This doesn't mean that these are the only types that program terms can type to,
only that the terms _that appear within a refinement type_ must be drawn from a
small fixed number of built-in types.  Contiguous arrays of bytes would appear
later in their refinement work for C[@LowLevelLiquidTypesPOPL10], and liquid
records and algebraic datatypes would appear later
still[@RefinementTypesForHaskell].

Base types are inferred via the Hindley-Milner (H-M) type inference
algorithm[@TaPL], an absolute bog-standard procedure that we describe here only
so that it can be compared to the refinement predicate inference procedure that
follows.  

H-M begins from an unannotated syntax tree and, as it walks the tree, generates
a collection of type constraints which relate program types or type variables
standing in for unknown types to each other.  A _unifier_ comprising a final
mapping from program terms to types then computed from these constraints.  If
the constraint set is not satisfiable, then one or more constraints clash (e.g.
two disperate types are constrained as equal) and the origin of that
contradicting constraint is the location of the type error.  

If the constraint set is underspecified, some term will map only to a type
variable and not a concrete type, so as to say "any type will do here".  This
generality is critical: unification is guaranteed to provide the _most general_
(or minimal)_ sequence of substitutions in its mapping; in this way, we say the
_principal type_ for each term is reconstructed.  While this ensures that we do
not unnecessarily constrain a term's type, there are also operational
implications: because a term's principal type will always be generated, there's
no value in recomputing it once additional constraints have been computed.  As
a result, there's no need to eagerly unify the full constraint set at once:
_lazy_ unification means inference and typechecking can be done
incrementally[@TaPL] or interleaved with each other, which is important for
more sophisticated _bidirectional_ typing algorithms.

### Lifting base types into refined types

Refinement predicates are drawn from arithmetic and relational expressions over
integer, boolean, and array sorts, and conjunctions thereof.   Their terminals
are either (well-typed) constants, program variables, or the special value
variable bound within the type itself.  (While not exhaustively enumerated in
the paper, the precise possible predicate types are documented [in the authors'
implementation of liquid types for
OCaml](https://github.com/ucsd-progsys/dsolve/blame/master/README#L97-L154).)
In other words, the quantifier-free theory of linear arithmetic and
uninterpreted functions (QF-UFLIA)!  

It's clear that liquid types are more restrained in their expressivity than
full dependent types, for which type checking and reconstruction quickly wander
into the realm of undecidability[@SystemFUndecidable].  But, the tradeoff
pays dividends:  Since QF-UFLIA is decidable, so too is the _typechecking_ of a
liquid type, since off-the-shelf SMT solvers like
[Yices](https://yices.csl.sri.com/) or Z3 can be used to check whether a
refinement predicate in this logic is valid.  It's interesting that the initial
paper[@LiquidTypesPLDI08] mentions using an SMT solver almost as an
afterthought, whereas the subsequent work([@LiquidTypesDSVerificationPLDI09],
[@RefinementTypesForHaskell], [@LowLevelLiquidTypesPOPL10],
[@GradualLiquidTypeInference]) makes sure to mention it explicitly and right in
the abstract.

If programmers were manually annotating all their program terms with refinement
types, we could treat the internals of the SMT solver as magic, rub it on our
problem, and go home early.  However, recall that our goal is type
_reconstruction_, not just _typechecking_; we need to divine a predicate
appropriate for the refinement type that is neither too weak (i.e. too abstract
to say anything meaningful) nor too strong (i.e. doesn't overfit to precisely
the concrete values inhabited by the type).  We saw before that the principal
type property of H-M type inference made "a good base typing" simply fall out
through unification; by contrast, conceivably, any number of "good refinement
typings" could be synthesized.

### Refinement type constraint generation

TODO: Lift base types that we've inferred into refinement types with constraint
variables that we'll solve for.  

TODO: Two ways to constrain our unknown predicates: if we want to synthesize a
qualifier that uses some program term (for instance, the predicate `x > y` for
the `max()` function example), that term of course needs to be in scope, and be
of the appropriate base type. This is a _scope_ constraint and helps us ensure
that our types only depend on values that make sense.

TODO: We can also constrain them by facts that follow from the control flow of
the program: for instance, in all terms getting typechecked within the `else`
branch of an `if x > 0 then {...} else {...}` statement, we know that `x <= 0`
is true.  This is a _flow constraint_ and gives us path sensitivity.

TODO: Once we've built up these constraints, we need to turn them into
a qualifier for our type.  That's where predicate abstraction comes in babeyyy
(should say something about how neither refutation/unification/etc is appropriate
here - something about an infinite space of possible substitutions or something)

### Predicate abstraction and subtyping through implications

Recalling how the technique was applied to great effect whilst contemplating
model-checking solutions([@SlamProject], [@BLAST], [@Houdini]), Rondon et al.,
a liquid type reconstruction algorithm consumes a set of predefined qualifiers
with type holes indicating points that well-typed terms can be inserted, and
produces a conjunction of those qualifiers.  Naturally, this induces a bias
into the reconstruction output: whoever wrote down the set of qualifiers for
predicate abstraction to choose from is in some sense determining the "basis
set" that will comprise a reconstructed liquid type.

```ocaml
(* ./default_patterns *)
qualif BOOL(v): ? v
qualif BOOL(v): not (? v)
qualif FALSE(_V): 1 = 0
qualif I(_V) : _V { * * } ^
qualif Id_rel_id_int(_V)(A:int) : _V { * * } ~A
qualif Int_rel_array_id(_V) : Array.length _V { * * } ^
qualif Id_eq_id(_V) : _V = ~A

(* ./postests/vec/len.hquals *)
qualif LVAR(_v)(A: int) : length _v { * * } ~A
qualif LCONST(v) : length v { * * } [0, 1]
qualif LVARV(v) : v { * * } length ~A
qualif SETAPPEND(_v) : length _v = (length v > i ? length v : i + 1)
qualif TOARR(v) : length t = Array.length v
```
_Figure 5: A selection of built-in qualifiers, and user-supplied ones used in
verifying a Rope[@RopeDS]-like `Vec` datatype, written in an internal pattern
DSL. `**` and `^` are the operator and integer literal wildcards, respectively.
Note the use of the recursively-defined function `length` in certain
qualifiers._

TODO: once we have qualifiers in Solvent, should we show those instead?

### Historical overview and context

TODO: both type inference and model checking had been around for decades before
this got published in 2008.  Why did this only appear then?  It's around the
era that SMT solvers became practical enough to use as a component in a larger
technique (TODO: look at the Decision Procedures book and see if there's a graph
showing an elbow curve up and to the right around that time?)  What else?

## Limitations and Subsequent Work

TODO: Low-level liquid types; and, don't forget about the gradual liquid types
followup paper[@GradualLiquidTypeInference].  Maybe also F*[@FStar]?

[^1]: In particular, those derived from the Hindley-Milner subset of System F,
  which we can intuit as being more or less equivalent in expressiveness to
  Scala, Haskell, or polymorphic Java[@JavaGenerics].  A critical feature of
  H-M type systems is that both typechecking and reconstruction (inference) is
  decidable and efficient.
[^2]: That is to say: trivally typing everybody to `⊤` won't do!
