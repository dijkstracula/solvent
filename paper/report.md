## Overview and Motivation

Enterprising formal methods researchers could do worse than position their
work in the type-theoretic space.  While inexpressive relative to their
counterparts in research languages, even "simple" type systems[^1] enjoyed by
conventional industrial languages like Java or C# provide a powerful mechanism
to statically reject invalid programs.  Under the Curry-Howard correspondence[@TaPL]
we can consider, at least to a first approximation, that a program passing the
typechecker corresponds to a proof in a constructive
logic[@ProgramEqualsProof].  Also, as a logical system, type systems enjoy
strong metatheoretic properties.  Soundness (that is, invalid programs will
always be rejected), reconstruction (that is, types can be inferred via terms'
usage without human annotation), and termination are guaranteed, even when
typechecking programs whose behaviour depends on runtime user input or data
structures of unknown or unbounded size.  In so doing, Milner's old canard that
_"well-typed programs don't go wrong"_[@milner-type-poly] has entered the
programmer's popular lexicon [@LiquidHaskellTutorial]; after all, type theory
is inarguably the branch of formal methods that software developers most
commonly exploit to reason about the behaviour of their programs.  

By "not going wrong", informally, we mean that there is always a way to
evaluate a program or program expression down to its final value.  A program
that can go wrong -- for instance, attempting division by zero, calling the
wrong method on an object, or iterating off the end of an array -- will have to
fail at runtime by throwing an exception or perhaps being killed by the
operating system.  If a well-typed program truly can't go wrong, then the
absence of such failure modes ought to have been proven by the type system.

However, as a form of abstract interpretation[@CousotCousot], Milner's _bon
mot_ is in reality circumscribed by how much information is lost by the
abstract transformation: in particular, both the typed and untyped program in
Figure 1 can, indeed, go wrong - the type system proves the _shape_ of the
input datatype (morally, an iterable, indexable collection of `int`s) but lost
facts about _particular_ well-typed terms. Concretely: Since at the type level
an empty list is indistinguishable from a non-empty one, it's impossible to
reject a program that requires a _non-empty_ list as input.

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
from __future__ import annotations
from typing import Any, Generic, TypeVar
N,T = TypeVar("N", bound=Nat), TypeVar("T")

class Nat: pass
class Z(Nat): pass
class S(Nat, Generic[N]): pass

# Note: `Two` and `Four` are typedefs for subtypes of Nat, not terms with a concrete value!
Two = S[S[Z]]
Four = S[S[Two]]
```
_Figure 2: A typelevel encoding of the natural numbers._

Representing numbers this way would let us embed a second type parameter `L <:
Nat` to a collection type `Vec[L, T]`, the vector of `L` elements of type `T` (see Figure 3).
As a concrete example, `[1,2]` might be typed as `List[S[S[Z], Int]`, and
`cons` as `𝛼 → List[l, 𝛼] → List[S[l], 𝛼]`.  The two constructors `nat` and
`cons` enforce the invariant that the typelevel value of `L` always conforms to
the length of the list.  In so doing, we say that `Vec` is _indexed_ by `Nat`.
Notice that this is not the same as being indexed by _values_ of type `Nat` or
`int`; terms and types in the Python type system occupy different syntactic
domains and are not interchangable in this way.

```{.python .numberLines startFrom="12"}
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
an implementation of `avg` that rejects ill-typed arguments, but with a
difficult to understand error._

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
impractical, if not impossible, to state entirely in the language of
parametrically-polymorphic types.  For instance, while we can prove the length
of a Vec is nonzero, we cannot state that elements _contained within the Vec_
are themselves nonzero, nor could we specify a constraint over the index type
itself (such as enforcing a list of even length), so we have to lower
expectations accordingly.

Further, ergonomic issues abound: a type error should be treated as a form 
of counterproof, but often reported errors are at the wrong level of abstraction;
for instance, decoding the two error-producing expressions in Figure 3 requires
exposes implementation details of `Nat` and `Vec` while obscuring relevent
ones, making applying the "counterproof" a frictive experience.  The type error
on [line 7 of Figure 1](#cb1-7) is far shorter and more descriptive than its
equivalent on [line 24 of Figure 3](#cb3-24).

### Towards types that depend on terms

A large burden has been placed on application developers to contort the type
system as we've just done.  Fundamentally, that terms and types occupy distinct
_syntactic domains_ makes a type annotation like `Vec[sum(range(10)), int]`
nonsensical: In Python's type system, `Vec`'s type arguments can only be other
types.

A _dependent_ type system[@DependentML], however, is one in which types and terms
_can_ intermingle.  This obviates the need for awkward typelevel programming with
the Peano naturals, but complexity is only pushed around, not eliminated.  In
its full bloom, we lose full automation of dependent type checking; anyone who
has needed to write a Coq proof longer than its associated program knows this
in their bones.  If we want to maintain full push-button automation for a
dependent type theory, we'll have to think about ways to give up on
completeness while still being useful.

### Towards a model-theoretic approach

Certainly, the logical statement `at no point will len(xs) be zero` feels very
much a safety property, suggesting a straightforward "throw a tool for model
checking like SLAM[@SlamProject], BLAST[@BLAST] or Houdini[@Houdini] at it"
solution.  Much like our non-higher order type systems, model checking
techniques are sound, push-button in their human-in-the-loop requirements, and
can scale up to tackle the practicalities of exploring the execution space in
real-world software.  

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

Generally, therefore, reasoning about inductive data structures, something
trivial for a typechecker, can cause a model checker to wander into the realm
of undecidability.  The encoding schemes for symbolically abstracting states into
statesets such as BDDs and subsets of first-order logic, typically eschew
quantifiers altogether.  Either users are therefore forced to either give up
full automation in their models[@Dafny], or model checker implementers are
required to add new axioms on a per-data structure
basis[@LinkedListVerification] or hope that their system's
heuristics[@TriggerSelection] will not cause verification to spiral out of
control.

## Unifying the two approaches with logically-qualified types

A _refinement type_[@RefinementTypesForML] is the a pairing of an ordinary,
polymorphic type (called the _base type_) and some logical predicate that
_refines_ it.  For example, `{v: int | 0 <= v ∧ v < n}` refines the base type
of the integers to be bound between 0 and some other value `n`. Since `n` is a
program-level term, a refinement type is also a dependent type (in particular,
type zoologists will recognise a familiar sight: this is the dependent type
`Fin n`).  A type definition like this, for instance, could allow the (partial)
function `select: List[𝛼] -> int -> 𝛼` to become the dependent total function
`select: Vec[n, 𝛼] -> Fin n -> 𝛼`, statically-rejecting out-of-bounds indices.
In addition to safety improvements, prior work[@DependentML] showed the clear
performance benefits of being able to elide runtime bounds checks.

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
def avg(xs: list[int] | len(xs) > 0) -> int
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
expressions[^2] as opposed to the type _checking_ problem, where a program
already annotated with types is verified to be consistent with the theory.  

Like all good inverse problems, type reconstruction is the meatier of the two
problems.  For some type theories, only typechecking is decidable, so it's
clearly in some sense the "harder" problem; and, being able to infer typelevel
correctness without human intervention gives us full push-button automation.

Also like all good inverse problems, type reconstruction has degrees of freedom
that checking does not - if several possible valid typings exist, which should
the algorithm deduce?  Nobody would claim that inferring `def double(x): return
2 * x` as `object -> object` would be terribly useful, correct though it might
be.  On the other side of the spectrum, if we had a full program analysis
oracle that told us that `double` is only ever called with argument 21, the
singleton refinement type ${v : int | v == 42}$ would similarly be correct, but
overfits to the input data in a way that doesn't provide a useful precondition
on the return value being used later in the program.  The authors must aim for
the best of both worlds: a dependent type system rich enough to prove useful
safety properties, while _not_ being so expressive that reconstruction becomes
impossible.

## From program expressions to base types

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

H-M is in essence, a lazy type-checker. Instead of checking the types of expressions,
as it comes upon them, it records typing constraints for later consideration; using 
type variables as placeholders as needed. A _unifier_ computes a solution from
these constraints, mapping type variables to types, so that type-checking succeeds.
If the constraint set is not satisfiable--one or more constraints clash--then we
can report a type error.

The constraint set may also be underspecified; some term will map only to a type
variable and not a concrete type, so as to say "any type will do here".  This
generality is critical: unification is guaranteed to provide the _most general_
(or minimal) sequence of substitutions in its mapping; in this way, we say the
_principal type_ for each term is reconstructed.  While this ensures that we do
not unnecessarily constrain a term's type, there are also operational
implications: because a term's principal type will always be generated, there's
no value in recomputing it once additional constraints have been computed.  As
a result, there's no need to eagerly unify the full constraint set at once:
_lazy_ unification means inference and typechecking can be done
incrementally[@TaPL] or interleaved with each other, which is important for
more sophisticated _bidirectional_ typing algorithms.

## From base types to logical qualifiers

We've previously seen the refining predicate's constraint domain ought
to be carefully chosen: in order to maintain decidable reconstruction
and automation, we have to give up on arbitrary program expressions and
propositions that we might enjoy in a higher-order logic like Coq, Agda, or
HOL.  To that end:  concretely, refinement predicates are drawn from arithmetic
and relational program expressions involving integer, boolean, and array sorts,
and conjunctions thereof.  (While not exhaustively enumerated in the paper, the
precise possible predicate types are documented [in the authors' implementation
of liquid types for
OCaml](https://github.com/ucsd-progsys/dsolve/blame/master/README#L97-L154).)
With a bit of squinting, we can see that these comprise the quantifier-free
theory of linear arithmetic and uninterpreted functions (QF-UFLIA)!  

It's clear that liquid types are more restrained in their expressivity than
full dependent types, for which type checking and reconstruction quickly wander
into the realm of undecidability[@SystemFUndecidable].  But, the tradeoff
pays dividends:  Since QF-UFLIA is decidable, so too is the _typechecking_ and
_reconstruction_ of a liquid type, since off-the-shelf SMT solvers like
[Yices](https://yices.csl.sri.com/) or Z3 can be used to check whether
refinement predicate in this logic is valid.  It's interesting that the initial
liquid types paper[@LiquidTypesPLDI08] mentions using an SMT solver almost as
an afterthought, whereas the subsequent
work([@LiquidTypesDSVerificationPLDI09], [@RefinementTypesForHaskell],
[@LowLevelLiquidTypesPOPL10], [@GradualLiquidTypeInference]) makes sure to
mention it explicitly and right in the abstract, suggesting that bringing this
particular kind of magic to bear reasonated with the research community.

## Subtyping as implication

Subtype polymorphism is an important component of many type systems, but
introduces complications that language designers need to carefully consider
since subtyping, anecdotally, tends to interact with language features in
non-trivial and unanticipated ways[@TaPL].

Subtyping is defined in terms of a _subsumption_ relation between two types:
recalling Liskov[@LiskovKeynote], `T1` is a subtype of `T2` if occurrences of
the more abstract `T2` can be transparently substituted for `T1`.  This
intuition lets us build a straightforward subtyping relationship for refinement
predicates: Stated in the language of logic: `T1` is _stronger_ as it places
more constraints on its inhabitants than `T2`.  Framed in a logical context,
asking whether the inhabitants of one type are subsumed by another is
equivalent to asking whether the is therefore checking the validity of the
implication T1 $\implies$ T2 under some context $\Gamma$.  This gives us `True`
and `False` as the extrema of our subtyping relation, as we would expect; we
will see shortly that by constraining the space of possible subtypes that we
explore, we form a lattice with `True` and `False` as our top and bottom.


$$
\begin{equation}
\begin{split}
\text{If the following is valid:} \; & \Gamma \; & \wedge \; & T_1 & \implies & T_2 \\
\text{Then the following typing judgement holds:} \; & \Gamma \; & \vdash \; & \{ v:\, B \; | \; T_1 \}  & <: & \{ v:\, B \; | \; T_2 \}\\
\end{split}
\end{equation}
$$
_Figure 5: The `Dec-<:-Base` typing rule: typing judgements follow from an
equality check on the base types and a validity check on the refinement
predicate subtyping relation.  Notice that the subtyping rule does not hold
if the base types are unequal but subtypes._

If programmers were manually annotating all their program terms with refinement
types, we could treat the internals of the SMT solver as magic, perform a simple
validity check, and go home early.  However, recall that our goal is type
_reconstruction_, not just _typechecking_; we need to divine a predicate
appropriate for the refinement type that is neither too weak (i.e. too abstract
to say anything meaningful) nor too strong (i.e. doesn't overfit to precisely
the concrete values inhabited by the type).  We saw before that the principal
type property of H-M type inference made "a good base typing" simply fall out
through unification; by contrast, conceivably, any number of "good refinement
typings" could be synthesized.  

```python
from itertools import product, count

def max1(x, y) -> {V | True}:              x if x > y else y
def max2(x, y) -> {V | V == x or V == y}:  x if x > y else y
def max3(x, y) -> {V | V >= x and V >= y}: x if x > y else y
def max4(x, y) -> {V | [(x==a and y==a+b and V == y) or (y==a and x==a+b and V == x) or
                        (x==a-b and y==a and V == y) or (y==a-b and x==a and V == x) 
                         for a,b in product(count(), 2)]} }: ...
```
_Figure 6: Four plausable typings of the `max()` function, each of varying
levels of goodness: note that `max4` depends upon an infinite number of
qualifiers!_

Recalling how the technique was applied to great effect whilst contemplating
model-checking solutions([@SlamProject], [@BLAST], [@Houdini]), a liquid type
reconstruction algorithm that consumes a set of _predefined qualifiers_ which
they treat as a sort of basis set that refinements will be constructed from.
So, a refinement predicate will be a conjunction of such qualifiers. Naturally,
this induces a bias into the reconstruction output: whoever wrote down the set
of qualifiers for predicate abstraction to choose from is in some sense
determining the "basis set" that will comprise a reconstructed liquid type.

```python
quals = [0 < V, 
         _ <= V, 
         V < _,
         len(_) <= V]
```
_Figure 7: The built-in qualifiers from the paper, in Solvent's internal
qualifier DSL.  The underbar token stands in for any appropriately-typed
program term and `V` is the distinguished value variable $v$._

By restricting the shape of each clause in the conjunction to ones derived from
the templates in the qualifier list, we're again giving up full expressivity.
This time, instead of constricting the overall logic to ensure decidability,
we're ensuring that the inference algorithm has a finite -- but hopefully
robust! -- search space to explore during predicate inference.

## Refinement type constraint generation

Constraint generation for the refinement predicate portion of the liquid type
follows a similar trajectory to that which we saw for base types.  The solver
begins by lifting the inferred base types into a refinement _template_ with a
constraint variable in place of a concrete predicate.  

Since we've seen that program terms can be substituted in for the `_` wildcard
in the qualifier list (see Figure 7), all refinement templates include a set of
_scope constraints_: intuitively, a scope constraint is an assertion in the
typing environment that a program term is in use at the particular point that
the type itself comes into scope.  A scope constraint says nothing about
whether the program term _needs_ to be used in a refining predicate, only that
it _may_ be.

A _flow constraint_, by comparison, is an assertion of some relationship
between program terms.  Critically, flow constraints are _path sensitive_: they
are an assumption in the typing environment that depends not on program values
but the control flow through the program.  For instance, an `if`-statement
would fork the typing environment into two flows: one in which the `then`
branch is taken and another when the `else` branch is taken.  At each leaf of
the AST we concretize a subtype containing a trivial qualfier: for instance,
`return x` qualfies the return type to be exactly `x`.

$$
\begin{equation}
\begin{split}
x:\text{int}; \, y:\text{int}; 
\begin{cases}
(x > y)     & \; \vdash \; \{ int \;|\; V = x \} <: \{ int \;|\; K_3 \} \\
\neg(x > y) & \; \vdash \; \{ int \;|\; V = y \} <: \{ int \;|\; K_3 \} 
\end{cases}
\end{split}
\end{equation}
$$
_Figure 8: A function annotated with refinement templates -- $K_1$, $K_2$, and
$K_3$ are constraint variables, and the typing context includes a
flow-sensitive subtyping relationship on the type of the return value, which is
dependent on which program branches are taken._

Given the constraints shown in Figure 7, an obvious but suboptimal type for
`max()`'s return value suggests itself.  We know that either branch of the
`if` must be taken; so, the disjunction of the subtype constraints would
technically work (see `max2()` in Figure 6).  This type, of course, only has
two inhabitants and wildly overfits to the input arguments; we'd like it to
generalize as much as possible.

### Abstraction from a fixed set of qualifiers


To generate a more general return type that that of Figure 6's `max2()`, we'll
construct an abstraction of the type using our built-in qualifiers and the
accumulated constraints as building blocks.  What we gain from these building
blocks -- a lattice formed by the conjunction of some fixed set of boolean
predicates -- is exactly the requirements to perform cartesian predicate
abstraction.

In particular, we take our _scope constraints_, having accumulated all possible
program terms, and substitute each constraint into the qualifier placeholder.
Given the typing environments in Figure 7, we'd be left with the qualifier set
`0 < V, V < x, V < y, x <= V, y <= V`.  (The final qualifier does not appear
because we have no scope constraint that types to a list.)

$$
\begin{equation}
\begin{split}
0 \leq v & & 
\star \leq v & &
\star \leq v & &
\star \lt v & &
\star \lt v \\
\{ int \;|\; v = x \} <: ( int \;|\: 0 \leq v & \; \wedge \;
                        & x \leq v & \; \wedge \;
                        & y \leq v & \; \wedge \;
                        & x \lt v & \; \wedge \;
                        & y \lt v) \\
\{ int \;|\; v = y \} <:( int \;|\: 0 \leq v & \; \wedge
                        & x \leq v & \; \wedge \;
                        & y \leq v & \; \wedge \;
                        & x \lt v & \; \wedge \;
                        & y \lt v) \\
\end{split}
\end{equation}
$$
_Figure 9: The strongest possible guess for `max()`'s return type: the
conjunction of every qualifier, expanded with every scope constraint.  It is
likely that, when transformed into an implication and checked by Z3, it will
prove to be too strong, and a refinement process to weaken the formula will
occur._

As the stronger the formula, the more precise the type, so we might hope that
the strongest possible formula -- conjoining the cross product of qualifiers
with scope constriants -- would produce the most qualified liquid type.
However, it's clear that the formula is too strong: `v = x` contradicts `v <
x`.  Intuitively: removing `v < x`, and any other contradictory clause, ought
to yield a formula that _does_ satisfy the subtyping relation. This happens to
be precisely the predicate abstraction refinement loop: while the proposed
refinement predicate does not follow from every flow-sensitive typing
environment, filter out the individual clauses that themselves do not follow,
weakening the type, and re-check.

\begin{equation}
\begin{split}
\{ int \;|\; v = x \} <:& \{ int \;|\: (\underline{0 \leq v}) & \; \wedge \;
                        & (x \leq v) & \; \wedge \;
                        & (y \leq v) & \; \wedge \;
                        & (\underline{x \lt v}) & \; \wedge \;
                        & (y \lt v) \}\\

\{ int \;|\; v = y \} <:& \{ int \;|\: (\underline{0 \leq v}) & \; \wedge \;
                        & (x \leq v) & \; \wedge \;
                        & (y \leq v) & \; \wedge \;
                        & (x \lt v) & \; \wedge \;
                        & (\underline{y \lt v}) \} \\

& \{ int \;|\: & 
                        & (x \leq v) & \; \wedge \;
                        & (y \leq v) \}
\end{split}
\end{equation}
_Figure 10: Predicate abstraction for the `max()` example: clauses that fail
the implication check are underlined.  The final refinement type can be read as
"an int $v$ that is no less than both x and y"._

Note that while the SMT solver could compute a validity counterproof, the
inference engine does not exploit this. While new qualifiers could conceivably
be mined from the counterexample, this is not explored in this work.  As a
result, the weakening process is strictly one that _removes_ qualifiers from
the conjunction.

### Extensions for recursive functions

Type reconstruction is complicated for recursive functions since the refinement
predicates now need to capture an inductive invariant for each iteration of the
computation.  Let's consider the following summation function that behaves
equivalently to `sum(range(k))`:

```{.python .numberLines}
@solvent.infer
def my_sum(k):
    "Computes \Sigma_{i=0}^{k} i."
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k
```

As before, the argument `k` will be typed to `int` with an unknown refinement
predicate variable $K_1$, as will the body of the function but with $K_2$.

$$
\begin{equation}
\begin{split}
k: K_1; \; \neg(k < 0); \;                     & \vdash \; \{ int \;|\; V = k - 1 \} & <: \{ int \;|\; K_1 \} \\
\\
k: K_1; \; k < 0 \;                            & \vdash \; \{ int \;|\; V = 0 \}     & <: \{ int \;|\; K_2 \} \\
k: K_1; \; \neg(k < 0); \; \underline{s = \text{sum}(k-1)} & \vdash \; \{ int \;|\; V = s + k \} & <: \{ int \;|\; K_2 \} \\
\end{split}
\end{equation}
$$
_An approximation for the subtyping relations for $K_1$ and $K_2$.  Notice that
we have placed the term-level assignment to `s` rather than a type assertion
for `s` in the typing context for expository reasons.  The intuition expressed
here will be made precise shortly._

Placing a function call and value assignment in a typing context as we've done
here would be invalid in a non-dependently typed language, and is arguably at
best an abuse of notation even here.  After all, the typing context should
contain the _type_ of `s`, not its runtime value.  However, the type of `s`
_does_ relate to the program term `k-1` because `s`'s type -- the return type
of the `sum()` function -- depends on that program term.  At runtime, we'd
perform beta-reduction and substitute all occurrences of `k` with the reduced
value of `k-1`.  We perform a similar (capture-avoiding) substitution at the
dependent type level, substituting the program _expression_ $k - 1$ for the
free variable $k$. This leaves us with the final set of constraints for $K_2$:

$$
\begin{equation}
\begin{split}
k: K_1; \; k < 0 \;                        & \vdash \; \{ int \;|\; V = 0 \}     & <: \{ int \;|\; K_2 \} \\
k: K_1; \; \neg(k < 0); \; s:[k-1/k]K_2 \; & \vdash \; \{ int \;|\; V = s + k \} & <: \{ int \;|\; K_2 \} \\
\end{split}
\end{equation}
$$

With our constraints finalized, we proceed with constraint solving just like
in the `sum()` example, where we learn from the base case's constraints that
$K_2 \; <: \; \{ int \;|\; 0 <= v \wedge k \leq v\}$. (It's possible that the
other path constraint will further remove one or more of these predicates in
subsequent refinement rounds if this type is too strong).  Moving to solving
the recursive case, we substitute the program expression `k-1` for the free
variable `k` in $K_2$:

\begin{equation}
\begin{split}
s: \; & [k-1/k]\,K_2 \\
s: \; & [k-1/k]\,\{ int \;|\; 0 <= v \wedge k \leq v\} \\
s: \; & \{ int \;|\; 0 <= v \wedge k-1 \leq v\} \\
      \implies & (0 <= s) \wedge (k-1 \leq s)
\end{split}
\end{equation}

In so doing, we have eliminated the free variables $k$ and $v$, lowered `s`'s
type assertion into its conjuncts, and yielded a straightforward typing
constraint to solve as we did with `max()`.  

\begin{equation}
\begin{split}
k < 0 & \vdash \{ int \;|\; v = 0 \} & <: \; & 
    (int \;|\: 0 \leq v & \; \wedge \; & k \leq v) \\

\neg(k < 0); \; (0 <= s); \; (k-1 \leq s) \; & \vdash \; \{ int \;|\; V = s + k \} & <: \; & 
    (int \;|\: 0 \leq v & \; \wedge \; & k \leq v) \\
\end{split}
\end{equation}

This substitution has let us infer some interesting facts: `s` must
be nonnegative, as must `k`: Z3 can therefore infer enough facts about their
sum to conclude that the type of `sum()` must be $int \rightarrow \{ int \;|\;
0 <= v \wedge k \leq v\}$.

> It would also be nice to have something about the implicit bias: this is
> a sort of heuristic for quantifier instantiation.

### Inferring `sum()`'s closed form with custom qualifiers and manual annotations

One final observation: We know the closed form of this summation:
$\Sigma_{i=0}^{n} \, =\, \frac{n * (n+1)}{2}$.  While a hypothetical oracle
could hand down a refinement type with this predicate, we know our current set
of qualifiers lack this particular expression shape, so it will never be found.

However, there's nothing that limits application programmers from inserting
their own bias into the reconstruction algorithm if they so choose: if we
_know_ we'd like a type with a particular shape to be inferred, and can express
it the liquid type system's qualifier DSL, then the system can incorporate it
into reconstruction.  

Simply adding `(_ * (_ + 1)) / 2` into the qualifier list alone doesn't
suffice, however: because the closed form only holds for _nonnegative_
integers, and `my_sum()` can consume any integer at all, the validity check on
this new qualifier will fail and predicate abstraction will filter it from the
valid qualifier list.  We can handle the nonnegativity requirement in two ways:
First, the qualifier can be made an implication `(_ >= 0) => (_ * (_ + 1)) /
2`, which is vacuously true in the base case and satisfied in the recursive
step case.  Second, we could abstain from adding the implication to the
qualifier, and instead _manually refine_ the type of the input argument `k` to
only consume non-negative values, which has the same effect.  Both solutions
are shown below:

```python
# Our two custom qualifiers: the precondition required for the closed form
# to hold, and the closed form itself.
nonneg = _ >= 0
closed_form = (_ * (_ + 1)) / 2 == V

# This implementation treats the precondition as part of the qualifier, yielding
# the implication as part of the return type's predicate:
#
# (k:int) -> {int | k <= V and 0 <= V and (-(k >= 0) or k * k + 1 / 2 == V })
@solvent.infer(user_quals=[nonneg.implies(closed_form)])
def my_sum(k):
    "Computes \Sigma_{i=0}^{k} i."
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k

# By contrast, this implementation adds the nonnegativity constraint as a 
# refinement of the argument to the sum: This simplifies the custom qualifier set
# and the return type's predicate, at the expense of explicitly stating the input
# type, and restricting the input domain.  The final inferred type is:
#
# (k:{int | V >= 0 }) -> {int | k <= V and 0 <= V and (k * k + 1 / 2 == V })
@solvent.infer(user_quals=[closed_form])
def my_sum(k: {int | nonneg}):
    "Computes \Sigma_{i=0}^{k} i."
    if k < 0:
        return 0
    else:
        s = my_sum(k - 1)
        return s + k
```
_Two different ways for an application developer to customise the type
inference procedure in order to reconstruct the closed form for `sum()`, each
with expressivity and automation tradeoffs.  Notice that the reconstructed
type could be further simplified to remove redundant clauses._

## Subsequent Work

The original liquid types paper focused on recursive programs in OCaml with an
eye towards provably eliding bounds checks, in the style of Dependent
ML[@DependentML] and previous ML refinement type work[@RefinementTypesForML].
Generalizing followup work came soon after, focusing on imperative programs in
C[@LowLevelLiquidTypesPOPL10] and lazy functional
languages[@RefinementTypesForHaskell].  More recently, follow-up work has been
done in integrating liquid types into a gradual typing
environment[@GradualLiquidTypeInference] and industrial languages like
TypeScript[@RefinementTypesForTypeScript].

More broadly, integration of SMT solvers into programming languages has been
explored by both higher-order function languages[@FStar] and imperative, OO-style
ones[@Dafny].

## Summary

Dependent type reconstruction is an impossibilty if careful constraints are not
placed on the type system.  Leveraging SMT for discharging subtyping checks
lets us maintain all the properties of simple polymorphic type systems while
increasing expressiveness.  We retain soundness -- certainly the most important
type-theoretic guarantee -- because we know Z3 and its theories are themselves
sound.  And subtyping and termination guarantees remain because our infinite
space of qualifiers is reduced to a finite lattice.

--

[^1]: In particular, those derived from the Hindley-Milner subset of System F,
  which we can intuit as being more or less equivalent in expressiveness to
  Scala, Haskell, or polymorphic Java[@JavaGenerics].  A critical feature of
  H-M type systems is that both typechecking and reconstruction (inference) is
  decidable and efficient.
[^2]: That is to say: trivally typing everybody to `⊤` won't do!
