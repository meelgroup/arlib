/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Communication

Two-party communication complexity, as a *measure of combinatorial structure*
rather than as a theory of protocols: rectangles, covers and partitions of a
fibre, and the counting quantities `Cov`, `Par` and nonnegative rank that a
lower-bound argument actually consumes.

The area exists because two other areas need the same tool and neither should
depend on the other.  `Arlib.KnowledgeCompilation` needs it because the rectangle
lemma reads a structured d-DNNF of size `s` as a rectangular partition of
`f⁻¹(1)` into `s` pieces, so a bound on rectangles is a bound on circuit size.
`Arlib.Automata` needs it because a lower bound on the number of states of an
unambiguous automaton is a lower bound on the number of rectangles covering the
matrix of the language's prefix/suffix relation.  These two uses have nothing
else in common — one splits a v-tree, the other splits a word — and for a while
the machinery lived inside `KnowledgeCompilation` with `Automata` reaching into
it.  It is here instead, below both, so that the areas form a strict DAG and a
consumer who wants rectangles need not compile a paper about d-DNNF.

Nothing in this area imports anything else in the library except `Arlib.Prelude`.

## Two shapes of the same idea, kept apart on purpose

The area carries the two-party picture twice, and the duplication is deliberate.

* The **variable-partition** shape (`Rectangle`, `Measures`, `NonnegRank`,
  `Gadget`).  There is an ambient Boolean cube: a function
  `f : {0,1}^V → {0,1}`, a finite variable set `Z`, and a `VarPartition Z`
  splitting `Z` into Alice's variables and Bob's.  A rectangle is a pair of
  predicates on the *same* type `V → Bool`, each constrained to depend on one
  block.  This is the shape a circuit lower bound needs, because a rectangle has
  to be compared with the value of a circuit node on the *same* assignment.
* The **abstract-domain** shape (`TwoParty`).  A bare `F : X → Y → Bool` on two
  unrelated types, with no cube, no variables and no `Fintype`.  This is the
  shape an automaton needs, where the split is at a *position* in a word and the
  two halves need not even share an alphabet, and the shape sparse set
  disjointness needs, where `X = Y = binom([n], k)`.

The first is a special case of the second only after transporting along
`(V → Bool) ≃ (X → Bool) × (Y → Bool)`.  That equivalence exists; no argument in
the library wants to reason through it, and unifying the two would put a
coercion in the middle of every proof to buy a page of shared statements.  So the
abstract-domain names are prefixed `tp` (`tpCov`, `tpPar`, `TPRect`) rather than
overloading `fixedCov` / `fixedPar`, and `TwoParty.lean` says at its head exactly
which arguments want which.

## Predicates first, minima second

Every measure here is built in two steps: a `Prop`-valued predicate
`Has…OfSize … k`, and then the measure as `sInf` of the `k` satisfying it.  This
is not a stylistic preference.  No proof in this development ever computes a
minimum — an upper bound is always "here is a cover" and a lower bound is always
"no cover of that size exists" — so both directions are one application of
`Nat.sInf_le` or `Nat.notMem_of_lt_sInf`, and the minimum itself never has to be
examined.

The corollary is a hazard that is documented rather than engineered away:
`Nat.sInf` of the empty set is `0`, so a function admitting *no* finite cover has
`Cov = 0` rather than `∞`.  Upper bounds and lower bounds are unaffected;
*comparisons between two measures* are not, and so `fixedCov_le_fixedPar` and its
relatives carry an explicit `Partitionable` hypothesis.  That hypothesis is free
in practice, discharged once and for all by `partitionable_of_dependsOn`: a
function of the finite variable set `Z` has a rectangular partition of each fibre
into `2^{|Z|}` cells.  Valuing the measures in `ℕ∞` would put a `⊤` case into
every downstream arithmetic step in order to avoid a lemma that is proved once.

## Neither logarithms nor protocols

The literature renames these measures logarithmically — `NCC_b := log₂ Cov_b`,
`UCC_b := log₂ Par_b` — and identifies them with the cost of non-deterministic
and unambiguous two-party protocols.  Neither the logarithm nor the protocol
appears anywhere in this area.  Every quantitative statement its consumers make
is used in the exponentiated form `Cov₀(f) = 2^{NCC₀(f)}`, so taking logarithms
would introduce real numbers and `Nat.log`-versus-`Real.logb` rounding questions
in exchange for nothing; and the protocol characterisation is a citation to
Kushilevitz–Nisan used only as intuition, so formalizing protocols would add a
layer with no consumer.  Everything here stays in `ℕ`.

## Modules

* `Communication.BooleanFunction` — `DependsOn f Z`, "assignments agreeing on `Z`
  give `f` the same value", with its `List`-indexed reading `DependsOnList`
  derived from it rather than restated.  A fact about Boolean functions and not
  about communication; it is here because this area is the lowest node both
  consumers already share.  See the file's own docstring on that choice.
* `Communication.Rectangle` — `VarPartition` and balancedness, Π-rectangles as
  pairs of predicates each local to its side of the partition, `Fin k`-indexed
  covers and partitions, and the closure property `Rectangle.mem_cross` — if `α`
  and `β` lie in `R` then so does the assignment following `α` on `X` and `β` on
  `Y` — which is the only property of a rectangle any argument here uses.
* `Communication.Measures` — `fixedCov`/`fixedPar` and their best-partition
  counterparts `bestCov`/`bestPar`, the unfolded lower-bound forms in which a
  bound is consumed (`forall_not_hasCover_of_lt_bestCov`, a statement about
  *every* balanced partition at once), and the trivial `2^{|Z|}` upper bound.
* `Communication.NonnegRank` — nonnegative rank-one terms as pairs of *local
  real-valued functions*, the exact analogue of `Rectangle`, and
  `Par₁(F) ≥ rk⁺(F)`: a rectangular *partition* of `F⁻¹(1)` is a decomposition of
  `F` into that many nonnegative rank-one pieces.  Both halves of `Partitions`
  are needed, which is why the inequality is about `Par₁` and not `Cov₁`.  Also
  the approximate version `HasApproxNonnegRankOfSize`, which is what a lifting
  theorem lands in.
* `Communication.Gadget` — composing a Boolean function with a two-party gadget,
  the construction lifting theorems are about, and the exactly-balanced partition
  it induces.  Stated for a general variable type, so that taking it to be
  `ι ⊕ ι` gives the composition of the *doubled* function `f^∨` for free — which
  is how the union argument's four-block bookkeeping disappears.
* `Communication.TwoParty` — rectangles, covers, partitions and nonnegative rank
  for a bare `F : X → Y → Bool` on two arbitrary types, with no ambient Boolean
  cube and no `Fintype`.  The shape `Arlib.Automata` needs.
-/

import Arlib.Communication.BooleanFunction
import Arlib.Communication.Rectangle
import Arlib.Communication.Measures
import Arlib.Communication.NonnegRank
import Arlib.Communication.Gadget
import Arlib.Communication.TwoParty
