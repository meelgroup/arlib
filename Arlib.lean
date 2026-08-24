/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib

A curated, Mathlib-style library of reusable Lean 4 results in randomised
algorithms and their analysis.

Importing `Arlib` pulls in every module the library exposes. Import an area
(e.g. `import Arlib.Probability`) for one subject, or a single module for one
piece.

This root re-exports every public area. Keep it a pure aggregation of area
roots — put content in the area modules, not here. **Each area root carries that
area's real documentation**: a substantial docstring explaining what the area is
for, how it is organised, and which conventions it commits to. Those are the
entry points; the list below is only a directory.

Every declaration lives in the namespace matching its module path. The two
deliberate exceptions are documented where they occur: `Arlib.Prelude`'s shared
notation, and the `Arlib.MDP` structure, which must share its area's namespace
so that dot notation on it resolves.

## Areas

Listed bottom-up, in dependency order.

* `Arlib.Prelude` — small shared notation, in particular the relative-error
  interval `(1 ± ε)·b` that every approximation guarantee is stated in.
* `Arlib.Combinatorics` — generic `Finset` / `List` / `BigOperators` helpers that
  recur but are not in Mathlib under a findable name: union-folds,
  powerset-of-union, a concatenation counting bound, `List.foldr min` bounds, the
  atoms of a finite family of sets.
* `Arlib.Communication` — two-party communication complexity as a measure of
  combinatorial structure: variable partitions, rectangles, covers and
  partitions of a fibre, the counting measures `Cov` and `Par`, nonnegative
  rank, and gadget composition — plus the same picture on abstract domains, for
  a split at a position in a word rather than at a variable.  It sits below both
  areas that use it, since a circuit lower bound and an automaton lower bound
  need the same rectangles and neither should depend on the other.
* `Arlib.Probability` — finite and discrete probability. Finite probability
  spaces with `Finset` events and real sums, the `FinDist`/`FinKernel`
  primitives, product and coin spaces, independence and k-wise independence,
  conditional expectation, couplings and total variation, moment and tail bounds
  (Markov, Chernoff, Freedman, median-of-means), Poisson laws. A smaller
  measure-theoretic layer covers stochastic approximation and martingale
  convergence, where no finite surrogate exists.
* `Arlib.InformationTheory` — discrete Shannon theory over a finite probability
  space: entropy, conditional entropy, mutual information, KL divergence, the
  chain rule, Gibbs' inequality, data processing, Fano, and the query lower
  bounds these give. Mathlib has none of this for discrete random variables.
* `Arlib.MarkovChains` — finite Markov chains: the `L²(μ)` calculus, the
  Dirichlet form and the Poincaré inequality, decay of variance and of
  χ²-divergence, total variation and mixing time, entropy decay, spectral
  independence and local-to-global techniques, and analyses of specific chains.
  The spectral gap is defined variationally throughout, never as `1 - λ₂`.
* `Arlib.Approximation` — relative-error approximation. The algebra of
  multiplicative error windows; FPRAS and FPAUS as predicates on a randomised
  algorithm, with self-reducibility, parsimonious reductions and amplification;
  Karp–Luby; and `Coresets/`, domain reduction for `ℓ¹` linear tests, together
  with the Lewis weights (`LewisWeights/`) whose row sampling produces the
  subspace embeddings it consumes.
* `Arlib.MDP` — finite Markov decision processes with reachability objectives:
  the model over a `FinKernel`, end components, the hitting-time weight and the
  contraction it supplies, `Q*` by value iteration, trajectory semantics, and
  policy values.
* `Arlib.GameTheory` — Yao's minimax principle, in the averaging form that
  lower-bound arguments actually use.
* `Arlib.KnowledgeCompilation` — representation languages for Boolean functions
  (NNF and its decomposable / deterministic / structured fragments, SDD,
  v-trees), size lower bounds obtained through the rectangle measures of
  `Arlib.Communication`, non-deterministic read-once branching programs,
  compilation by forgetting, and Tseitin formulas. Circuits are DAGs and size is
  a vertex count; see the area root for why that is not negotiable.
* `Arlib.Automata` — finite automata and the unambiguous fragment, and lower
  bounds on the number of states needed to complement, to union, and to
  separate, obtained through communication complexity.

## A caveat that applies across areas

Several headline theorems are **conditional**: they take a named `structure`
bundle standing for a result proved in the literature but not formalized here.
This is deliberate — such a result enters as an explicit hypothesis, never as an
`axiom`, so the statement displays what it rests on. The bundles are inhabited
wherever a witness is constructible, because a bundle with jointly unsatisfiable
fields would make every theorem taking it vacuously true while `#print axioms`
still looked clean. A few are deliberately not inhabited, and say so. Do not read
a conditional theorem as an unconditional one; `ARCHITECTURE.md` indexes them all.
-/

import Arlib.Prelude
import Arlib.Combinatorics
import Arlib.Communication
import Arlib.Probability
import Arlib.InformationTheory
import Arlib.MarkovChains
import Arlib.Approximation
import Arlib.MDP
import Arlib.GameTheory
import Arlib.KnowledgeCompilation
import Arlib.Automata
