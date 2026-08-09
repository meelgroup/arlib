/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib

A curated, mathlib-style library of reusable Lean 4 + Mathlib lemmas, distilled
from the meelgroup formalization projects.

Importing `Arlib` pulls in every reusable module the library exposes. Import a
sub-namespace (e.g. `import Arlib.Probability`) to pull in just one area.

This root re-exports every public area of the library. Keep it as a pure
aggregation of area roots — put content in the area modules, not here.

## Areas

* `Arlib.Prelude` — small shared notation (e.g. the relative-error interval).
* `Arlib.Convexity` — log-concave functions on `ℝ`, and isoperimetry: the
  product-to-minimum conversion for partition expansion bounds, with the
  Kannan–Lovász–Simonovits one-dimensional inequality as an interface.
* `Arlib.Probability` — finite/discrete probability: finite probability spaces,
  product/coin spaces, independence, conditional expectation, Markov and
  median-of-means tail bounds.
* `Arlib.Combinatorics` — generic `Finset` / `List` / `BigOperators` helpers
  (union-folds, powerset-of-union, disjoint-union projection, a concatenation
  counting bound, `List.foldr min` bounds).
* `Arlib.Approximation` — relative-error approximation: the algebra of
  multiplicative error windows, and `Coresets/`, domain reduction for `ℓ¹` linear
  tests (weighted point sets, the functional `∑ᵢ μᵢ |⟨y, vᵢ⟩|`, subspace
  embeddings and their composition, tensor and Hadamard products, and the
  propagation invariant for a bottom-up reduction over a tree of regions).
* `Arlib.Algorithms` — analyses of specific algorithms, each split so that only
  the problem-independent half lives here. Currently the Tootsie Pop Algorithm:
  the Poisson law of its contraction counter, and almost-sure termination.
* `Arlib.MDP` — finite Markov decision processes with reachability objectives:
  the model over a `FinKernel`, end components, the hitting-time weight and the
  contraction it supplies, `Q*` by value iteration, trajectory semantics, and
  policy values.
* `Arlib.MarkovChains` — finite Markov chains: kernels, the `L²(μ)` calculus,
  the Dirichlet form and the Poincaré inequality, decay of variance and of
  χ²-divergence, total variation and mixing time, and analyses of specific
  chains.
* `Arlib.KnowledgeCompilation` — representation languages for Boolean functions
  (NNF and its decomposable / deterministic / structured fragments), the
  communication-complexity measures they are bounded by, size lower bounds, and
  non-deterministic read-once branching programs.
* `Arlib.Automata` — finite automata and the unambiguous fragment, and lower
  bounds on the number of states needed to complement, to union, and to
  separate, obtained through communication complexity.
-/

import Arlib.Prelude
import Arlib.Probability
import Arlib.Combinatorics
import Arlib.Approximation
import Arlib.GameTheory
import Arlib.InformationTheory
import Arlib.Algorithms
import Arlib.MarkovChains
import Arlib.KnowledgeCompilation
import Arlib.Automata
import Arlib.MDP
import Arlib.Convexity
