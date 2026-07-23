/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `Arlib.Algorithms.TPA` — the Tootsie Pop Algorithm

Part of the `Arlib.Algorithms` area; see `Arlib/Algorithms.lean`.

The Tootsie Pop Algorithm (Huber, 2010) estimates a ratio of measures
`μ(B)/μ(B')` for a *centre* `B'` inside a *shell* `B`, given a family of nested
sets interpolating between them whose measure varies continuously.  It replaces
the classical self-reducibility product estimator, whose output is a product of
scaled binomials, by a single Poisson random variable — which is why its analysis
is sharp and why it is worth having as reusable infrastructure.

This sub-area holds the algorithm-independent part: the law of TPA's counter.  The
work of exhibiting a nested family for a particular counting problem, and of
showing that one contraction really does multiply the measure by a uniform
factor, belongs to the project that uses TPA.

## Modules

* `Arlib.Algorithms.TPA.Count` — the closed form `tpaTail` for `P(U₁ ⋯ U_m > c)`, its
  one-dimensional integral recursion, the resulting Poisson law for the number of
  contractions, and almost-sure termination.
* `Arlib.Algorithms.TPA.UniformProduct` — the identification of `tpaTail` with the
  probability it is named for: on the product of `m` copies of `Uniform(0,1)` the
  event `{U₁ ⋯ U_m > c}` really does have measure `tpaTail m c` (for `0 < c < 1`),
  and consecutive differences are the Poisson masses `poissonPMF (ln(1/c))`.
* `Arlib.Algorithms.TPA.TwoPhase` — the arithmetic of the two-phase run-count schedule: the
  exact phase-one threshold, the phase-two budget inequalities (which force
  `1 ≤ A`), and the passage from additive log accuracy to relative accuracy.
-/
import Arlib.Algorithms.TPA.Count
import Arlib.Algorithms.TPA.UniformProduct
import Arlib.Algorithms.TPA.TwoPhase
