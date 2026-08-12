/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `Arlib.Probability`

A `FinProb` is a finite outcome type with an explicit mass function. Events are
`Finset`s, probabilities are real sums, and everything is decidable — which is
what makes combinatorial arguments (union bound, tail bounds) go through without
any measure theory.
-/
import Arlib.Probability

namespace ArlibTest.Probability

open Arlib.Probability Arlib.Probability.FinProb

/-- A fair coin, built from scratch. This is the whole interface: a finite `Ω`,
a nonnegative `mass`, and a proof that it sums to one. -/
noncomputable def fairCoin : FinProb where
  Ω := Bool
  μ :=
    { p := fun _ => 1 / 2
      p_nonneg := by intro _; norm_num
      p_sum := by simp }

/-- Probabilities of the two outcomes. -/
example : fairCoin.Pr {true} = 1 / 2 := by
  simp [FinProb.Pr, FinProb.mass, fairCoin]
  rfl

/-- The union bound, the workhorse of the area, over a `Finset` of events. -/
example (P : FinProb) (s : Finset ℕ) (E : ℕ → P.Event) :
    P.Pr (s.biUnion E) ≤ ∑ i ∈ s, P.Pr (E i) :=
  P.Pr_biUnion_le s E

/-- Every probability lies in `[0, 1]` — stated as the pair of bounds a caller
usually wants together. -/
example (P : FinProb) (E : P.Event) : 0 ≤ P.Pr E ∧ P.Pr E ≤ 1 :=
  ⟨P.Pr_nonneg E, P.Pr_le_one E⟩

/-- Monotonicity, and additivity on a disjoint union. -/
example (P : FinProb) (A B : P.Event) (h : Disjoint A B) :
    P.Pr A ≤ P.Pr (A ∪ B) ∧ P.Pr (A ∪ B) = P.Pr A + P.Pr B :=
  ⟨P.Pr_mono Finset.subset_union_left, P.Pr_union_disjoint h⟩

end ArlibTest.Probability
