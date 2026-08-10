/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Yao's minimax principle (averaging direction)

Fix a finite set of inputs `I`, a finite set of deterministic algorithms `D`, and
a cost function `cost : I → D → ℝ` (for instance the number of queries, or an
error indicator).  A *randomized algorithm* is a probability distribution `r` on
`D`, and an *input distribution* is a probability distribution `Γ` on `I`.

Yao's minimax principle states that the worst-case cost of the best randomized
algorithm equals the best-case cost of the best deterministic algorithm against
the worst input distribution.  The full statement is an application of von
Neumann's minimax theorem and requires both directions.

**Only the "easy" (averaging) direction is formalized here**, namely
`Arlib.yao_minimax`:

> if *every* deterministic algorithm `d` has `Γ`-average cost at least `c`, then
> *every* randomized algorithm `r` has cost at least `c` on *some* input.

This is the direction that lower-bound arguments actually use: to lower bound
the worst-case cost (or error probability) of an arbitrary randomized algorithm,
it suffices to exhibit a single input distribution `Γ` under which every
deterministic algorithm has average cost at least `c`.  No minimax theorem, no
compactness, and no LP duality is needed — the whole content is the exchange of
the two finite sums, isolated here as `Arlib.sum_gamma_sum_r_comm`, together
with the observation that a weighted average never exceeds its maximum.

## Main results

* `Arlib.sum_gamma_sum_r_comm` : `∑ x, Γ x * (∑ d, r d * cost x d)`
  `= ∑ d, r d * (∑ x, Γ x * cost x d)`, i.e. the `Γ`-average of the randomized
  cost is the `r`-average of the deterministic average costs.
* `Arlib.yao_minimax` : the averaging direction of Yao's minimax principle.
-/

open scoped BigOperators

open Finset

namespace Arlib.GameTheory

/-- The `Γ`-average of the randomized cost equals the `r`-average of the
deterministic costs. This is the computation underlying `yao_minimax`. -/
theorem sum_gamma_sum_r_comm {I D : Type*} [Fintype I] [Fintype D]
    (cost : I → D → ℝ) (Γ : I → ℝ) (r : D → ℝ) :
    ∑ x, Γ x * (∑ d, r d * cost x d) = ∑ d, r d * (∑ x, Γ x * cost x d) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => by ring

/-- Yao's minimax principle (averaging form). If every deterministic algorithm `d`
has `Γ`-average cost at least `c`, then every randomized algorithm `r` has cost at
least `c` on some input. -/
theorem yao_minimax {I D : Type*} [Fintype I] [Fintype D]
    (cost : I → D → ℝ) (Γ : I → ℝ) (hΓ0 : ∀ x, 0 ≤ Γ x) (hΓ1 : ∑ x, Γ x = 1)
    (r : D → ℝ) (hr0 : ∀ d, 0 ≤ r d) (hr1 : ∑ d, r d = 1) (c : ℝ)
    (hdet : ∀ d : D, c ≤ ∑ x, Γ x * cost x d) :
    ∃ x : I, c ≤ ∑ d, r d * cost x d := by
  by_contra hcon
  push_neg at hcon
  -- The `Γ`-average of the randomized costs is at least `c`, by exchanging sums
  -- and averaging the deterministic bounds `hdet` with the weights `r`.
  have key : c ≤ ∑ x, Γ x * (∑ d, r d * cost x d) := by
    rw [sum_gamma_sum_r_comm]
    calc c = ∑ d, r d * c := by rw [← Finset.sum_mul, hr1, one_mul]
      _ ≤ ∑ d, r d * (∑ x, Γ x * cost x d) :=
          Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hdet d) (hr0 d)
  -- Since `∑ x, Γ x = 1 ≠ 0`, some input carries positive `Γ`-mass.
  obtain ⟨x₀, -, hx₀⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hΓ1]; exact one_ne_zero)
  have hx₀pos : 0 < Γ x₀ := lt_of_le_of_ne (hΓ0 x₀) (Ne.symm hx₀)
  -- But if every input has randomized cost `< c`, the `Γ`-average is `< c`.
  have hlt : ∑ x, Γ x * (∑ d, r d * cost x d) < ∑ x, Γ x * c := by
    refine Finset.sum_lt_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hcon x).le (hΓ0 x))
      ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon x₀) hx₀pos⟩
  rw [← Finset.sum_mul, hΓ1, one_mul] at hlt
  exact absurd key (not_le.mpr hlt)

end Arlib.GameTheory
