/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Defs

/-!
# Gibbs' inequality

This file proves the single analytic fact that the rest of `Arlib.InformationTheory`
runs on: the sum `∑ a, p a * log (p a / q a)` is nonnegative whenever `p` and `q`
are nonnegative, `q` has total mass at most that of `p`, and `q` is absolutely
continuous over `p` (`q a = 0 → p a = 0`).

## Main results

* `Arlib.InformationTheory.sum_mul_log_div_nonneg` — Gibbs' inequality in the
  general (sub-normalised `q`) form.
* `Arlib.InformationTheory.KLdist_nonneg` — nonnegativity of the Kullback–Leibler
  divergence between two probability distributions.

## Implementation notes

The proof is the standard `log x ≤ x - 1` argument, applied termwise. Writing
`log (p a / q a) = - log (q a / p a)` and bounding `log (q a / p a) ≤ q a / p a - 1`
gives the termwise inequality `p a - q a ≤ p a * log (p a / q a)`; summing and
using `∑ q ≤ ∑ p` finishes. Mathlib's conventions `Real.log 0 = 0` and `x / 0 = 0`
make the degenerate terms behave, so no junk-value side conditions leak into the
statement.
-/

open scoped BigOperators
open Finset

namespace Arlib
namespace InformationTheory

/-- The termwise form of Gibbs' inequality: `p a - q a ≤ p a * log (p a / q a)`.
This is where `log x ≤ x - 1` is used. -/
private theorem sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hac : y = 0 → x = 0) : x - y ≤ x * Real.log (x / y) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · -- `x = 0`: the goal reduces to `0 ≤ y`.
    simp [← hx0, hy]
  · -- `x > 0`, hence `y ≠ 0` by contraposition of `hac`, hence `y > 0`.
    have hy0 : 0 < y := by
      rcases eq_or_lt_of_le hy with hy0 | hy0
      · exact absurd (hac hy0.symm) (ne_of_gt hx0)
      · exact hy0
    have hlog : Real.log (y / x) ≤ y / x - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    have hneg : Real.log (x / y) = -Real.log (y / x) := by
      rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hy0),
        Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)]
      ring
    rw [hneg]
    have hmul : x * Real.log (y / x) ≤ x * (y / x - 1) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hx0)
    have hxy : x * (y / x - 1) = y - x := by
      field_simp
    rw [hxy] at hmul
    linarith

/-- **Gibbs' inequality**, in the general form where `q` need only have total mass
at most that of `p`. This is the single analytic fact the rest of the area runs on. -/
theorem sum_mul_log_div_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsum : ∑ a, q a ≤ ∑ a, p a)
    (hac : ∀ a, q a = 0 → p a = 0) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by
  have key : ∑ a, (p a - q a) ≤ ∑ a, p a * Real.log (p a / q a) :=
    Finset.sum_le_sum fun a _ => sub_le_mul_log_div (hp a) (hq a) (hac a)
  have hsplit : ∑ a, (p a - q a) = (∑ a, p a) - ∑ a, q a := Finset.sum_sub_distrib p q
  rw [hsplit] at key
  linarith

/-- **Gibbs' inequality** / nonnegativity of KL divergence. -/
theorem KLdist_nonneg {α : Type} [Fintype α] {p q : α → ℝ}
    (hp : IsProbDist p) (hq : IsProbDist q) (hac : ∀ a, q a = 0 → p a = 0) :
    0 ≤ KLdist p q := by
  have hsum : ∑ a, q a ≤ ∑ a, p a := by rw [hp.sum_eq_one, hq.sum_eq_one]
  simpa only [KLdist] using
    sum_mul_log_div_nonneg p q hp.nonneg hq.nonneg hsum hac

end InformationTheory
end Arlib
