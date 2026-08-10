/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Defs

/-!
# Basic bounds on Shannon entropy

This file proves the two elementary bounds every later result leans on:
entropy is nonnegative, and entropy is at most the log of the alphabet size.

The maximum-entropy bound is the only analytic content here. It is proved by the
standard `log x ≤ x - 1` argument, applied termwise to `1 / (N * p a)`, which
avoids any appeal to concavity or to Jensen's inequality: the difference
`Hdist p - log N` is written as a single sum whose `a`-th term is bounded by
`1 / N - p a`, and those bounds sum to zero.

## Main results

* `Hdist_nonneg`, `H_nonneg` — entropy is nonnegative.
* `Hdist_le_log_card`, `H_le_log_card` — the maximum-entropy bound.
* `H_bool_le_log_two` — the `Bool`-valued specialisation consumed by Fano's
  inequality.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Nonnegativity -/

/-- Entropy is nonnegative. -/
theorem Hdist_nonneg {α : Type} [Fintype α] {p : α → ℝ} (hp : IsProbDist p) :
    0 ≤ Hdist p := by
  show 0 ≤ ∑ a : α, Real.negMulLog (p a)
  exact Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hp.nonneg a) (hp.le_one a)

/-- Entropy of a random variable is nonnegative. -/
theorem H_nonneg {α : Type} [Fintype α] [DecidableEq α] {P : FinProb} (X : P.Ω → α) :
    0 ≤ H P X :=
  Hdist_nonneg (isProbDist_dist X)

/-! ### The maximum-entropy bound -/

/-- The termwise estimate behind `Hdist_le_log_card`: for `x ≥ 0` and `N > 0`,

`-x * log x - x * log N = x * log (1 / (N * x)) ≤ x * (1 / (N * x) - 1) = 1 / N - x`,

the middle step being `Real.log_le_sub_one_of_pos`. At `x = 0` both sides
degenerate and the bound reads `0 ≤ 1 / N`. -/
private theorem negMulLog_sub_mul_log_le {N : ℝ} (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x - x * Real.log N ≤ 1 / N - x := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · -- `hx0 : 0 = x`
    rw [← hx0]
    rw [Real.negMulLog_zero]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  · have hNx : (0 : ℝ) < N * x := mul_pos hN hx0
    have hkey : Real.log (1 / (N * x)) ≤ 1 / (N * x) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hrw : Real.negMulLog x - x * Real.log N = x * Real.log (1 / (N * x)) := by
      rw [Real.negMulLog_eq_neg, one_div, Real.log_inv,
        Real.log_mul (ne_of_gt hN) (ne_of_gt hx0)]
      ring
    have hmul : x * Real.log (1 / (N * x)) ≤ x * (1 / (N * x) - 1) :=
      mul_le_mul_of_nonneg_left hkey hx
    have hval : x * (1 / (N * x) - 1) = 1 / N - x := by
      field_simp
      ring
    linarith

/-- **Maximum-entropy bound.** A distribution on `α` has entropy at most
`log (card α)`, with the uniform distribution attaining it. -/
theorem Hdist_le_log_card {α : Type} [Fintype α] {p : α → ℝ} (hp : IsProbDist p) :
    Hdist p ≤ Real.log (Fintype.card α) := by
  have hne : Nonempty α := hp.nonempty
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hN : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hcard
  have hN' : ((Fintype.card α : ℝ)) ≠ 0 := ne_of_gt hN
  -- Rewrite `Hdist p - log N` as a single sum.
  have hsplit :
      Hdist p - Real.log (Fintype.card α)
        = ∑ a, (Real.negMulLog (p a) - p a * Real.log (Fintype.card α)) := by
    show (∑ a : α, Real.negMulLog (p a)) - Real.log (Fintype.card α) = _
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_eq_one, one_mul]
  -- Bound the sum termwise.
  have hbound :
      ∑ a, (Real.negMulLog (p a) - p a * Real.log (Fintype.card α))
        ≤ ∑ _a : α, (1 / (Fintype.card α : ℝ) - p _a) :=
    Finset.sum_le_sum fun a _ => negMulLog_sub_mul_log_le hN (hp.nonneg a)
  -- The bounds sum to zero.
  have hzero : ∑ _a : α, (1 / (Fintype.card α : ℝ) - p _a) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hp.sum_eq_one,
      nsmul_eq_mul]
    field_simp
  linarith

/-- **Maximum-entropy bound** for a random variable. -/
theorem H_le_log_card {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X : P.Ω → α) : H P X ≤ Real.log (Fintype.card α) :=
  Hdist_le_log_card (isProbDist_dist X)

/-- A `Bool`-valued random variable has entropy at most `log 2`. This is the form
Fano's inequality consumes. -/
theorem H_bool_le_log_two {P : FinProb} (X : P.Ω → Bool) : H P X ≤ Real.log 2 := by
  have h := H_le_log_card X
  rwa [Fintype.card_bool, Nat.cast_ofNat] at h

end InformationTheory
end Arlib
