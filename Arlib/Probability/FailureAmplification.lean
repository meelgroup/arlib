/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Repetition and the logarithmic sample bound

The bookkeeping shared by every "repeat until you succeed" argument, isolated so
that no downstream file has to redo it.

If a single attempt fails with probability at most `c < 1`, then `m` independent
attempts all fail with probability at most `c ^ m`, and driving that below a
confidence parameter `δ` costs

  `m ≥ log δ / log c`

repetitions.  `pow_le_of_log_div_le` is that implication, and
`le_of_pow_le` is its converse, which is what a *lower* bound on the number of
samples needs: an algorithm that succeeds with probability `1 - δ` on an
instance where failure has probability at least `c ^ (N-1)` must have taken
`N ≥ 1 + log δ / log c` samples.

Both directions come down to the same two facts: `Real.log` is monotone, and
`log c < 0` for `c ∈ (0,1)`, so dividing by it reverses inequalities.  Getting
that reversal the right way round is the only content, and it is exactly the
step that is easy to get wrong on paper.

Everything is proved from first principles with no `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

namespace Arlib.Probability

/-- For `c ∈ (0,1)`, `log c < 0`. -/
theorem log_neg_of_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : Real.log c < 0 :=
  Real.log_neg hc0 hc1

/-- **Enough repetitions.**  If a single attempt fails with probability at most
`c ∈ (0,1)`, then `m ≥ log δ / log c` repetitions drive the failure probability
below `δ`. -/
theorem pow_le_of_log_div_le {c δ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ)
    {m : ℕ} (hm : Real.log δ / Real.log c ≤ (m : ℝ)) : c ^ m ≤ δ := by
  have hlc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hmul : (m : ℝ) * Real.log c ≤ Real.log δ := (div_le_iff_of_neg hlc).1 hm
  have hpow : Real.log (c ^ m) ≤ Real.log δ := by
    rw [Real.log_pow]; exact hmul
  have hcm : (0 : ℝ) < c ^ m := pow_pos hc0 m
  calc c ^ m = Real.exp (Real.log (c ^ m)) := (Real.exp_log hcm).symm
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 hpow
    _ = δ := Real.exp_log hδ

/-- **Not enough repetitions.**  The converse: if `c ^ m ≤ δ` for `c ∈ (0,1)` and
`δ > 0`, then `m ≥ log δ / log c`.  This is the direction a sample-complexity
*lower* bound uses. -/
theorem log_div_le_of_pow_le {c δ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (_hδ : 0 < δ)
    {m : ℕ} (hm : c ^ m ≤ δ) : Real.log δ / Real.log c ≤ (m : ℝ) := by
  have hlc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hcm : (0 : ℝ) < c ^ m := pow_pos hc0 m
  have hlog : Real.log (c ^ m) ≤ Real.log δ := Real.log_le_log hcm hm
  rw [Real.log_pow] at hlog
  exact (div_le_iff_of_neg hlc).2 hlog

/-- The same, in the shifted form in which a lower bound on a *sample count*
appears: a failure event of probability `b · c ^ (N - 1)` that must be at most
`δ` forces `N ≥ 1 + log (δ / b) / log c`. -/
theorem one_add_log_div_le_of_mul_pow_le {b c δ : ℝ} (hb : 0 < b) (hc0 : 0 < c)
    (hc1 : c < 1) (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) (h : b * c ^ (N - 1) ≤ δ) :
    1 + Real.log (δ / b) / Real.log c ≤ (N : ℝ) := by
  have hδb : 0 < δ / b := div_pos hδ hb
  have hpow : c ^ (N - 1) ≤ δ / b := by
    rw [le_div_iff₀ hb, mul_comm]
    exact h
  have hlog := log_div_le_of_pow_le hc0 hc1 hδb hpow
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub hN
    simpa using this
  rw [hcast] at hlog
  linarith

/-- For any horizon `N` there is a failure probability `c` so close to `1` that
`c ^ N` still exceeds a prescribed threshold.  This is the divergence that makes
a size-only sample budget impossible: the instance parameter can always be
chosen to defeat it. -/
theorem exists_pow_gt (N : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ t < c ^ N := by
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set e : ℝ := 1 / ((N : ℝ) + 1) with he
  have he0 : 0 < e := by rw [he]; positivity
  refine ⟨t ^ e, Real.rpow_pos_of_pos ht0 e, Real.rpow_lt_one ht0.le ht1 he0, ?_⟩
  have hrw : (t ^ e) ^ N = t ^ (e * (N : ℝ)) := by
    rw [← Real.rpow_natCast (t ^ e) N, ← Real.rpow_mul ht0.le]
  rw [hrw]
  have hlt : e * (N : ℝ) < 1 := by
    rw [he, div_mul_eq_mul_div, one_mul, div_lt_one hden]
    linarith
  calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    _ < t ^ (e * (N : ℝ)) :=
        (Real.rpow_lt_rpow_left_iff_of_base_lt_one ht0 ht1).2 hlt

end Arlib.Probability
