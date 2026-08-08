/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
/-
# The Shannon entropy of the Poisson distribution: a Stirling upper bound

Building on `Arlib.Probability.Poisson`, this module bounds the Shannon entropy

  `H(λ) = -∑ₖ pₖ log pₖ`,   `pₖ = poissonPMF λ k = e^{-λ} λ^k / k!`,

from above by the Gaussian shape `½ log(2πe λ)`, up to an explicit additive
constant.

## The route

Since `-log pₖ = λ - k logλ + log(k!)`, using `∑ₖ pₖ = 1` and the mean
`∑ₖ pₖ k = λ` gives the exact decomposition

  `H = λ - λ logλ + E_poi[log(k!)]`.

The crux is an upper bound on `E_poi[log(k!)]`.  We use the **Stirling upper
bound** `log(k!) ≤ k log k - k + ½ log k + 1` for `k ≥ 1`, which we extract from
Mathlib's `Stirling.stirlingSeq` (monotone with limit `√π`, so bounded above by
its first term `stirlingSeq 1 = e/√2`).  Averaging against the Poisson law needs
two facts:

* the **exact recurrence identity** `E_poi[k log k] = λ · E_poi[log(1+k)]`,
  a shift of the summation index using `(k+1) p_{k+1} = λ p_k`; and
* the **Jensen bound** `E_poi[log(1+k)] ≤ log(1+λ)`, proved by the tangent line
  `log x ≤ log a + (x-a)/a` to the concave logarithm, exported here as
  `tsum_poissonPMF_mul_log_one_add_le`.

Together these give `E_poi[log(k!)] ≤ λ log(1+λ) - λ + ½ log(1+λ) + 1`, whence

  `H ≤ ½ log(1+λ) + 2`   (`poisson_entropy_le_log_one_add`),

and, repackaged into the advertised Gaussian shape,

  `H ≤ ½ log(2πe(1+λ)) + (2 - ½ log(2πe))`   (`poisson_entropy_le`).

## The constant, honestly

The literal bound `H ≤ ½ log(2πeλ) + C` with a *fixed* constant `C` is **false**:
as `λ → 0⁺` the entropy tends to `0` while `½ log(2πeλ) → -∞`.  Any universally
valid bound of this shape must therefore have `1+λ` (or `λ + c`) inside the
logarithm, which is what we prove.  The additive constant achieved is
`2 - ½ log(2πe) ≈ 0.581`; equivalently the clean form `½ log(1+λ) + 2`.  The
leading term `½ log λ` (coefficient `½`, not `1`) is the correct Gaussian shape
and is what makes the Stirling `½ log k` term (as opposed to the cruder integral
bound) necessary.

No `sorry`.
-/
import Arlib.Probability.Poisson
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace Arlib

open scoped Nat

/-! ## Elementary analytic helpers -/

/-- The quadratic-vs-exponential bound `x² ≤ 4 e^x` for `x ≥ 0`.  It follows from
`e^{x/2} ≥ x/2 + 1 ≥ x/2` squared.  Used only to produce a summable majorant for
`k ↦ pₖ log(k!)`. -/
theorem sq_le_four_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 4 * Real.exp x := by
  have h1 : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp (x / 2)
  have hnn : (0 : ℝ) ≤ x / 2 := by linarith
  have hle : x / 2 ≤ Real.exp (x / 2) := by linarith
  have h3 : (x / 2) ^ 2 ≤ (Real.exp (x / 2)) ^ 2 := pow_le_pow_left₀ hnn hle 2
  have h4 : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  nlinarith [h3, h4]

/-- The crude bound `log(k!) ≤ k²`, from `k! ≤ k^k` and `log k ≤ k`.  A summable
majorant, not the sharp Stirling estimate. -/
theorem log_factorial_le_sq (k : ℕ) : Real.log (k ! : ℝ) ≤ (k : ℝ) ^ 2 := by
  have hkkpos : 0 < k ^ k := lt_of_lt_of_le (Nat.factorial_pos k) (Nat.factorial_le_pow k)
  have h1 : Real.log (k ! : ℝ) ≤ Real.log ((k ^ k : ℕ) : ℝ) :=
    (Real.log_le_log_iff (by exact_mod_cast Nat.factorial_pos k)
      (by exact_mod_cast hkkpos)).mpr (by exact_mod_cast Nat.factorial_le_pow k)
  rw [Nat.cast_pow, Real.log_pow] at h1
  have h2 : Real.log (k : ℝ) ≤ (k : ℝ) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) by exact_mod_cast h)
      linarith
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [h1, h2, hknn]

/-- Monotonicity: `log k ≤ log (1 + k)`. -/
theorem log_le_log_one_add (k : ℕ) : Real.log (k : ℝ) ≤ Real.log (1 + (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · exact (Real.log_le_log_iff (by exact_mod_cast h) (by positivity)).mpr (by linarith)

/-- **Stirling's upper bound** on `log(k!)`:
`log(k!) ≤ k log k - k + ½ log k + 1` for every `k`.

For `k ≥ 1` this is `Stirling.log_stirlingSeq_formula` combined with the fact that
`log ∘ stirlingSeq ∘ succ` is antitone, so bounded above by its value at `0`,
namely `log (stirlingSeq 1) = log (e/√2) = 1 - ½ log 2`.  For `k = 0` both sides
are compared directly (`0 ≤ 1`). -/
theorem log_factorial_le (k : ℕ) :
    Real.log (k ! : ℝ) ≤ (k : ℝ) * Real.log k - k + Real.log k / 2 + 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have h1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
      rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp, Real.log_sqrt (by norm_num)]
    have hanti : Real.log (Stirling.stirlingSeq (n + 1)) ≤ 1 - Real.log 2 / 2 := by
      rw [← h1]; exact Stirling.log_stirlingSeq'_antitone (Nat.zero_le n)
    have hform := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity)] at hform
    push_cast at hform ⊢
    nlinarith [hform, hanti]

/-! ## Summability of the entropy pieces -/

/-- `k ↦ pₖ log(1+k)` is summable: it is dominated by the mean series `pₖ · k`,
since `log(1+k) ≤ k`. -/
theorem summable_poissonPMF_mul_log_one_add {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (fun k : ℕ => poissonPMF lam k * Real.log (1 + (k : ℝ))) := by
  apply Summable.of_nonneg_of_le _ _ (summable_poissonPMF_mul_id lam)
  · intro k
    refine mul_nonneg (poissonPMF_nonneg hlam k) (Real.log_nonneg ?_)
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  · intro k
    refine mul_le_mul_of_nonneg_left ?_ (poissonPMF_nonneg hlam k)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (k : ℝ) by positivity)
    linarith

/-- `k ↦ pₖ log(k!)` is summable: it is dominated by `4 · pₖ e^{k}`, using
`log(k!) ≤ k² ≤ 4 e^{k}` and the moment generating function. -/
theorem summable_poissonPMF_mul_log_factorial {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (fun k : ℕ => poissonPMF lam k * Real.log (k ! : ℝ)) := by
  apply Summable.of_nonneg_of_le _ _
    ((hasSum_poissonPMF_mul_exp lam 1).summable.mul_left 4)
  · intro k
    refine mul_nonneg (poissonPMF_nonneg hlam k) (Real.log_nonneg ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  · intro k
    have hfk : Real.log (k ! : ℝ) ≤ (k : ℝ) ^ 2 := log_factorial_le_sq k
    have hq : ((k : ℝ)) ^ 2 ≤ 4 * Real.exp (k : ℝ) := sq_le_four_mul_exp (Nat.cast_nonneg k)
    have hpk := poissonPMF_nonneg hlam k
    have hstep : poissonPMF lam k * Real.log (k ! : ℝ)
        ≤ poissonPMF lam k * (4 * Real.exp (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpk
    calc poissonPMF lam k * Real.log (k ! : ℝ)
        ≤ poissonPMF lam k * (4 * Real.exp (k : ℝ)) := hstep
      _ = 4 * (poissonPMF lam k * Real.exp (1 * (k : ℝ))) := by rw [one_mul]; ring

/-! ## The Jensen bound `E_poi[log(1+k)] ≤ log(1+λ)` -/

/-- **Jensen's inequality for the concave logarithm against the Poisson law**:
`∑ₖ pₖ log(1+k) ≤ log(1+λ)`.

Proved via the tangent-line majorant `log x ≤ log(1+λ) + (x-(1+λ))/(1+λ)` at
`x = 1+k` (which is `Real.log_le_sub_one_of_pos` after dividing by `1+λ`); the
linear majorant sums exactly to `log(1+λ)` because `∑ₖ pₖ (k-λ) = 0`.

This is independently useful for any Poisson computation that must control the
average of a slowly growing function. -/
theorem tsum_poissonPMF_mul_log_one_add_le {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑' k : ℕ, poissonPMF lam k * Real.log (1 + (k : ℝ)) ≤ Real.log (1 + lam) := by
  have hla : (0 : ℝ) < 1 + lam := by linarith
  have hne : (1 : ℝ) + lam ≠ 0 := ne_of_gt hla
  have hmaj : HasSum (fun k : ℕ => poissonPMF lam k *
      (Real.log (1 + lam) + ((k : ℝ) - lam) / (1 + lam))) (Real.log (1 + lam)) := by
    have hA := (hasSum_poissonPMF lam).mul_left (Real.log (1 + lam))
    have hB := (hasSum_poissonPMF_mul_id lam).mul_left (1 / (1 + lam))
    have hC := (hasSum_poissonPMF lam).mul_left (lam / (1 + lam))
    have h := (hA.add hB).sub hC
    have hval : Real.log (1 + lam) * 1 + 1 / (1 + lam) * lam - lam / (1 + lam) * 1
        = Real.log (1 + lam) := by field_simp
    rw [hval] at h
    refine h.congr_fun (fun k => ?_)
    field_simp
    ring
  have hle : ∀ k : ℕ, poissonPMF lam k * Real.log (1 + (k : ℝ)) ≤
      poissonPMF lam k * (Real.log (1 + lam) + ((k : ℝ) - lam) / (1 + lam)) := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_ (poissonPMF_nonneg hlam k)
    have hx : (0 : ℝ) < (1 + (k : ℝ)) / (1 + lam) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) hne] at hlog
    have hrw : (1 + (k : ℝ)) / (1 + lam) - 1 = ((k : ℝ) - lam) / (1 + lam) := by
      field_simp
    rw [hrw] at hlog
    linarith
  calc ∑' k, poissonPMF lam k * Real.log (1 + (k : ℝ))
      ≤ ∑' k, poissonPMF lam k * (Real.log (1 + lam) + ((k : ℝ) - lam) / (1 + lam)) :=
        tsum_le_tsum hle (summable_poissonPMF_mul_log_one_add hlam) hmaj.summable
    _ = Real.log (1 + lam) := hmaj.tsum_eq

/-! ## The recurrence identity `E_poi[k log k] = λ · E_poi[log(1+k)]` -/

/-- The exact identity `∑ₖ pₖ · k · log k = λ · ∑ₖ pₖ log(1+k)`, obtained by
shifting the summation index with `(k+1) p_{k+1} = λ p_k`. -/
theorem hasSum_poissonPMF_mul_id_mul_log {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k : ℕ => poissonPMF lam k * (k : ℝ) * Real.log (k : ℝ))
      (lam * ∑' j : ℕ, poissonPMF lam j * Real.log (1 + (j : ℝ))) := by
  have hL : HasSum (fun j : ℕ => poissonPMF lam j * Real.log (1 + (j : ℝ)))
      (∑' j : ℕ, poissonPMF lam j * Real.log (1 + (j : ℝ))) :=
    (summable_poissonPMF_mul_log_one_add hlam).hasSum
  have hshift : HasSum (fun j : ℕ =>
      poissonPMF lam (j + 1) * ((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ))
      (lam * ∑' j : ℕ, poissonPMF lam j * Real.log (1 + (j : ℝ))) := by
    refine (hL.mul_left lam).congr_fun (fun j => ?_)
    have hs := succ_mul_poissonPMF_succ lam j
    have hlogeq : Real.log (((j + 1 : ℕ)) : ℝ) = Real.log (1 + (j : ℝ)) := by
      push_cast; rw [add_comm]
    rw [hlogeq]
    push_cast
    linear_combination (Real.log (1 + (j : ℝ))) * hs
  have hmain := (hasSum_nat_add_iff
    (f := fun k : ℕ => poissonPMF lam k * (k : ℝ) * Real.log (k : ℝ)) 1).mp hshift
  simpa using hmain

/-! ## The Stirling bound on `E_poi[log(k!)]` -/

/-- **Upper bound on the Poisson average of `log(k!)`**:
`∑ₖ pₖ log(k!) ≤ λ log(1+λ) - λ + ½ log(1+λ) + 1`.

Averaging the Stirling bound `log(k!) ≤ k log k - k + ½ log k + 1`
(`log_factorial_le`, with `log k ≤ log(1+k)`) against the Poisson law and using
the identity `∑ₖ pₖ k log k = λ ∑ₖ pₖ log(1+k)` and the Jensen bound
`∑ₖ pₖ log(1+k) ≤ log(1+λ)`. -/
theorem tsum_poissonPMF_mul_log_factorial_le {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑' k : ℕ, poissonPMF lam k * Real.log (k ! : ℝ)
      ≤ lam * Real.log (1 + lam) - lam + Real.log (1 + lam) / 2 + 1 := by
  set L := ∑' j : ℕ, poissonPMF lam j * Real.log (1 + (j : ℝ)) with hLdef
  have hL : HasSum (fun j : ℕ => poissonPMF lam j * Real.log (1 + (j : ℝ))) L :=
    (summable_poissonPMF_mul_log_one_add hlam).hasSum
  have hID_log := hasSum_poissonPMF_mul_id_mul_log hlam
  rw [← hLdef] at hID_log
  have hID := hasSum_poissonPMF_mul_id lam
  have hLog1 := hL.mul_left (1 / 2)
  have hMass := hasSum_poissonPMF lam
  have hg : HasSum (fun k : ℕ => poissonPMF lam k *
      ((k : ℝ) * Real.log (k : ℝ) - k + Real.log (1 + (k : ℝ)) / 2 + 1))
      (lam * L - lam + 1 / 2 * L + 1) := by
    have h := ((hID_log.sub hID).add hLog1).add hMass
    refine h.congr_fun (fun k => ?_)
    ring
  -- pointwise Stirling bound
  have hN : ∀ k : ℕ, Real.log (k ! : ℝ) ≤
      (k : ℝ) * Real.log (k : ℝ) - k + Real.log (1 + (k : ℝ)) / 2 + 1 := by
    intro k
    have h1 := log_factorial_le k
    have h2 := log_le_log_one_add k
    linarith
  have hbound : ∑' k : ℕ, poissonPMF lam k * Real.log (k ! : ℝ) ≤ lam * L - lam + 1 / 2 * L + 1 := by
    rw [← hg.tsum_eq]
    exact tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hN k) (poissonPMF_nonneg hlam k))
      (summable_poissonPMF_mul_log_factorial hlam) hg.summable
  have hJ : L ≤ Real.log (1 + lam) := tsum_poissonPMF_mul_log_one_add_le hlam
  have hLmul : lam * L ≤ lam * Real.log (1 + lam) := mul_le_mul_of_nonneg_left hJ hlam
  linarith [hbound, hJ, hLmul]

/-! ## The entropy bound -/

/-- **Shannon entropy of the Poisson distribution — clean form.**
For `λ > 0`,

  `H(λ) = -∑ₖ pₖ log pₖ ≤ ½ log(1+λ) + 2`.

Via the exact decomposition `H = λ - λ logλ + E_poi[log(k!)]` (from `∑ pₖ = 1`
and `∑ pₖ k = λ`), the Stirling bound `tsum_poissonPMF_mul_log_factorial_le`, and
`λ log(1+λ) ≤ λ logλ + 1` (tangent line to `log`). -/
theorem poisson_entropy_le_log_one_add {lam : ℝ} (hlam : 0 < lam) :
    -(∑' k : ℕ, poissonPMF lam k * Real.log (poissonPMF lam k))
      ≤ Real.log (1 + lam) / 2 + 2 := by
  -- pointwise logarithm of the mass function
  have hlogp : ∀ k : ℕ, Real.log (poissonPMF lam k)
      = -lam + (k : ℝ) * Real.log lam - Real.log (k ! : ℝ) := by
    intro k
    rw [poissonPMF, Real.log_div
        (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero k (ne_of_gt hlam)))
        (by exact_mod_cast Nat.factorial_ne_zero k),
      Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero k (ne_of_gt hlam)),
      Real.log_exp, Real.log_pow]
  have hSlogsum : HasSum (fun k : ℕ => poissonPMF lam k * Real.log (k ! : ℝ))
      (∑' k, poissonPMF lam k * Real.log (k ! : ℝ)) :=
    (summable_poissonPMF_mul_log_factorial hlam.le).hasSum
  have hdecomp : HasSum (fun k : ℕ => poissonPMF lam k * Real.log (poissonPMF lam k))
      (-lam + Real.log lam * lam - ∑' k, poissonPMF lam k * Real.log (k ! : ℝ)) := by
    have hA := (hasSum_poissonPMF lam).mul_left (-lam)
    have hB := (hasSum_poissonPMF_mul_id lam).mul_left (Real.log lam)
    have hC := hSlogsum.neg
    have h := (hA.add hB).add hC
    have hval : -lam * 1 + Real.log lam * lam + -(∑' k, poissonPMF lam k * Real.log (k ! : ℝ))
        = -lam + Real.log lam * lam - ∑' k, poissonPMF lam k * Real.log (k ! : ℝ) := by ring
    rw [hval] at h
    refine h.congr_fun (fun k => ?_)
    rw [hlogp k]; ring
  have heq : ∑' k, poissonPMF lam k * Real.log (poissonPMF lam k)
      = -lam + Real.log lam * lam - ∑' k, poissonPMF lam k * Real.log (k ! : ℝ) :=
    hdecomp.tsum_eq
  rw [heq]
  have hB := tsum_poissonPMF_mul_log_factorial_le hlam.le
  -- tangent-line bound `λ log(1+λ) - λ logλ ≤ 1`
  have htan : lam * Real.log (1 + lam) - lam * Real.log lam ≤ 1 := by
    have hx : (0 : ℝ) < (1 + lam) / lam := div_pos (by linarith) hlam
    have hlog := Real.log_le_sub_one_of_pos hx
    have hmul := mul_le_mul_of_nonneg_left hlog hlam.le
    have h2 : lam * ((1 + lam) / lam - 1) = 1 := by field_simp
    have hsplit : Real.log ((1 + lam) / lam) = Real.log (1 + lam) - Real.log lam :=
      Real.log_div (by positivity) (ne_of_gt hlam)
    rw [h2, hsplit] at hmul
    have hdist : lam * (Real.log (1 + lam) - Real.log lam)
        = lam * Real.log (1 + lam) - lam * Real.log lam := by ring
    linarith [hmul, hdist]
  nlinarith [hB, htan]

/-- **Shannon entropy of the Poisson distribution — Gaussian shape.**
For `λ > 0`,

  `H(λ) = -∑ₖ pₖ log pₖ ≤ ½ log(2πe(1+λ)) + (2 - ½ log(2πe))`.

The additive constant is `2 - ½ log(2πe) ≈ 0.581`.  The `1+λ` inside the
logarithm (rather than `λ`) is necessary for a universal fixed constant: as
`λ → 0⁺` the entropy tends to `0` but `½ log(2πeλ) → -∞`.  See the module
docstring. -/
theorem poisson_entropy_le {lam : ℝ} (hlam : 0 < lam) :
    -(∑' k : ℕ, poissonPMF lam k * Real.log (poissonPMF lam k))
      ≤ Real.log (2 * Real.pi * Real.exp 1 * (1 + lam)) / 2
        + (2 - Real.log (2 * Real.pi * Real.exp 1) / 2) := by
  have hbase := poisson_entropy_le_log_one_add hlam
  have hsplit : Real.log (2 * Real.pi * Real.exp 1 * (1 + lam))
      = Real.log (2 * Real.pi * Real.exp 1) + Real.log (1 + lam) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [hsplit]
  linarith [hbase]

end Arlib
