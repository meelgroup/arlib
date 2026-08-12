/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.LewisWeights.Rademacher

/-!
# Even-moment Khintchine inequality for Rademacher sums

Building on the sub-Gaussian MGF bound `avg_exp_le` from `Rademacher.lean`, this
file proves the even-moment Khintchine inequality: for `k ≥ 1`,
`𝔼_σ (∑ᵢ σᵢ xᵢ)^(2k) ≤ (2 e k ∑ xᵢ²)^k`.

The proof extracts a single even power from `cosh` via its (termwise nonnegative)
power series (`pow_le_factorial_mul_cosh`), then optimises the free scale
`t = √(2k / ∑xᵢ²)`.

No `sorry`.
-/

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Extracting an even power from `cosh` -/

/-- A single even power is dominated by the corresponding term of the `cosh`
power series (all of whose terms are nonnegative): `u^(2k) ≤ (2k)! · cosh u`. -/
theorem pow_le_factorial_mul_cosh (u : ℝ) (k : ℕ) :
    u ^ (2 * k) ≤ (2 * k).factorial * Real.cosh u := by
  have hs := Real.hasSum_cosh u
  have hterm : u ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh u :=
    le_hasSum hs k (fun j _ => by
      apply div_nonneg
      · rw [pow_mul]; positivity
      · positivity)
  have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ hfac] at hterm
  exact le_of_le_of_eq hterm (mul_comm _ _)

/-! ## The even-moment Khintchine inequality -/

/-- **Even-moment Khintchine inequality.**  For `k ≥ 1`, the `2k`-th moment of a
sign sum is controlled by the `k`-th power of `2 e k` times the sum of squares:
`𝔼_σ (∑ᵢ σᵢ xᵢ)^(2k) ≤ (2 · e · k · ∑ xᵢ²)^k`.  Proved by extracting the even
power from `cosh` and optimising the scale `t = √(2k / ∑xᵢ²)`. -/
theorem avg_pow_le (x : ι → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    avg (fun s => (∑ i, Sgn (s i) * x i) ^ (2 * k))
      ≤ (2 * Real.exp 1 * (k : ℝ) * ∑ i, x i ^ 2) ^ k := by
  set s2 := ∑ i, x i ^ 2 with hs2def
  have hs2nonneg : 0 ≤ s2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases eq_or_lt_of_le hs2nonneg with hs2zero | hs2pos
  · -- Degenerate case `s2 = 0`: every `x i = 0`, both sides are `0`.
    have hx : ∀ i, x i = 0 := by
      intro i
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sq_nonneg (x i))).mp hs2zero.symm
      exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))
    have hzero : (fun s : ι → Bool => (∑ i, Sgn (s i) * x i) ^ (2 * k)) = fun _ => 0 := by
      funext s
      have hZ0 : (∑ i, Sgn (s i) * x i) = 0 := by
        apply Finset.sum_eq_zero; intro i _; rw [hx i, mul_zero]
      rw [hZ0, zero_pow (by omega : 2 * k ≠ 0)]
    have havgz : avg (fun _ : ι → Bool => (0 : ℝ)) = 0 := by unfold avg; simp
    rw [hzero, havgz, ← hs2zero]
    simp [zero_pow (show k ≠ 0 by omega)]
  · -- Main case `0 < s2`.
    have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have h2kR : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
    have h2kne : (2 * (k : ℝ)) ≠ 0 := ne_of_gt h2kR
    have harg : (0 : ℝ) ≤ 2 * (k : ℝ) / s2 := by positivity
    set t := Real.sqrt (2 * (k : ℝ) / s2) with htdef
    have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos h2kR hs2pos)
    have ht2 : t ^ 2 = 2 * (k : ℝ) / s2 := Real.sq_sqrt harg
    have ht2s2 : t ^ 2 * s2 = 2 * (k : ℝ) := by rw [ht2, div_mul_cancel₀ _ hs2ne]
    have htpow : (0 : ℝ) < t ^ (2 * k) := pow_pos htpos _
    have hfac_nonneg : (0 : ℝ) ≤ ((2 * k).factorial : ℝ) / t ^ (2 * k) :=
      div_nonneg (Nat.cast_nonneg _) htpow.le
    -- Rewriting a scaled sign sum.
    have hneg : ∀ s : ι → Bool,
        ∑ i, Sgn (s i) * (-(t * x i)) = -(t * ∑ i, Sgn (s i) * x i) := by
      intro s
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    -- Each exponential average is bounded by `exp k`.
    have hexp1 : avg (fun s : ι → Bool => Real.exp (t * ∑ i, Sgn (s i) * x i))
        ≤ Real.exp (k : ℝ) := by
      have hfun1 : (fun s : ι → Bool => Real.exp (t * ∑ i, Sgn (s i) * x i))
          = fun s => Real.exp (∑ i, Sgn (s i) * (t * x i)) := by
        funext s; congr 1
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hfun1]
      refine le_trans (avg_exp_le (fun i => t * x i)) (le_of_eq ?_)
      congr 1
      have he : ∑ i, (t * x i) ^ 2 = t ^ 2 * s2 := by
        rw [hs2def, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [he, ht2s2]; ring
    have hexp2 : avg (fun s : ι → Bool => Real.exp (-(t * ∑ i, Sgn (s i) * x i)))
        ≤ Real.exp (k : ℝ) := by
      have hfun2 : (fun s : ι → Bool => Real.exp (-(t * ∑ i, Sgn (s i) * x i)))
          = fun s => Real.exp (∑ i, Sgn (s i) * (-(t * x i))) := by
        funext s; rw [hneg s]
      rw [hfun2]
      refine le_trans (avg_exp_le (fun i => -(t * x i))) (le_of_eq ?_)
      congr 1
      have he : ∑ i, (-(t * x i)) ^ 2 = t ^ 2 * s2 := by
        rw [hs2def, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [he, ht2s2]; ring
    -- The `cosh` average is bounded by `exp k`.
    have hcosh_bound : avg (fun s => Real.cosh (t * ∑ i, Sgn (s i) * x i))
        ≤ Real.exp (k : ℝ) := by
      have hsplit : avg (fun s => Real.cosh (t * ∑ i, Sgn (s i) * x i))
          = (1 / 2) * (avg (fun s => Real.exp (t * ∑ i, Sgn (s i) * x i))
                       + avg (fun s => Real.exp (-(t * ∑ i, Sgn (s i) * x i)))) := by
        have hfe : (fun s : ι → Bool => Real.cosh (t * ∑ i, Sgn (s i) * x i))
            = fun s => (1 / 2) * (Real.exp (t * ∑ i, Sgn (s i) * x i)
                                + Real.exp (-(t * ∑ i, Sgn (s i) * x i))) := by
          funext s; rw [Real.cosh_eq]; ring
        rw [hfe, avg_const_mul, avg_add]
      rw [hsplit]
      have hadd : avg (fun s => Real.exp (t * ∑ i, Sgn (s i) * x i))
             + avg (fun s => Real.exp (-(t * ∑ i, Sgn (s i) * x i)))
             ≤ Real.exp (k : ℝ) + Real.exp (k : ℝ) := add_le_add hexp1 hexp2
      calc (1 / 2) * (avg (fun s => Real.exp (t * ∑ i, Sgn (s i) * x i))
                      + avg (fun s => Real.exp (-(t * ∑ i, Sgn (s i) * x i))))
          ≤ (1 / 2) * (Real.exp (k : ℝ) + Real.exp (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hadd (by norm_num)
        _ = Real.exp (k : ℝ) := by ring
    -- Pointwise: `Z^(2k) ≤ (2k)!/t^(2k) · cosh (t·Z)`.
    have hpoint : ∀ s : ι → Bool,
        (∑ i, Sgn (s i) * x i) ^ (2 * k)
          ≤ (((2 * k).factorial : ℝ) / t ^ (2 * k)) * Real.cosh (t * ∑ i, Sgn (s i) * x i) := by
      intro s
      have h1 := pow_le_factorial_mul_cosh (t * ∑ i, Sgn (s i) * x i) k
      rw [mul_pow] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ htpow]
      calc (∑ i, Sgn (s i) * x i) ^ (2 * k) * t ^ (2 * k)
          = t ^ (2 * k) * (∑ i, Sgn (s i) * x i) ^ (2 * k) := by ring
        _ ≤ ((2 * k).factorial : ℝ) * Real.cosh (t * ∑ i, Sgn (s i) * x i) := h1
    have havg_point : avg (fun s => (∑ i, Sgn (s i) * x i) ^ (2 * k))
        ≤ (((2 * k).factorial : ℝ) / t ^ (2 * k)) * avg (fun s => Real.cosh (t * ∑ i, Sgn (s i) * x i)) := by
      have := avg_mono hpoint
      rwa [avg_const_mul] at this
    have step1 : avg (fun s => (∑ i, Sgn (s i) * x i) ^ (2 * k))
        ≤ (((2 * k).factorial : ℝ) / t ^ (2 * k)) * Real.exp (k : ℝ) :=
      le_trans havg_point (mul_le_mul_of_nonneg_left hcosh_bound hfac_nonneg)
    -- Final arithmetic.
    have hfac_le : ((2 * k).factorial : ℝ) ≤ (2 * (k : ℝ)) ^ (2 * k) := by
      calc ((2 * k).factorial : ℝ) ≤ (↑((2 * k) ^ (2 * k)) : ℝ) := by
              exact_mod_cast Nat.factorial_le_pow (2 * k)
        _ = (2 * (k : ℝ)) ^ (2 * k) := by push_cast; ring
    have ht2k : t ^ (2 * k) = (2 * (k : ℝ) / s2) ^ k := by rw [pow_mul, ht2]
    have hexp_eq : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
      rw [← Real.exp_nat_mul, mul_one]
    have hEq : ((2 * (k : ℝ)) ^ (2 * k)) / (2 * (k : ℝ) / s2) ^ k * (Real.exp 1) ^ k
        = (2 * Real.exp 1 * (k : ℝ) * s2) ^ k := by
      rw [pow_mul, ← div_pow, ← mul_pow]
      congr 1
      field_simp
    calc avg (fun s => (∑ i, Sgn (s i) * x i) ^ (2 * k))
        ≤ (((2 * k).factorial : ℝ) / t ^ (2 * k)) * Real.exp (k : ℝ) := step1
      _ ≤ ((2 * (k : ℝ)) ^ (2 * k)) / t ^ (2 * k) * Real.exp (k : ℝ) := by
          gcongr
      _ = (2 * Real.exp 1 * (k : ℝ) * s2) ^ k := by rw [ht2k, hexp_eq]; exact hEq

end Arlib.Approximation.LewisWeights
