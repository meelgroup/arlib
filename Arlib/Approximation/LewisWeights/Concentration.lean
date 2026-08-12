/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The ℓ₁ concentration bound: the per-row moment estimate

The quantitative core of Cohen–Peng's `momBound` (§6).  For a matrix whose ℓ₁
Lewis weights are all at most `U`, each row's Rademacher process

`∑ⱼ σⱼ · wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ)`   (`M = gram w a`)

has `2k`-th moment at most `(2 e k U)^k`.  This is Khintchine (`avg_pow_le`)
applied to the vector `xⱼ = wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ)`, whose energy `∑ⱼ xⱼ²` is
bounded by `U` through the Lewis identity `sum_sq_lev` together with the uniform
bound `wⱼ ≤ U`.  It is Cohen–Peng's "`U w̄⁻² · aᵢᵀM⁻¹aᵢ = U`" step, made
rigorous: the middle collapses to `gram`, `gram·gram⁻¹ = 1`, and `wⱼ ≤ U`
supplies the `U`.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Khintchine
import Arlib.Approximation.LewisWeights.LinAlg

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-! ## Symmetry of the inverse bilinear form -/

omit [DecidableEq d] in
/-- For a symmetric matrix `S`, the bilinear form `x ⬝ᵥ S y` is symmetric. -/
theorem dotProduct_mulVec_symm {S : Matrix d d ℝ} (hS : Sᵀ = S) (x y : d → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]

variable {w : ι → ℝ} {a : ι → d → ℝ}

omit [DecidableEq ι] in
/-- The inverse Gram matrix is symmetric. -/
theorem gram_inv_transpose (w : ι → ℝ) (a : ι → d → ℝ) :
    ((gram w a)⁻¹)ᵀ = (gram w a)⁻¹ := by
  have hHerm : ((gram w a)⁻¹).IsHermitian := (gram_isHermitian w a).inv
  ext p q
  have h := congrFun (congrFun hHerm p) q
  simp only [Matrix.conjTranspose_apply, star_trivial] at h
  simpa [Matrix.transpose_apply] using h

omit [DecidableEq ι] in
/-- `aᵢ ⬝ᵥ M⁻¹ aⱼ = aⱼ ⬝ᵥ M⁻¹ aᵢ`: the leverage bilinear form is symmetric. -/
theorem inv_bilin_symm (i j : ι) :
    a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j) = a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i) :=
  dotProduct_mulVec_symm (gram_inv_transpose w a) (a i) (a j)

/-! ## The energy bound -/

omit [DecidableEq ι] in
/-- **The per-row energy bound.**  If `w` are the ℓ₁ Lewis weights, all at most
`U`, then `∑ⱼ (wᵢ⁻¹ aᵢᵀM⁻¹aⱼ)² ≤ U`.  Uses `sum_sq_lev` (`∑ⱼ wⱼ⁻¹(aⱼᵀM⁻¹aᵢ)²
= aᵢᵀM⁻¹aᵢ = wᵢ²`) and `1 ≤ U wⱼ⁻¹` from `wⱼ ≤ U`. -/
theorem sum_bilin_sq_le (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) (i : ι) :
    ∑ j, ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j))) ^ 2 ≤ U := by
  have hPD := hL.1
  have hterm : ∀ j, ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j))) ^ 2
      = (w i)⁻¹ ^ 2 * (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2 := by
    intro j; rw [inv_bilin_symm i j]; ring
  simp_rw [hterm, ← Finset.mul_sum]
  have hlev : ∑ j, (w j)⁻¹ * (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2 = (w i) ^ 2 := by
    rw [sum_sq_lev hPD, hL.2 i]
  have hbound : ∑ j, (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2 ≤ U * (w i) ^ 2 := by
    rw [← hlev, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hwj : (1 : ℝ) ≤ U * (w j)⁻¹ := by
      have h1 : w j * (w j)⁻¹ = 1 := mul_inv_cancel₀ (hw j).ne'
      have h2 : w j * (w j)⁻¹ ≤ U * (w j)⁻¹ :=
        mul_le_mul_of_nonneg_right (hU j) (inv_nonneg.mpr (hw j).le)
      rw [h1] at h2; exact h2
    nlinarith [mul_nonneg (sub_nonneg.mpr hwj)
      (sq_nonneg (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)))]
  have hwi : (w i)⁻¹ ^ 2 * (w i) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (hw i).ne', one_pow]
  calc (w i)⁻¹ ^ 2 * ∑ j, (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2
      ≤ (w i)⁻¹ ^ 2 * (U * (w i) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = U := by rw [← mul_assoc, mul_comm ((w i)⁻¹ ^ 2) U, mul_assoc, hwi, mul_one]

/-! ## The per-row moment bound -/

/-- **The per-row moment bound** (Cohen–Peng `momBound`, single term).  Under the
Lewis property with all weights `≤ U`, the `2k`-th Rademacher moment of row `i`'s
process is at most `(2 e k U)^k`. -/
theorem avg_row_pow_le (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) {k : ℕ} (hk : 1 ≤ k) (i : ι) :
    avg (fun s => (∑ j, Sgn (s j) *
        ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k))
      ≤ (2 * Real.exp 1 * (k : ℝ) * U) ^ k := by
  refine (avg_pow_le _ hk).trans (pow_le_pow_left₀ (by positivity) ?_ k)
  exact mul_le_mul_of_nonneg_left (sum_bilin_sq_le hL hw hU i) (by positivity)

/-- Averaging distributes over a finite sum. -/
theorem avg_sum {ν : Type*} (s : Finset ν) (F : ν → (ι → Bool) → ℝ) :
    avg (fun σ => ∑ i ∈ s, F i σ) = ∑ i ∈ s, avg (F i) := by
  simp only [avg]
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

/-- **`momBound` right-hand side.**  Summing the per-row moment bound over the `n`
rows: `𝔼_σ[∑ᵢ (row i's process)^{2k}] ≤ n · (2 e k U)^k`.  This is the finite
quantity that `lewlinf` (projection + ℓ₁/ℓ∞ duality) upper-bounds the full
Rademacher process `(max_{‖Ax‖₁=1} ∑ σ aᵢᵀx)^{2k}` by. -/
theorem avg_sum_row_pow_le (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) {k : ℕ} (hk : 1 ≤ k) :
    avg (fun s => ∑ i, (∑ j, Sgn (s j) *
        ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k))
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k := by
  rw [avg_sum]
  calc ∑ i, avg (fun s => (∑ j, Sgn (s j) *
          ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k))
      ≤ ∑ _i : ι, (2 * Real.exp 1 * (k : ℝ) * U) ^ k :=
        Finset.sum_le_sum fun i _ => avg_row_pow_le hL hw hU hk i
    _ = (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Arlib.Approximation.LewisWeights
