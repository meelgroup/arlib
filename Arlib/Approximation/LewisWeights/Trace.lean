/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.LewisWeights.LinAlg

/-
# The trace identity for ℓ₁ Lewis weights

For ℓ₁ Lewis weights the leverage of each row equals the square of its weight,
`aᵢᵀ M⁻¹ aᵢ = wᵢ²` with `M = gram w a`.  Summing the reweighted leverages gives
the trace of `M⁻¹ M`:

`∑ᵢ wᵢ = ∑ᵢ wᵢ⁻¹ (aᵢᵀ M⁻¹ aᵢ) = tr(M⁻¹ M) = tr(1) = card d`.

So the ℓ₁ Lewis weights always sum to the dimension.

No `sorry`.
-/

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset Matrix

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

omit [Fintype d] [DecidableEq d] in
/-- Entrywise formula for the Gram matrix:
`gram w a q p = ∑ᵢ wᵢ⁻¹ (aᵢ q)(aᵢ p)`. -/
theorem gram_apply (w : ι → ℝ) (a : ι → d → ℝ) (q p : d) :
    gram w a q p = ∑ i, (w i)⁻¹ * (a i q) * (a i p) := by
  unfold gram
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, outer_apply, smul_eq_mul, mul_assoc]

/-- The ℓ₁ Lewis weights sum to the dimension:
`∑ᵢ wᵢ = card d`, via `tr(M⁻¹ M) = tr(1) = d`. -/
theorem sum_lewis_eq_card (hL : IsLewis w a) (hw : ∀ i, 0 < w i) :
    ∑ i, w i = (Fintype.card d : ℝ) := by
  have hPD := hL.1
  have hdet : IsUnit (gram w a).det := isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  -- Step 1: `wᵢ = wᵢ⁻¹ (aᵢᵀ M⁻¹ aᵢ)`.
  have step1 : ∀ i, w i = (w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) := by
    intro i
    have hlev : a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i) = (w i) ^ 2 := by
      have := hL.2 i; rwa [lev] at this
    rw [hlev, pow_two, ← mul_assoc, inv_mul_cancel₀ (hw i).ne', one_mul]
  -- Step 2: open the quadratic form as a double sum.
  have quad : ∀ i, a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)
      = ∑ p, ∑ q, (gram w a)⁻¹ p q * a i q * a i p := by
    intro i
    rw [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  calc ∑ i, w i
      = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) :=
        Finset.sum_congr rfl fun i _ => step1 i
    _ = ∑ i, ∑ p, ∑ q, (gram w a)⁻¹ p q * (w i)⁻¹ * a i q * a i p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [quad i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ p, ∑ q, ∑ i, (gram w a)⁻¹ p q * (w i)⁻¹ * a i q * a i p := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ q, (gram w a)⁻¹ p q * gram w a q p := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [gram_apply w a q p, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ p, ((gram w a)⁻¹ * gram w a) p p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.mul_apply]
    _ = Matrix.trace ((gram w a)⁻¹ * gram w a) := rfl
    _ = Matrix.trace (1 : Matrix d d ℝ) := by rw [Matrix.nonsing_inv_mul _ hdet]
    _ = (Fintype.card d : ℝ) := Matrix.trace_one

end Arlib.Approximation.LewisWeights
