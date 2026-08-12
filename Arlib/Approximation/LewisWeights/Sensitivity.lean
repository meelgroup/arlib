/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ℓ₁ sensitivity of Lewis weights

The single inequality that makes importance sampling by Lewis weights work: for
ℓ₁ Lewis weights `w`, every row's contribution to any linear test is controlled
by its weight,

`|aᵢ ⬝ᵥ y| ≤ wᵢ · ∑ⱼ |aⱼ ⬝ᵥ y|`   (`abs_dot_le_lewis_L1`).

That is, `wᵢ` bounds the **ℓ₁ sensitivity** `sup_y |aᵢ·y| / ‖Ay‖₁` of row `i`.
Consequently, when a reduced set samples row `i` with probability `∝ wᵢ`, the
reweighted term `(1/pᵢ)|aᵢ·y|` is uniformly bounded by `(∑w)·‖Ay‖₁` — the bounded
increments a concentration bound needs.

The proof is Cauchy–Schwarz for the Lewis Gram form (`gram_form_cs`) plus the
self-bounding step `√(yᵀMy) ≤ ‖Ay‖₁`.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Existence

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

omit [DecidableEq ι] in
/-- `|aᵢ·y| ≤ wᵢ · √(yᵀ M y)`, Cauchy–Schwarz against the Lewis Gram form with
`u = M⁻¹aᵢ` (so `⟨u,y⟩_M = aᵢ·y` and `⟨u,u⟩_M = levᵢ = wᵢ²`). -/
theorem abs_dot_le_lewis_sqrt_quad (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    (y : d → ℝ) (i : ι) :
    |a i ⬝ᵥ y| ≤ w i * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by
  have hwr : ∀ j, 0 ≤ (w j)⁻¹ := fun j => (inv_pos.mpr (hw j)).le
  have hcs := gram_form_cs w a hwr ((gram w a)⁻¹ *ᵥ a i) y
  have hL1 : ((gram w a)⁻¹ *ᵥ a i) ⬝ᵥ (gram w a *ᵥ y) = a i ⬝ᵥ y := by
    rw [gram_symm w a ((gram w a)⁻¹ *ᵥ a i) y, gram_mulVec_inv hL.1 i, dotProduct_comm]
  have hR1 : ((gram w a)⁻¹ *ᵥ a i) ⬝ᵥ (gram w a *ᵥ ((gram w a)⁻¹ *ᵥ a i)) = (w i) ^ 2 := by
    rw [gram_mulVec_inv hL.1 i, dotProduct_comm]
    exact hL.2 i
  rw [hL1, hR1] at hcs
  have hQnn : 0 ≤ y ⬝ᵥ (gram w a *ᵥ y) := gram_quad_nonneg w a hwr y
  calc |a i ⬝ᵥ y|
      = Real.sqrt ((a i ⬝ᵥ y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((w i) ^ 2 * (y ⬝ᵥ (gram w a *ᵥ y))) := Real.sqrt_le_sqrt hcs
    _ = w i * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hw i).le]

omit [DecidableEq ι] in
/-- The self-bounding step: `√(yᵀ M y) ≤ ‖Ay‖₁ = ∑ⱼ |aⱼ·y|`. -/
theorem sqrt_quad_le_L1 (hL : IsLewis w a) (hw : ∀ i, 0 < w i) (y : d → ℝ) :
    Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) ≤ ∑ j, |a j ⬝ᵥ y| := by
  have hwr : ∀ j, 0 ≤ (w j)⁻¹ := fun j => (inv_pos.mpr (hw j)).le
  have hQnn : 0 ≤ y ⬝ᵥ (gram w a *ᵥ y) := gram_quad_nonneg w a hwr y
  have hL1nn : 0 ≤ ∑ j, |a j ⬝ᵥ y| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hkey : y ⬝ᵥ (gram w a *ᵥ y)
      ≤ Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) * ∑ j, |a j ⬝ᵥ y| := by
    conv_lhs => rw [dotProduct_gram_mulVec]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hb : (w j)⁻¹ * |a j ⬝ᵥ y| ≤ Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by
      have hA := abs_dot_le_lewis_sqrt_quad hL hw y j
      calc (w j)⁻¹ * |a j ⬝ᵥ y|
          ≤ (w j)⁻¹ * (w j * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y))) :=
            mul_le_mul_of_nonneg_left hA (hwr j)
        _ = Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by
            rw [← mul_assoc, inv_mul_cancel₀ (hw j).ne', one_mul]
    have heq : (w j)⁻¹ * (a j ⬝ᵥ y) * (a j ⬝ᵥ y)
        = ((w j)⁻¹ * |a j ⬝ᵥ y|) * |a j ⬝ᵥ y| := by
      rw [mul_assoc, mul_assoc, abs_mul_abs_self]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  rcases eq_or_lt_of_le hQnn with hQ0 | hQpos
  · rw [← hQ0, Real.sqrt_zero]; exact hL1nn
  · have hsqpos : 0 < Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := Real.sqrt_pos.mpr hQpos
    have hmul : Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y))
        ≤ Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) * ∑ j, |a j ⬝ᵥ y| := by
      rw [Real.mul_self_sqrt hQnn]; exact hkey
    exact le_of_mul_le_mul_left hmul hsqpos

omit [DecidableEq ι] in
/-- **The ℓ₁ sensitivity bound.**  `|aᵢ·y| ≤ wᵢ · ∑ⱼ |aⱼ·y|`: the Lewis weight
`wᵢ` bounds row `i`'s ℓ₁ sensitivity. -/
theorem abs_dot_le_lewis_L1 (hL : IsLewis w a) (hw : ∀ i, 0 < w i) (y : d → ℝ) (i : ι) :
    |a i ⬝ᵥ y| ≤ w i * ∑ j, |a j ⬝ᵥ y| :=
  (abs_dot_le_lewis_sqrt_quad hL hw y i).trans
    (mul_le_mul_of_nonneg_left (sqrt_quad_le_L1 hL hw y) (hw i).le)

end Arlib.Approximation.LewisWeights
