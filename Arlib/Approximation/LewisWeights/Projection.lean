/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `w̄⁻¹`-orthogonal projection identities for Route A

Cohen–Peng's concentration argument runs on the `w̄⁻¹`-orthogonal projection onto
the column space of `A`,

`Π = A (AᵀW̄⁻¹A)⁻¹ AᵀW̄⁻¹ = A M⁻¹ AᵀW̄⁻¹`,   `M = gram w a`.

This file records the three purely linear-algebraic identities Route A needs
(§5 batch items 2–3 of `docs/dev/LewisWeights-ROUTE_A_PLAN.md`):

* `gram_mulVec_eq_sum` — `M x` as the weighted outer-product sum `∑ⱼ wⱼ⁻¹(aⱼ·x)aⱼ`.
* `gram_inv_mulVec_gram_mulVec` — `Π` fixes the column space: `M⁻¹ (M x) = x`.
* `projT_apply` — the `i`-th coordinate of `Πᵀσ` is exactly arlib's per-row
  Rademacher process `∑ⱼ σⱼ wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ)`, rewritten as a single dual
  pairing `wᵢ⁻¹ · aᵢ ⬝ᵥ M⁻¹ (∑ⱼ σⱼ aⱼ)` so the sup-bridge (L3) can quote the
  moment bound `Concentration.avg_row_pow_le` verbatim.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Existence
import Arlib.Approximation.LewisWeights.Rademacher

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
  {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## A sum-distribution helper for `mulVec` in its vector argument -/

omit [Fintype ι] [DecidableEq d] in
/-- `mulVec` distributes over a finite sum of vectors (Mathlib has `sum_mulVec`
for the matrix argument but no companion for the vector argument). -/
theorem mulVec_sum_vec (M : Matrix d d ℝ) (s : Finset ι) (v : ι → d → ℝ) :
    M *ᵥ (∑ i ∈ s, v i) = ∑ i ∈ s, M *ᵥ v i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Matrix.mulVec_add, ih]

/-! ## (T1) `gram *ᵥ x` as the weighted outer-product sum -/

omit [DecidableEq ι] [DecidableEq d] in
/-- `gram w a *ᵥ x = ∑ⱼ (wⱼ⁻¹ (aⱼ·x)) • aⱼ`.  (The natural parenthesisation:
`•` binds tighter than `*`, so the scalar `(w j)⁻¹ * (a j ⬝ᵥ x)` must be grouped
before the `• a j`.) -/
theorem gram_mulVec_eq_sum (w : ι → ℝ) (a : ι → d → ℝ) (x : d → ℝ) :
    gram w a *ᵥ x = ∑ j, ((w j)⁻¹ * (a j ⬝ᵥ x)) • a j :=
  gram_mulVec w a x

/-! ## (T2) The projection fixes the column space: `M⁻¹ (M x) = x` -/

omit [DecidableEq ι] in
/-- `(gram w a)⁻¹ *ᵥ (gram w a *ᵥ x) = x`.  Since `Π (A x) = A M⁻¹ AᵀW̄⁻¹ (A x)`
and `AᵀW̄⁻¹ A = M`, this is `M⁻¹ M x = x`, i.e. `Π` fixes the column space. -/
theorem gram_inv_mulVec_gram_mulVec (hL : IsLewis w a) (x : d → ℝ) :
    (gram w a)⁻¹ *ᵥ (gram w a *ᵥ x) = x := by
  have hdet : IsUnit (gram w a).det := isUnit_iff_ne_zero.mpr hL.1.det_pos.ne'
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-! ## (T3) `(Πᵀσ)ᵢ` as a single dual pairing -/

/-- The `i`-th coordinate of `Πᵀσ` is exactly the per-row Rademacher process
bounded by `Concentration.avg_row_pow_le`, and equals the single dual pairing
`wᵢ⁻¹ · aᵢ ⬝ᵥ M⁻¹ (∑ⱼ σⱼ aⱼ)`.

The dual vector is `c σ := ∑ⱼ Sgn(σⱼ) • aⱼ` **without** any `wⱼ⁻¹`: the arlib
process sums `σⱼ · wᵢ⁻¹ (aᵢᵀ M⁻¹ aⱼ)`, and pulling `wᵢ⁻¹` and `M⁻¹` out by
linearity leaves precisely `aᵢᵀ M⁻¹ (∑ⱼ σⱼ aⱼ)`.  (Inserting a `wⱼ⁻¹` into `c`
would not match the left-hand process, which carries no `wⱼ⁻¹`.) -/
theorem projT_apply (s : ι → Bool) (i : ι) :
    (∑ j, Sgn (s j) * ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j))))
      = (w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ (∑ j, Sgn (s j) • a j))) := by
  rw [mulVec_sum_vec, dotProduct_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end Arlib.Approximation.LewisWeights
