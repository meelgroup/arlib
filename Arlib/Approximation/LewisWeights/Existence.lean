/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Existence of ℓ₁ Lewis weights via the Banach fixed-point theorem

For a family of nonzero rows `a : ι → (d → ℝ)` whose span is all of `d → ℝ`
(`hspan`), there exist strictly positive weights `w : ι → ℝ` with
`IsLewis w a`, i.e. the leverage of each row equals the square of its weight.
(Nonzero rows are needed for *strict* positivity: a zero row has leverage `0`,
forcing its weight to `0`; see the note above `exists_isLewis`.)

The construction is the classical iteration: the map
`T u i = ½ log (lev (exp ∘ u) a i)` is a `½`-contraction on the sup-metric of
`ι → ℝ`, and its fixed point exponentiates to the Lewis weights.  The
contraction estimate rests on the sharp (Lipschitz-`1`) stability of
`log ∘ lev` under multiplicative perturbations of the weights.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.LinAlg
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-! ## L1 — positive definiteness of the Gram matrix from spanning rows -/

omit [DecidableEq ι] [DecidableEq d] in
/-- With strictly positive weights and spanning rows the Gram matrix is
positive definite. -/
theorem gram_posDef (w : ι → ℝ) (a : ι → d → ℝ) (hw : ∀ i, 0 < w i)
    (hspan : ∀ x : d → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) :
    (gram w a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_isHermitian w a) fun x hx => ?_
  have hstar : (star x : d → ℝ) = x := by funext i; simp
  rw [hstar, dotProduct_gram_mulVec]
  have hterm : ∀ i, (w i)⁻¹ * (a i ⬝ᵥ x) * (a i ⬝ᵥ x)
      = (w i)⁻¹ * (a i ⬝ᵥ x) ^ 2 := fun i => by rw [sq]; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (w i)⁻¹ * (a i ⬝ᵥ x) ^ 2 :=
    fun i _ => mul_nonneg (inv_nonneg.mpr (hw i).le) (sq_nonneg _)
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) (Ne.symm ?_)
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero
  have hx0 : ∀ i, a i ⬝ᵥ x = 0 := by
    intro i
    have hi := hall i (Finset.mem_univ i)
    have hinv : (w i)⁻¹ ≠ 0 := inv_ne_zero (hw i).ne'
    have hsq : (a i ⬝ᵥ x) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hi with h | h
      · exact absurd h hinv
      · exact h
    exact sq_eq_zero_iff.mp hsq
  exact hx (hspan x hx0)

/-! ## L2 — monotonicity of the quadratic form in the reciprocal weights -/

omit [DecidableEq ι] [DecidableEq d] in
/-- If `(w i)⁻¹ ≤ (v i)⁻¹` pointwise then the Gram quadratic form of `w` is
dominated by that of `v`. -/
theorem gram_quadForm_mono (v w : ι → ℝ) (a : ι → d → ℝ)
    (hle : ∀ i, (w i)⁻¹ ≤ (v i)⁻¹) (x : d → ℝ) :
    x ⬝ᵥ (gram w a *ᵥ x) ≤ x ⬝ᵥ (gram v a *ᵥ x) := by
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (hle i) (mul_self_nonneg _)

/-! ## The symmetry of the Gram bilinear form -/

omit [DecidableEq ι] [DecidableEq d] in
/-- The Gram bilinear form is symmetric. -/
theorem gram_symm (w : ι → ℝ) (a : ι → d → ℝ) (x y : d → ℝ) :
    x ⬝ᵥ (gram w a *ᵥ y) = y ⬝ᵥ (gram w a *ᵥ x) := by
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## L3 — Cauchy–Schwarz for the Gram bilinear form -/

omit [DecidableEq ι] [DecidableEq d] in
/-- Cauchy–Schwarz for the (positive-semidefinite) Gram bilinear form. -/
theorem gram_form_cs (w : ι → ℝ) (a : ι → d → ℝ) (hw : ∀ i, 0 ≤ (w i)⁻¹)
    (u v : d → ℝ) :
    (u ⬝ᵥ (gram w a *ᵥ v)) ^ 2
      ≤ (u ⬝ᵥ (gram w a *ᵥ u)) * (v ⬝ᵥ (gram w a *ᵥ v)) := by
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec, dotProduct_gram_mulVec]
  have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ u))
    (fun i => Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ v))
  have s1 : ∑ i, (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ u)) * (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ v))
      = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ u) * (a i ⬝ᵥ v) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ u)) * (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ v))
        = (Real.sqrt ((w i)⁻¹) * Real.sqrt ((w i)⁻¹)) * ((a i ⬝ᵥ u) * (a i ⬝ᵥ v)) := by ring
      _ = (w i)⁻¹ * (a i ⬝ᵥ u) * (a i ⬝ᵥ v) := by rw [Real.mul_self_sqrt (hw i)]; ring
  have s2 : ∑ i, (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ u)) ^ 2
      = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ u) * (a i ⬝ᵥ u) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ u)) ^ 2
        = (Real.sqrt ((w i)⁻¹)) ^ 2 * (a i ⬝ᵥ u) ^ 2 := by ring
      _ = (w i)⁻¹ * (a i ⬝ᵥ u) * (a i ⬝ᵥ u) := by rw [Real.sq_sqrt (hw i), sq]; ring
  have s3 : ∑ i, (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ v)) ^ 2
      = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ v) * (a i ⬝ᵥ v) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (Real.sqrt ((w i)⁻¹) * (a i ⬝ᵥ v)) ^ 2
        = (Real.sqrt ((w i)⁻¹)) ^ 2 * (a i ⬝ᵥ v) ^ 2 := by ring
      _ = (w i)⁻¹ * (a i ⬝ᵥ v) * (a i ⬝ᵥ v) := by rw [Real.sq_sqrt (hw i), sq]; ring
  rw [s1, s2, s3] at key
  exact key

omit [DecidableEq ι] [DecidableEq d] in
/-- The Gram quadratic form is nonnegative when the reciprocal weights are. -/
theorem gram_quad_nonneg (w : ι → ℝ) (a : ι → d → ℝ) (hw : ∀ i, 0 ≤ (w i)⁻¹)
    (x : d → ℝ) : 0 ≤ x ⬝ᵥ (gram w a *ᵥ x) := by
  rw [dotProduct_gram_mulVec]
  exact Finset.sum_nonneg fun j _ => by
    rw [mul_assoc]; exact mul_nonneg (hw j) (mul_self_nonneg _)

/-! ## L4 — the leverage-ratio bound -/

omit [DecidableEq ι] in
/-- If the Gram quadratic form of `w` is bounded by `α` times that of `v`, then
each leverage of `v` is bounded by `α` times the corresponding leverage of `w`.
This is the key one-sided comparison. -/
theorem lev_ratio (w v : ι → ℝ) (a : ι → d → ℝ)
    (hL_w : (gram w a).PosDef) (hL_v : (gram v a).PosDef)
    (hw : ∀ i, 0 ≤ (w i)⁻¹) (hv : ∀ i, 0 ≤ (v i)⁻¹)
    {α : ℝ} (hα : 0 ≤ α)
    (hmono : ∀ x, x ⬝ᵥ (gram w a *ᵥ x) ≤ α * (x ⬝ᵥ (gram v a *ᵥ x)))
    (i : ι) : lev v a i ≤ α * lev w a i := by
  set z := (gram v a)⁻¹ *ᵥ a i with hzdef
  set p := (gram w a)⁻¹ *ᵥ a i with hpdef
  have hz : gram v a *ᵥ z = a i := gram_mulVec_inv hL_v i
  have hp : gram w a *ᵥ p = a i := gram_mulVec_inv hL_w i
  -- `lev v a i = a i ⬝ᵥ z` and `= z ⬝ᵥ (gram v a *ᵥ z)`
  have hlevv : lev v a i = a i ⬝ᵥ z := by rw [lev, ← hzdef]
  have hlevv' : lev v a i = z ⬝ᵥ (gram v a *ᵥ z) := by
    rw [hlevv, hz, dotProduct_comm]
  have hlevw : lev w a i = a i ⬝ᵥ p := by rw [lev, ← hpdef]
  have hlevw' : lev w a i = p ⬝ᵥ (gram w a *ᵥ p) := by
    rw [hlevw, hp, dotProduct_comm]
  -- `a i ⬝ᵥ z = p ⬝ᵥ (gram w a *ᵥ z)`
  have haiz : a i ⬝ᵥ z = p ⬝ᵥ (gram w a *ᵥ z) := by
    rw [← hp, dotProduct_comm (gram w a *ᵥ p) z, gram_symm w a z p]
  -- Cauchy–Schwarz at `w`
  have hcs : (a i ⬝ᵥ z) ^ 2 ≤ lev w a i * (z ⬝ᵥ (gram w a *ᵥ z)) := by
    rw [haiz, hlevw']
    exact gram_form_cs w a hw p z
  -- domination of the `w`-form by `α ·` the `v`-form
  have hdom : z ⬝ᵥ (gram w a *ᵥ z) ≤ α * lev v a i := by
    rw [hlevv']; exact hmono z
  -- nonnegativity
  have hLnn : 0 ≤ lev v a i := by rw [hlevv']; exact gram_quad_nonneg v a hv z
  have hWnn : 0 ≤ lev w a i := by rw [hlevw']; exact gram_quad_nonneg w a hw p
  -- assemble `(lev v)^2 ≤ (α · lev w) · lev v`
  have hchain : (lev v a i) ^ 2 ≤ (α * lev w a i) * lev v a i := by
    calc (lev v a i) ^ 2 = (a i ⬝ᵥ z) ^ 2 := by rw [hlevv]
      _ ≤ lev w a i * (z ⬝ᵥ (gram w a *ᵥ z)) := hcs
      _ ≤ lev w a i * (α * lev v a i) := mul_le_mul_of_nonneg_left hdom hWnn
      _ = (α * lev w a i) * lev v a i := by ring
  rcases eq_or_lt_of_le hLnn with hL0 | hLpos
  · rw [← hL0]; exact mul_nonneg hα hWnn
  · have : lev v a i * lev v a i ≤ (α * lev w a i) * lev v a i := by
      rw [← sq]; exact hchain
    exact le_of_mul_le_mul_right this hLpos

omit [DecidableEq ι] [DecidableEq d] in
/-- Scaled monotonicity: if `(w i)⁻¹ ≤ α (v i)⁻¹` pointwise then the Gram
quadratic form of `w` is bounded by `α` times that of `v`. -/
theorem gram_quadForm_mono_scaled (v w : ι → ℝ) (a : ι → d → ℝ) {α : ℝ}
    (hle : ∀ i, (w i)⁻¹ ≤ α * (v i)⁻¹) (x : d → ℝ) :
    x ⬝ᵥ (gram w a *ᵥ x) ≤ α * (x ⬝ᵥ (gram v a *ᵥ x)) := by
  rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hnn : (0 : ℝ) ≤ (a i ⬝ᵥ x) * (a i ⬝ᵥ x) := mul_self_nonneg _
  calc (w i)⁻¹ * (a i ⬝ᵥ x) * (a i ⬝ᵥ x)
      = (w i)⁻¹ * ((a i ⬝ᵥ x) * (a i ⬝ᵥ x)) := by ring
    _ ≤ (α * (v i)⁻¹) * ((a i ⬝ᵥ x) * (a i ⬝ᵥ x)) := mul_le_mul_of_nonneg_right (hle i) hnn
    _ = α * ((v i)⁻¹ * (a i ⬝ᵥ x) * (a i ⬝ᵥ x)) := by ring

omit [DecidableEq ι] in
/-- The leverage is nonnegative. -/
theorem lev_nonneg (w : ι → ℝ) (a : ι → d → ℝ) (hPD : (gram w a).PosDef)
    (hw : ∀ i, 0 ≤ (w i)⁻¹) (i : ι) : 0 ≤ lev w a i := by
  have hz : gram w a *ᵥ ((gram w a)⁻¹ *ᵥ a i) = a i := gram_mulVec_inv hPD i
  have hzeq : lev w a i
      = ((gram w a)⁻¹ *ᵥ a i) ⬝ᵥ (gram w a *ᵥ ((gram w a)⁻¹ *ᵥ a i)) := by
    rw [hz, lev, dotProduct_comm]
  rw [hzeq]
  exact gram_quad_nonneg w a hw _

/-! ## Sharp two-sided leverage stability -/

/-- Elementary log inequality: from `x ≤ eᵗ y` (with `x, y > 0`) deduce
`log x - log y ≤ t`. -/
theorem log_sub_le_of_le_exp_mul {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ Real.exp t * y) : Real.log x - Real.log y ≤ t := by
  have h := Real.log_le_log hx hxy
  rw [Real.log_mul (Real.exp_pos t).ne' hy.ne', Real.log_exp] at h
  linarith

omit [DecidableEq ι] in
/-- **Sharp leverage stability.**  If the log-weights differ by at most `t`
pointwise, then the log-leverages differ by at most `t` pointwise.  This is the
Lipschitz-`1` estimate that drives the contraction. -/
theorem lev_approx (w v : ι → ℝ) (a : ι → d → ℝ)
    (hposw : ∀ i, 0 < w i) (hposv : ∀ i, 0 < v i)
    (hspan : ∀ x : d → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0)
    {t : ℝ} (ht : ∀ i, |Real.log (w i) - Real.log (v i)| ≤ t) (i : ι) :
    |Real.log (lev w a i) - Real.log (lev v a i)| ≤ t := by
  have hPDw := gram_posDef w a hposw hspan
  have hPDv := gram_posDef v a hposv hspan
  have hwr : ∀ j, 0 ≤ (w j)⁻¹ := fun j => (inv_pos.mpr (hposw j)).le
  have hvr : ∀ j, 0 ≤ (v j)⁻¹ := fun j => (inv_pos.mpr (hposv j)).le
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) (ht i)
  -- reciprocal-weight bounds from the log bound
  have hwv : ∀ j, (w j)⁻¹ ≤ Real.exp t * (v j)⁻¹ := by
    intro j
    have habs := abs_le.mp (ht j)
    rw [← Real.exp_log (inv_pos.mpr (hposw j)), ← Real.exp_log (inv_pos.mpr (hposv j)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_inv, Real.log_inv]; linarith [habs.1]
  have hvw : ∀ j, (v j)⁻¹ ≤ Real.exp t * (w j)⁻¹ := by
    intro j
    have habs := abs_le.mp (ht j)
    rw [← Real.exp_log (inv_pos.mpr (hposv j)), ← Real.exp_log (inv_pos.mpr (hposw j)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_inv, Real.log_inv]; linarith [habs.2]
  -- two-sided leverage bounds via L4
  have hlev_vw : lev v a i ≤ Real.exp t * lev w a i :=
    lev_ratio w v a hPDw hPDv hwr hvr (Real.exp_pos t).le
      (fun x => gram_quadForm_mono_scaled v w a hwv x) i
  have hlev_wv : lev w a i ≤ Real.exp t * lev v a i :=
    lev_ratio v w a hPDv hPDw hvr hwr (Real.exp_pos t).le
      (fun x => gram_quadForm_mono_scaled w v a hvw x) i
  have hWnn : 0 ≤ lev w a i := lev_nonneg w a hPDw hwr i
  have hVnn : 0 ≤ lev v a i := lev_nonneg v a hPDv hvr i
  rcases eq_or_lt_of_le hWnn with hW0 | hWpos
  · -- degenerate row: both leverages vanish
    have hwe : lev w a i = 0 := hW0.symm
    have hV0 : lev v a i = 0 := by
      have hle0 : lev v a i ≤ 0 := by rw [hwe, mul_zero] at hlev_vw; exact hlev_vw
      linarith [hVnn]
    rw [hwe, hV0, Real.log_zero, sub_self, abs_zero]; exact ht0
  · -- generic row: both leverages positive, take logs
    have hVpos : 0 < lev v a i := by
      by_contra h
      push Not at h
      have hV0 : lev v a i = 0 := le_antisymm h hVnn
      rw [hV0, mul_zero] at hlev_wv
      exact absurd (lt_of_lt_of_le hWpos hlev_wv) (lt_irrefl 0)
    rw [abs_le]
    refine ⟨?_, log_sub_le_of_le_exp_mul hWpos hVpos hlev_wv⟩
    have := log_sub_le_of_le_exp_mul hVpos hWpos hlev_vw
    linarith

/-! ## The contraction map and its fixed point -/

omit [DecidableEq ι] in
/-- The sharp `½`-contraction estimate for the log-leverage map
`u ↦ ½ log (lev (exp ∘ u) a)` in the sup metric of `ι → ℝ`. -/
theorem lewisMap_dist (a : ι → d → ℝ)
    (hspan : ∀ x : d → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0) (u u' : ι → ℝ) :
    dist (fun i => (1/2) * Real.log (lev (fun j => Real.exp (u j)) a i))
         (fun i => (1/2) * Real.log (lev (fun j => Real.exp (u' j)) a i))
      ≤ (1/2 : ℝ) * dist u u' := by
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hb : ∀ j, |Real.log (Real.exp (u j)) - Real.log (Real.exp (u' j))| ≤ dist u u' := by
    intro j
    rw [Real.log_exp, Real.log_exp, ← Real.dist_eq]
    exact dist_le_pi_dist u u' j
  have hla := lev_approx (fun j => Real.exp (u j)) (fun j => Real.exp (u' j)) a
    (fun j => Real.exp_pos _) (fun j => Real.exp_pos _) hspan hb i
  rw [Real.dist_eq, ← mul_sub, abs_mul, show |(1/2 : ℝ)| = 1/2 by norm_num]
  exact mul_le_mul_of_nonneg_left hla (by norm_num)

/-! ## Existence of the Lewis weights

The strict positivity `∀ i, 0 < w i` demanded by `IsLewis` (via
`lev w a i = (w i)^2`) genuinely requires every row to be nonzero: a zero row
`a i = 0` always has `lev w a i = 0`, which would force `w i = 0`.  Such a zero
row is perfectly compatible with `hspan` (the remaining rows can still span), so
`hspan` alone does **not** suffice for strictly positive weights; the standard
extra hypothesis `hnz : ∀ i, a i ≠ 0` is included.  (With it, the Gram inverse —
which is positive definite — makes each leverage strictly positive.) -/

omit [DecidableEq ι] in
/-- **Existence of ℓ₁ Lewis weights.**  For nonzero rows spanning `d → ℝ`, there
are strictly positive weights whose leverage equals the square of the weight. -/
theorem exists_isLewis (a : ι → d → ℝ)
    (hspan : ∀ x : d → ℝ, (∀ i, a i ⬝ᵥ x = 0) → x = 0)
    (hnz : ∀ i, a i ≠ 0) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ IsLewis w a := by
  classical
  -- the `½`-contraction on log-weight space
  have hCW : ContractingWith (1/2)
      (fun u i => (1/2) * Real.log (lev (fun j => Real.exp (u j)) a i)) := by
    refine ⟨by rw [div_lt_one (by norm_num)]; norm_num,
      LipschitzWith.of_dist_le_mul fun u u' => ?_⟩
    refine (lewisMap_dist a hspan u u').trans_eq ?_
    norm_num
  -- its fixed point
  set u₀ := ContractingWith.fixedPoint _ hCW with hu₀
  have hfix := ContractingWith.fixedPoint_isFixedPt hCW
  rw [← hu₀] at hfix
  have hpt : ∀ i, (1/2) * Real.log (lev (fun j => Real.exp (u₀ j)) a i) = u₀ i :=
    fun i => congrFun hfix i
  -- the candidate weights and their Gram positive definiteness
  have hPD := gram_posDef (fun j => Real.exp (u₀ j)) a (fun i => Real.exp_pos _) hspan
  refine ⟨fun j => Real.exp (u₀ j), fun i => Real.exp_pos _, hPD, fun i => ?_⟩
  set L := lev (fun j => Real.exp (u₀ j)) a i with hL
  have hlog : Real.log L = 2 * u₀ i := by have := hpt i; rw [← hL] at this; linarith
  -- strict positivity of the leverage from positive definiteness of the inverse
  have hpos : 0 < L := by
    have h := Matrix.PosDef.dotProduct_mulVec_pos hPD.inv (hnz i)
    have hstar : (star (a i) : d → ℝ) = a i := by funext k; simp
    rw [hstar] at h
    rw [hL, lev]
    exact h
  calc L = Real.exp (Real.log L) := (Real.exp_log hpos).symm
    _ = Real.exp (2 * u₀ i) := by rw [hlog]
    _ = (Real.exp (u₀ i)) ^ 2 := by rw [two_mul, Real.exp_add, sq]

end Arlib.Approximation.LewisWeights
