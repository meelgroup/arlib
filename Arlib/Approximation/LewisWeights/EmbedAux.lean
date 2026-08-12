/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Geometry of the ℓ₁ functionals in the Lewis metric

The all-query subspace-embedding argument compares two ℓ₁ seminorms of the query:

* `g y = ‖A y‖₁ = ∑ⱼ |aⱼ ⬝ᵥ y|`   — the exact functional `(WPS.exact ι a).E y`;
* `f y = ∑ₖ cₖ |a_{ωₖ} ⬝ᵥ y|`      — the sampled functional `(sampledWPS … ω).E y`.

Both are controlled, above and below, by the **Lewis quadratic form**
`Q y = yᵀ M y` (`Mq (gram w a) y`), and both are Lipschitz in the Lewis metric
`√Q`.  Precisely, with `d = Fintype.card d` and `M = gram w a`:

    √(Q y) ≤ g y ≤ d · √(Q y),          f y ≤ d · √(Q y),
    |g y − g y'| ≤ d · √(Q (y − y')),   |f y − f y'| ≤ d · √(Q (y − y')).

The lower bound is `sqrt_quad_le_L1`; the upper bounds are the ℓ₁ sensitivity
bound `abs_dot_le_lewis_sqrt_quad` summed, the total mass collapsing to `∑ wᵢ = d`
by the trace identity `sum_lewis_eq_card`.  The Lipschitz bounds are the upper
bounds applied to `y − y'` through subadditivity of a seminorm.

These are the only facts about `f` and `g` the sup-bridge uses; they are collected
here, free of any probability.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Sensitivity
import Arlib.Approximation.LewisWeights.Trace
import Arlib.Approximation.LewisWeights.MNet
import Arlib.Approximation.LewisWeights.Sampler

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## The bridge between `dot` and `⬝ᵥ` -/

omit [DecidableEq d] in
/-- `WPS.E` is phrased with `dot y v = ∑ y·v`; the Lewis lemmas with `v ⬝ᵥ y`.
They agree. -/
theorem dot_eq_dotProduct (y v : d → ℝ) : dot y v = v ⬝ᵥ y := by
  rw [dot_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] [DecidableEq d] in
/-- The exact functional as a sum of `⬝ᵥ` tests. -/
theorem E_exact_dotProduct (y : d → ℝ) :
    (WPS.exact ι a).E y = ∑ j, |a j ⬝ᵥ y| := by
  rw [WPS.E_exact]
  exact Finset.sum_congr rfl fun j _ => by rw [dot_eq_dotProduct]

/-! ## `Q` abbreviation -/

omit [DecidableEq ι] [DecidableEq d] in
/-- The Lewis quadratic form `Q y = yᵀ M y`, `M = gram w a`; definitionally
`Mq (gram w a) y`. -/
theorem Mq_gram (y : d → ℝ) : Mq (gram w a) y = y ⬝ᵥ (gram w a *ᵥ y) := rfl

/-! ## Bounds on the exact functional `g` -/

omit [DecidableEq ι] in
/-- **Lower bound.** `√(Q y) ≤ g y`.  This is `sqrt_quad_le_L1`. -/
theorem sqrt_Mq_le_Eexact (hL : IsLewis w a) (hw : ∀ i, 0 < w i) (y : d → ℝ) :
    Real.sqrt (Mq (gram w a) y) ≤ (WPS.exact ι a).E y := by
  rw [E_exact_dotProduct, Mq_gram]
  exact sqrt_quad_le_L1 hL hw y

omit [DecidableEq ι] in
/-- **Upper bound.** `g y ≤ d · √(Q y)`.  Sum the sensitivity bound
`|aⱼ ⬝ᵥ y| ≤ wⱼ √(Q y)`; the total weight is `∑ wⱼ = d`. -/
theorem Eexact_le_card_sqrt_Mq (hL : IsLewis w a) (hw : ∀ i, 0 < w i) (y : d → ℝ) :
    (WPS.exact ι a).E y ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) y) := by
  rw [E_exact_dotProduct, Mq_gram]
  calc ∑ j, |a j ⬝ᵥ y|
      ≤ ∑ j, w j * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) :=
        Finset.sum_le_sum fun j _ => abs_dot_le_lewis_sqrt_quad hL hw y j
    _ = (∑ j, w j) * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by rw [Finset.sum_mul]
    _ = (Fintype.card d : ℝ) * Real.sqrt (y ⬝ᵥ (gram w a *ᵥ y)) := by
        rw [sum_lewis_eq_card hL hw]

omit [DecidableEq ι] in
/-- **Lipschitz.** `|g y − g y'| ≤ d · √(Q (y − y'))`.  A seminorm is
`1`-Lipschitz for itself; then apply the upper bound to `y − y'`. -/
theorem Eexact_lipschitz (hL : IsLewis w a) (hw : ∀ i, 0 < w i) (y y' : d → ℝ) :
    |(WPS.exact ι a).E y - (WPS.exact ι a).E y'|
      ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) (y - y')) := by
  have hsub : ∀ u v : d → ℝ,
      (WPS.exact ι a).E u ≤ (WPS.exact ι a).E v + (WPS.exact ι a).E (u - v) := by
    intro u v
    rw [E_exact_dotProduct, E_exact_dotProduct, E_exact_dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have : a j ⬝ᵥ u = a j ⬝ᵥ v + a j ⬝ᵥ (u - v) := by
      rw [← dotProduct_add]; congr 1; funext i; simp [Pi.sub_apply]
    rw [this]; exact abs_add_le _ _
  have h1 := hsub y y'
  have h2 := hsub y' y
  have hyx : (WPS.exact ι a).E (y' - y) = (WPS.exact ι a).E (y - y') := by
    rw [E_exact_dotProduct, E_exact_dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a j ⬝ᵥ (y' - y) = -(a j ⬝ᵥ (y - y')) by
      rw [← dotProduct_neg]; congr 1; funext i; simp [Pi.sub_apply], abs_neg]
  rw [hyx] at h2
  have hub := Eexact_le_card_sqrt_Mq hL hw (y - y')
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## Bounds on the sampled functional `f` -/

omit [DecidableEq ι] in
/-- The reweighted sampled mass sums to `∑ wᵢ = d`.  `cₖ · w_{ωₖ} = W/m`, and
there are `m` coordinates. -/
theorem sum_sampled_mass_mul_weight [Nonempty ι] (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) (ω : Fin m → ι) :
    ∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * w (ω k) = ∑ j, w j := by
  have hWpos : 0 < ∑ j, w j := Finset.sum_pos (fun i _ => hw i) ⟨Classical.arbitrary ι, mem_univ _⟩
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hterm : ∀ k : Fin m,
      (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * w (ω k) = (∑ j, w j) / m := by
    intro k
    have hwk : w (ω k) ≠ 0 := (hw (ω k)).ne'
    field_simp
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [DecidableEq ι] in
/-- **Upper bound on the sampled functional.** `f z ≤ d · √(Q z)`.  Sum the
sensitivity bound over the drawn rows; the reweighted mass collapses to
`∑ wᵢ = d`. -/
theorem sampledWPS_le_card_sqrt_Mq [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) (ω : Fin m → ι) (z : d → ℝ) :
    (sampledWPS w hw a m ω).E z ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) z) := by
  rw [sampledWPS_E, Mq_gram]
  have hsqrt_nn : 0 ≤ Real.sqrt (z ⬝ᵥ (gram w a *ᵥ z)) := Real.sqrt_nonneg _
  calc ∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |dot z (a (ω k))|
      = ∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |a (ω k) ⬝ᵥ z| := by
        refine Finset.sum_congr rfl fun k _ => ?_; rw [dot_eq_dotProduct]
    _ ≤ ∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j))))
          * (w (ω k) * Real.sqrt (z ⬝ᵥ (gram w a *ᵥ z))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left (abs_dot_le_lewis_sqrt_quad hL hw z (ω k)) ?_
        exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg m)
          (div_nonneg (hw (ω k)).le (Finset.sum_nonneg fun j _ => (hw j).le)))
    _ = (∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * w (ω k))
          * Real.sqrt (z ⬝ᵥ (gram w a *ᵥ z)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ = (Fintype.card d : ℝ) * Real.sqrt (z ⬝ᵥ (gram w a *ᵥ z)) := by
        rw [sum_sampled_mass_mul_weight hw hm ω, sum_lewis_eq_card hL hw]

omit [DecidableEq ι] in
/-- **Lipschitz.** `|f y − f y'| ≤ d · √(Q (y − y'))`. -/
theorem sampledWPS_lipschitz [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) (ω : Fin m → ι) (y y' : d → ℝ) :
    |(sampledWPS w hw a m ω).E y - (sampledWPS w hw a m ω).E y'|
      ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) (y - y')) := by
  set c : Fin m → ℝ := fun k => 1 / ((m : ℝ) * (w (ω k) / (∑ j, w j))) with hc
  have hcnn : ∀ k, 0 ≤ c k := fun k => one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg m)
    (div_nonneg (hw (ω k)).le (Finset.sum_nonneg fun j _ => (hw j).le)))
  have hsub : ∀ u v : d → ℝ,
      (sampledWPS w hw a m ω).E u
        ≤ (sampledWPS w hw a m ω).E v + (sampledWPS w hw a m ω).E (u - v) := by
    intro u v
    rw [sampledWPS_E, sampledWPS_E, sampledWPS_E, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hdvu : dot u (a (ω k)) = dot v (a (ω k)) + dot (u - v) (a (ω k)) := by
      rw [dot_eq_dotProduct, dot_eq_dotProduct, dot_eq_dotProduct, ← dotProduct_add]
      congr 1; funext i; simp [Pi.sub_apply]
    rw [hdvu, ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (hcnn k)
  have h1 := hsub y y'
  have h2 := hsub y' y
  have hyx : (sampledWPS w hw a m ω).E (y' - y) = (sampledWPS w hw a m ω).E (y - y') := by
    rw [sampledWPS_E, sampledWPS_E]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show dot (y' - y) (a (ω k)) = -(dot (y - y') (a (ω k))) by
      rw [dot_eq_dotProduct, dot_eq_dotProduct, ← dotProduct_neg]
      congr 1; funext i; simp [Pi.sub_apply], abs_neg]
  rw [hyx] at h2
  have hub := sampledWPS_le_card_sqrt_Mq hL hw hm ω (y - y')
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Arlib.Approximation.LewisWeights
