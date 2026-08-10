/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Per-query concentration of the Lewis importance-sampling estimator

For a *fixed* query `y`, the sampled functional `(sampledWPS … ω).E y` concentrates
around its mean `‖A y‖₁ = (WPS.exact ι a).E y` exponentially in the sample count:

    Pr[ |Ê(y) − ‖Ay‖₁| ≥ γ · ‖Ay‖₁ ]  ≤  2 · exp(−γ² m / (4 d)).

This is the relative Chernoff bound of `Bernstein.chernoff_relative` instantiated
at the sampler.  The summand of coordinate `k` is
`(W / (m · w_{ωₖ})) · |a_{ωₖ} ⬝ᵥ y|`, which is:

* **nonnegative and bounded** by `b = (W/m) · ‖Ay‖₁`, because the ℓ₁ sensitivity
  bound gives `|aᵢ ⬝ᵥ y| ≤ wᵢ · ‖Ay‖₁` (`abs_dot_le_lewis_L1`);
* has **sum-mean** `‖Ay‖₁` (`estimator_unbiased`).

The exponent then collapses: `γ² μ / (4 b) = γ² ‖Ay‖₁ / (4 (W/m) ‖Ay‖₁) = γ² m / (4 W)`,
and `W = ∑ wᵢ = d` by the trace identity `sum_lewis_eq_card`.  The `d` in the
denominator is the whole reason importance sampling by Lewis weights works: the
per-term bound is uniform once the weights are the Lewis weights.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Bernstein
import Arlib.Approximation.LewisWeights.EmbedAux

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset Arlib

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

/-- **Per-query concentration.**  For a fixed query `y` with `‖Ay‖₁ > 0`, the
Lewis importance-sampling estimator deviates from `‖Ay‖₁` by a factor `γ` with
probability at most `2 · exp(−γ² m / (4 d))`. -/
theorem sampledWPS_conc [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) (y : d → ℝ) (hy : 0 < (WPS.exact ι a).E y)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (sampleSpace w hw m).Pr (Finset.univ.filter (fun ω =>
        γ * (WPS.exact ι a).E y ≤ |(sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y|))
      ≤ 2 * Real.exp (-(γ ^ 2 * (m : ℝ)) / (4 * (Fintype.card d : ℝ))) := by
  set C := sampleCoin w hw m with hC
  set W := ∑ j, w j with hW
  set g := (WPS.exact ι a).E y with hg
  have hWpos : 0 < W := Finset.sum_pos (fun i _ => hw i) ⟨Classical.arbitrary ι, mem_univ _⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the per-coordinate summand
  set gb : (i : C.ι) → C.Coin i → ℝ :=
    fun _ i => (1 / ((m : ℝ) * (w i / W))) * |dot y (a i)| with hgb_def
  set b : ℝ := (W / m) * g with hb
  have hwcne : ∀ c : ι, w c ≠ 0 := fun c => (hw c).ne'
  have hWne : W ≠ 0 := hWpos.ne'
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  -- `S C gb` is exactly the sampled functional
  have hSeq : S C gb = fun ω => (sampledWPS w hw a m ω).E y := by
    funext ω
    rw [sampledWPS_E]; rfl
  -- its mean is `‖Ay‖₁`
  have hμ : C.toFinProb.Ex (S C gb) = g := by
    rw [hSeq]
    exact estimator_unbiased w hw a m hm y
  -- positivity of coin masses
  have hpos : ∀ (i : C.ι) (c : C.Coin i), 0 < C.coinMass i c := by
    intro i c; exact div_pos (hw c) hWpos
  -- `b > 0`
  have hBpos : 0 < b := by rw [hb]; exact mul_pos (div_pos hWpos hmR) hy
  have hcoefpos : ∀ c : ι, 0 < 1 / ((m : ℝ) * (w c / W)) :=
    fun c => div_pos one_pos (mul_pos hmR (div_pos (hw c) hWpos))
  -- summands are nonnegative
  have hg0 : ∀ (i : C.ι) (c : C.Coin i), 0 ≤ gb i c := by
    intro i c
    simp only [hgb_def]
    exact mul_nonneg (hcoefpos c).le (abs_nonneg _)
  -- summands are bounded by `b`
  have hbnd : ∀ (i : C.ι) (c : C.Coin i), gb i c ≤ b := by
    intro i c
    simp only [hgb_def]; rw [hb]
    have hsens : |a c ⬝ᵥ y| ≤ w c * g := by
      rw [hg, E_exact_dotProduct]
      exact abs_dot_le_lewis_L1 hL hw y c
    have hdot : |dot y (a c)| = |a c ⬝ᵥ y| := by rw [dot_eq_dotProduct]
    have hden1 : (0 : ℝ) < (m : ℝ) * (w c / W) := mul_pos hmR (div_pos (hw c) hWpos)
    have hden2 : (0 : ℝ) < (m : ℝ) * w c := mul_pos hmR (hw c)
    have hwcc : w c ≠ 0 := (hw c).ne'
    have hcoef : 1 / ((m : ℝ) * (w c / W)) = W / ((m : ℝ) * w c) := by
      field_simp
    rw [hdot, hcoef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff hden2 hmR]
    nlinarith [mul_nonneg (mul_nonneg hWpos.le hmR.le) (sub_nonneg.mpr hsens),
      hWpos.le, hmR.le, (hw c).le, abs_nonneg (a c ⬝ᵥ y)]
  -- apply the abstract relative Chernoff bound
  have hcher := chernoff_relative C gb hpos hBpos hg0 hbnd γ hγ0 hγ1
  rw [hμ] at hcher
  simp only [hSeq] at hcher
  -- collapse the exponent: `γ² g / (4 b) = γ² m / (4 W) = γ² m / (4 d)`
  have hexp : -(γ ^ 2 * g) / (4 * b) = -(γ ^ 2 * (m : ℝ)) / (4 * (Fintype.card d : ℝ)) := by
    have hWcard : W = (Fintype.card d : ℝ) := by rw [hW]; exact sum_lewis_eq_card hL hw
    rw [hb, ← hWcard]
    have hgne : g ≠ 0 := hy.ne'
    field_simp
    ring
  rw [hexp] at hcher
  exact hcher