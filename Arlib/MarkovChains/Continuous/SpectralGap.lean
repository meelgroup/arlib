/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.Dirichlet

/-
# Spectral gap and the easy direction of Cheeger's inequality, on a general state space

The continuous analogue of the second half of
`Arlib.MarkovChains.Techniques.Conductance`: the Poincaré inequality, and the fact that a
bottleneck caps the spectral gap.

## Variance without subtraction

The finite development writes `Var f = ⟪f,f⟫ − (E f)²`. That is unusable in `ℝ≥0∞`, where
subtraction is truncated. The fix is the **pair form**

  `Var f = ½ ∫∫ (f x − f y)² μ(dx) μ(dy)`,

which agrees with the usual variance for a probability measure and is manifestly
nonnegative. It is also literally `Arlib.Kernel.dirichlet` for the *constant* kernel — the
chain that forgets its position and redraws from `μ` — so `Arlib.Kernel.variancePair` is
defined that way and inherits `dirichlet_indicator_eq_flow_add` for free.

The payoff shows up in `Arlib.Kernel.variancePair_ind`: the variance of an indicator is
`μ A · μ Aᶜ`, with no `1 − μ A` anywhere.

## Scope

Only the **easy** direction of Cheeger is here — a bottleneck caps the gap. The hard
direction (a small gap forces a small cut) is not proved, exactly as in the finite module.
Neither is any mixing-time bound: converting a spectral gap into a bound on total variation
distance is the next module, and is not attempted here.

## Main results

* `Arlib.Kernel.variancePair_ind` — `Var(1_A) = μ A · μ Aᶜ`.
* `Arlib.Kernel.spectralGap_mul_le_cut` — the Poincaré inequality read at `1_A`.
* `Arlib.Kernel.spectralGap_le_conductance` — `γ ≤ 2 Φ(A)` for `μ A ≤ ½`.
* `Arlib.Kernel.not_spectralGapAtLeast_of_lt` — the slow-mixing shape.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **variance** of `f` under `μ`, in pair form:

  `Var f = ½ ∫∫ (f x − f y)² μ(dx) μ(dy)`.

Equal to the Dirichlet form of the constant kernel, which is how it is defined here. -/
noncomputable def variancePair (μ : Measure Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  dirichlet μ (Kernel.const Ω μ) f

/-- The flow of the constant kernel is a product of masses. -/
theorem flow_const (μ : Measure Ω) (A B : Set Ω) :
    flow μ (Kernel.const Ω μ) A B = μ B * μ A := by
  rw [flow]
  simp [Kernel.const_apply, setLIntegral_const]

/-- **The variance of an indicator is `μ A · μ Aᶜ`.**

The finite statement is `Pr A · (1 − Pr A)`; for a probability measure these agree, but
the form here needs no subtraction and so is well behaved in `ℝ≥0∞`. -/
theorem variancePair_ind (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    variancePair μ (ind A) = μ A * μ Aᶜ := by
  rw [variancePair, dirichlet_indicator_eq_flow_add μ _ hA, flow_const, flow_const]
  rw [show μ Aᶜ * μ A + μ A * μ Aᶜ = 2 * (μ A * μ Aᶜ) by ring]
  rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.two_ne_top, one_mul]

/-- **The Poincaré inequality with constant `γ`**: the Dirichlet form dominates `γ` times
the variance, for every real `f`.

This is the spectral gap in variational form; no eigenvalue appears. -/
def SpectralGapAtLeast (μ : Measure Ω) (κ : Kernel Ω Ω) (γ : ℝ≥0∞) : Prop :=
  ∀ f : Ω → ℝ, γ * variancePair μ f ≤ dirichlet μ κ f

/-- **A bottleneck bounds the gap, un-normalised form.** Reading the Poincaré inequality
at `f = 1_A` gives

  `γ · μ A · μ Aᶜ ≤ cut A`,

with no constraint on `μ A`. This is the form a concrete chain applies. -/
theorem spectralGap_mul_le_cut {μ : Measure Ω} {κ : Kernel Ω Ω} {γ : ℝ≥0∞}
    (hrev : Reversible μ κ) (hgap : SpectralGapAtLeast μ κ γ)
    {A : Set Ω} (hA : MeasurableSet A) :
    γ * (μ A * μ Aᶜ) ≤ cut μ κ A := by
  have h := hgap (ind A)
  rwa [variancePair_ind μ hA, dirichlet_indicator hrev hA] at h

/-- **The easy direction of Cheeger's inequality.** If `κ` is reversible for `μ`, has
spectral gap at least `γ`, and `A` has `0 < μ A ≤ ½`, then

  `γ ≤ 2 Φ(A)`.

A set with small conductance is a bottleneck, and a bottleneck caps the gap.

The proof is the Poincaré inequality at `1_A` together with `μ Aᶜ ≥ ½`; reversibility
enters only through `dirichlet_indicator`. -/
theorem spectralGap_le_conductance {μ : Measure Ω} [IsProbabilityMeasure μ]
    {κ : Kernel Ω Ω} {γ : ℝ≥0∞} (hrev : Reversible μ κ) (hgap : SpectralGapAtLeast μ κ γ)
    {A : Set Ω} (hA : MeasurableSet A) (hpos : μ A ≠ 0) (hhalf : μ A ≤ 1 / 2) :
    γ ≤ 2 * conductance μ κ A := by
  have hne : μ A ≠ ⊤ := measure_ne_top μ A
  -- `μ Aᶜ ≥ 1/2`
  have hcompl : 1 / 2 ≤ μ Aᶜ := by
    rw [prob_compl_eq_one_sub hA]
    refine ENNReal.le_sub_of_add_le_right hne ?_
    calc (1 : ℝ≥0∞) / 2 + μ A ≤ 1 / 2 + 1 / 2 := add_le_add_left hhalf _
      _ = 1 := ENNReal.add_halves 1
  -- half the mass of `A` already meets the Poincaré bound
  have hmul : γ * (μ A / 2) ≤ cut μ κ A := by
    refine le_trans (mul_le_mul_left' ?_ γ) (spectralGap_mul_le_cut hrev hgap hA)
    rw [← mul_one_div]
    exact mul_le_mul_left' hcompl _
  -- rearrange to `γ * μ A ≤ 2 * cut`
  have hgm : γ * μ A ≤ 2 * cut μ κ A := by
    have h1 : γ * μ A / 2 ≤ cut μ κ A := by rwa [mul_div_assoc]
    rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.two_ne_top)] at h1
    rwa [mul_comm (cut μ κ A) 2] at h1
  rw [conductance_apply, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hne)]
  exact hgm

/-- **The slow-mixing shape.** A set of mass at most `½` whose conductance is small enough
that `2 Φ(A) < γ` certifies that the Poincaré inequality fails at `γ`.

This is how a bottleneck is turned into a lower bound on mixing time. -/
theorem not_spectralGapAtLeast_of_lt {μ : Measure Ω} [IsProbabilityMeasure μ]
    {κ : Kernel Ω Ω} {γ : ℝ≥0∞} (hrev : Reversible μ κ)
    {A : Set Ω} (hA : MeasurableSet A) (hpos : μ A ≠ 0) (hhalf : μ A ≤ 1 / 2)
    (hlt : 2 * conductance μ κ A < γ) :
    ¬ SpectralGapAtLeast μ κ γ := fun hgap =>
  absurd (spectralGap_le_conductance hrev hgap hA hpos hhalf) (not_le.mpr hlt)

end Arlib.Kernel
