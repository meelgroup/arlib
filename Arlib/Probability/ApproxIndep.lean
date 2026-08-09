/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-
# Approximate independence

Two random variables are **`ν`-independent** when every joint event decouples up to an
additive `ν`:

  `|P(X ∈ A, Y ∈ B) − P(X ∈ A)·P(Y ∈ B)| ≤ ν`   for all measurable `A`, `B`.

Equivalently, `ν` bounds the *dependence coefficient*
`sup_{A,B} |P(X∈A,Y∈B) − P(X∈A)P(Y∈B)|`. This file takes the bounded form
(`Arlib.IndepUpTo`) as primitive rather than constructing the supremum: it is the form
consumers actually use, and it avoids `sSup` bookkeeping entirely.

The notion arises whenever a process is *almost* memoryless — for instance when successive
samples come from a Markov chain that has only approximately mixed, so that consecutive
draws are independent only up to the total variation error. Analyses of such samplers need
exactly this: independence is unavailable, but a quantitative surrogate is.

## Main definitions

* `Arlib.IndepUpTo` — `ν`-independence.

## Main results

* `Arlib.IndepUpTo.mono` — a weaker bound still holds.
* `Arlib.IndepUpTo.comp` — measurable functions do not increase dependence.
* `Arlib.indepUpTo_zero_of_indepFun` — genuine independence is `0`-independence, so the
  notion is a strict generalisation and is non-vacuous.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **`ν`-independence**: every joint event decouples up to an additive `ν`.

`ν = 0` is genuine independence (`Arlib.indepUpTo_zero_of_indepFun`); larger `ν` is a
quantitative relaxation. -/
def IndepUpTo (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (ν : ℝ) : Prop :=
  ∀ A : Set α, ∀ B : Set β, MeasurableSet A → MeasurableSet B →
    |(μ (X ⁻¹' A ∩ Y ⁻¹' B)).toReal
      - (μ (X ⁻¹' A)).toReal * (μ (Y ⁻¹' B)).toReal| ≤ ν

/-- A `ν`-independent pair is `ν'`-independent for any larger `ν'`. -/
theorem IndepUpTo.mono {X : Ω → α} {Y : Ω → β} {ν ν' : ℝ}
    (h : IndepUpTo μ X Y ν) (hle : ν ≤ ν') : IndepUpTo μ X Y ν' :=
  fun A B hA hB => le_trans (h A B hA hB) hle

/-- **`ν`-independence is symmetric.** -/
theorem IndepUpTo.symm {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    (h : IndepUpTo μ X Y ν) : IndepUpTo μ Y X ν := by
  intro B A hB hA
  have hset : Y ⁻¹' B ∩ X ⁻¹' A = X ⁻¹' A ∩ Y ⁻¹' B := Set.inter_comm _ _
  rw [hset, mul_comm]
  exact h A B hA hB

/-- **Measurable functions do not increase dependence** — the paper's `lem:fn-indep`.

`μ(f(X), g(Y)) ≤ μ(X, Y)`: post-composing with measurable maps can only merge events, so
the supremum defining the dependence coefficient is taken over a sub-family.

The proof is the observation that `(f ∘ X)⁻¹(A) = X⁻¹(f⁻¹(A))`, so every constraint on the
composed pair is already a constraint on the original pair. -/
theorem IndepUpTo.comp {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (hf : Measurable f) (hg : Measurable g)
    (h : IndepUpTo μ X Y ν) : IndepUpTo μ (f ∘ X) (g ∘ Y) ν := by
  intro A B hA hB
  have hX : (f ∘ X) ⁻¹' A = X ⁻¹' (f ⁻¹' A) := rfl
  have hY : (g ∘ Y) ⁻¹' B = Y ⁻¹' (g ⁻¹' B) := rfl
  rw [hX, hY]
  exact h _ _ (hf hA) (hg hB)

/-- **Genuine independence is `0`-independence.**

Establishes that the notion generalises `ProbabilityTheory.IndepFun` rather than replacing
it, and — since independent pairs exist — that `Arlib.IndepUpTo` is not vacuous. -/
theorem indepUpTo_zero_of_indepFun [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}
    (h : IndepFun X Y μ) : IndepUpTo μ X Y 0 := by
  intro A B hA hB
  have hmul := h.measure_inter_preimage_eq_mul A B hA hB
  rw [hmul, ENNReal.toReal_mul, sub_self, abs_zero]

/-! ## The covariance bound

`lem:cov-bd` of the approximate-independence toolkit: for bounded variables, `ν`-independence
controls the covariance. The proof is a layer-cake argument, and the layer cake is *essential*
— a naive simple-function bound gives `(Σcᵢ)(Σdⱼ)·ν`, which degrades with the number of
pieces. The sharp factor comes from the **nesting** of the level sets `{X > t}`.

Everything is done against a fixed event `B` rather than a second random variable, which is
both more reusable and exactly what the second layer cake will consume.
-/

set_option maxHeartbeats 1000000 in
/-- **The covariance bound against an event** — the core of `lem:cov-bd`.

If `0 ≤ X ≤ a` and every level set of `X` decouples from `B` up to `ν`, then

  `|E(X·1_B) − E(X)·P(B)| ≤ a·ν`.

The `a` is the length of the layer-cake interval `(0, a]`: past `a` the level sets are
empty, so only that range contributes, and on it each layer contributes at most `ν`. -/
theorem abs_setIntegral_sub_mul_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : Set Ω}
    {a ν : ℝ} (hX : Measurable X) (hint : Integrable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXa : ∀ ω, X ω ≤ a) (ha : 0 < a)
    (hdep : ∀ t : ℝ, |(μ ({ω | t < X ω} ∩ B)).toReal
        - (μ {ω | t < X ω}).toReal * (μ B).toReal| ≤ ν) :
    |∫ ω in B, X ω ∂μ - (∫ ω, X ω ∂μ) * (μ B).toReal| ≤ a * ν := by
  classical
  set g₁ : ℝ → ℝ := fun t => (μ ({ω | t < X ω} ∩ B)).toReal with hg₁
  set g₂ : ℝ → ℝ := fun t => (μ {ω | t < X ω}).toReal * (μ B).toReal with hg₂
  set D : ℝ → ℝ := fun _ => ν with hD
  have hm1 : Measurable g₁ := by
    rw [hg₁]
    refine Antitone.measurable ?_
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.inter_subset_inter_left _ fun ω hω => lt_of_le_of_lt hst hω))
  have hm2 : Measurable g₂ := by
    rw [hg₂]
    refine Measurable.mul_const ?_ _
    refine Antitone.measurable ?_
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω hω => lt_of_le_of_lt hst hω)
  -- both vanish past `a`
  have hempty : ∀ t, a ≤ t → {ω | t < X ω} = ∅ := by
    intro t hat; ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact le_trans (hXa ω) hat
  have hv1 : ∀ t, a ≤ t → g₁ t = 0 := by intro t h; simp [hg₁, hempty t h]
  have hv2 : ∀ t, a ≤ t → g₂ t = 0 := by intro t h; simp [hg₂, hempty t h]
  -- domination by `ν · 1_{Ioc 0 a}` on `Ioi 0`
  set bnd : ℝ → ℝ := (Ioc (0:ℝ) a).indicator (fun _ => ν) with hbnd
  have hbnd_int : IntegrableOn bnd (Ioi 0) := by
    refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
    simp [Real.volume_Ioc]
  have hdom : ∀ t ∈ Ioi (0:ℝ), |g₁ t - g₂ t| ≤ bnd t := by
    intro t ht
    rcases le_or_lt t a with hta | hta
    · rw [hbnd, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ht, hta⟩)]; exact hdep t
    · rw [hbnd, Set.indicator_of_not_mem (by simp [Set.mem_Ioc]; intro _; linarith),
        hv1 t hta.le, hv2 t hta.le, sub_zero, abs_zero]
  have hI : IntegrableOn (fun t => g₁ t - g₂ t) (Ioi 0) := by
    refine Integrable.mono' hbnd_int ((hm1.sub hm2).aestronglyMeasurable) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hdom t ht
  set one_bnd : ℝ → ℝ := (Ioc (0:ℝ) a).indicator (fun _ => (1:ℝ)) with hone
  have hone_int : IntegrableOn one_bnd (Ioi 0) := by
    refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
    simp [Real.volume_Ioc]
  have hI1 : IntegrableOn g₁ (Ioi 0) := by
    refine Integrable.mono' hone_int hm1.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rcases le_or_lt t a with hta | hta
    · rw [hone, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ht, hta⟩)]
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    · rw [hone, Set.indicator_of_not_mem (by simp [Set.mem_Ioc]; intro _; linarith),
        hv1 t hta.le]
      simp
  have hI2 : IntegrableOn g₂ (Ioi 0) := by
    have : g₂ = fun t => g₁ t - (g₁ t - g₂ t) := by funext t; ring
    rw [this]; exact hI1.sub hI
  -- assemble
  have h1 : ∫ ω in B, X ω ∂μ = ∫ t in Ioi 0, g₁ t := by
    rw [(hint.restrict (s := B)).integral_eq_integral_meas_lt
      (Filter.Eventually.of_forall hX0)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hg₁]
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hX)]
  have h2 : (∫ ω, X ω ∂μ) * (μ B).toReal = ∫ t in Ioi 0, g₂ t := by
    rw [hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hX0),
      ← integral_mul_right]
  rw [h1, h2, ← integral_sub hI1 hI2]
  calc |∫ t in Ioi 0, (g₁ t - g₂ t)| ≤ ∫ t in Ioi 0, |g₁ t - g₂ t| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Ioi 0))
            (fun t => g₁ t - g₂ t)
    _ ≤ ∫ t in Ioi 0, bnd t := by
        refine integral_mono_of_nonneg (by filter_upwards with t using abs_nonneg _) hbnd_int ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht using hdom t ht
    _ = a * ν := by
        rw [hbnd, integral_indicator measurableSet_Ioc]
        simp [Real.volume_Ioc, ha.le, mul_comm]

/-- **The covariance bound, from `ν`-independence.** Specialises
`Arlib.abs_setIntegral_sub_mul_le` to the level sets of a second variable: if `X` and `Y`
are `ν`-independent and `0 ≤ X ≤ a`, then for every measurable `B'`,

  `|E(X·1_{Y ∈ B'}) − E(X)·P(Y ∈ B')| ≤ a·ν`. -/
theorem IndepUpTo.covariance_bound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → β} {a ν : ℝ} (hX : Measurable X) (hint : Integrable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXa : ∀ ω, X ω ≤ a) (ha : 0 < a)
    (h : IndepUpTo μ X Y ν) {B' : Set β} (hB' : MeasurableSet B') :
    |∫ ω in Y ⁻¹' B', X ω ∂μ - (∫ ω, X ω ∂μ) * (μ (Y ⁻¹' B')).toReal| ≤ a * ν := by
  refine Arlib.abs_setIntegral_sub_mul_le hX hint hX0 hXa ha (fun t => ?_)
  have := h (Set.Ioi t) B' measurableSet_Ioi hB'
  simpa [Set.preimage, Set.mem_Ioi] using this

end Arlib
