/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Arlib.MarkovChains.Continuous.TotalVariation

/-
# Data processing for a Markov kernel

`Arlib.MarkovChains.Continuous.TotalVariation` proves the *deterministic* data-processing
inequality `Arlib.Kernel.TVLe.map`: pushing two measures forward along a measurable map
cannot increase their total variation distance. It leaves the randomised version — running
both measures one step through the same Markov kernel — explicitly unproved, because that
one is not bookkeeping. This file supplies it.

## Why it is not bookkeeping

`TVLe μ ν ε` is a statement about *sets*: `μ S ≤ ν S + ε` for every measurable `S`. But

  `(μ.bind κ) S = ∫⁻ x, κ x S ∂μ`

is a statement about an *integral*, of the function `f x = κ x S`. So the bound has to be
moved past a lower Lebesgue integral, and nothing in the definition of `TVLe` does that.

The move is the layer cake formula. Writing `f` through its level sets,

  `∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | t ≤ f x} dt`,

turns the integral into an integral *of measures of sets*, where the hypothesis applies
directly. The one thing to be careful about is that the naive bound
`μ {t ≤ f} ≤ ν {t ≤ f} + ε` integrated over all of `(0, ∞)` gives `+∞ · ε`, not `+ε`. What
saves it is that `f` is bounded by `1` — a Markov kernel assigns mass at most `1` to any
set — so the level sets are empty for `t > 1` and the slack `ε` is only paid on `(0, 1]`,
which has Lebesgue measure exactly `1`. Hence the `ε` comes out undegraded, which is what
makes the inequality sharp and the statement worth having.

The general form `Arlib.Kernel.TVLe.lintegral_le` is stated for an arbitrary measurable
`f : Ω → ℝ≥0∞` bounded by `1`, since that is where all the content is; the kernel statement
is the special case `f = fun x => κ x S`. Everything is valued in `ℝ≥0∞`, so `ε = ⊤` is
allowed and there are no finiteness side conditions.

## Scope

* Only one step. There is no iterated (see `Continuous.Mixing.TVLe.bind_iterate`, now proved) version `TVLe (μ.bind κ^[n]) (ν.bind κ^[n]) ε` here,
  though it follows from this one by induction; nothing yet needs it.
* No *contraction*: this says the kernel does not **increase** the distance, not that it
  strictly decreases it. Quantifying the decrease is the Dobrushin coefficient, which is
  not defined anywhere in this library.
* Nothing about two *different* kernels, and no bound in terms of a distance between
  kernels.

## Main results

* `Arlib.Kernel.TVLe.lintegral_le` — the analytic core: a set-wise `TVLe` bound passes to
  lower integrals of measurable functions bounded by `1`, with the same `ε`.
* `Arlib.Kernel.TVLe.bind` — **kernel data processing**: `TVLe μ ν ε` implies
  `TVLe (μ.bind κ) (ν.bind κ) ε` for a Markov kernel `κ`. A sampler that is `ε`-close to
  its target stays `ε`-close after another step of the chain.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ ν : Measure Ω} {ε : ℝ≥0∞}

/-- **A set-wise total variation bound passes to lower integrals**, provided the integrand
is bounded by `1`:

  `TVLe μ ν ε → f measurable → f ≤ 1 → ∫⁻ f ∂μ ≤ ∫⁻ f ∂ν + ε`.

This is the analytic content of `Arlib.Kernel.TVLe.bind`; see the module docstring for why
the boundedness hypothesis cannot be dropped from the constant `ε`. -/
theorem TVLe.lintegral_le (h : TVLe μ ν ε) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν + ε := by
  -- The layer cake formula in Mathlib is stated for real-valued functions, so work with
  -- `g = f.toReal`; no information is lost because `f` is bounded, hence finite.
  have hfne : ∀ x, f x ≠ ⊤ := fun x => ne_top_of_le_ne_top one_ne_top (hf1 x)
  set g : Ω → ℝ := fun x => (f x).toReal with hgdef
  have hgm : Measurable g := hf.ennreal_toReal
  have hgnn : ∀ x, 0 ≤ g x := fun _ => ENNReal.toReal_nonneg
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    simpa [hgdef, ENNReal.one_toReal] using
      (ENNReal.toReal_le_toReal (hfne x) one_ne_top).2 (hf1 x)
  have hofReal : ∀ x, ENNReal.ofReal (g x) = f x := fun x => ENNReal.ofReal_toReal (hfne x)
  have hAm : ∀ t : ℝ, MeasurableSet {x | t ≤ g x} := fun _ =>
    measurableSet_le measurable_const hgm
  -- Layer cake: the integral is the integral of the measures of the level sets.
  have cake : ∀ ρ : Measure Ω, ∫⁻ x, f x ∂ρ = ∫⁻ t in Set.Ioi (0 : ℝ), ρ {x | t ≤ g x} := by
    intro ρ
    rw [← lintegral_eq_lintegral_meas_le ρ (Filter.Eventually.of_forall hgnn) hgm.aemeasurable]
    exact lintegral_congr fun x => (hofReal x).symm
  -- The slack function: `ε` on `(0, 1]` and `0` above, since the level sets are empty there.
  set c : ℝ → ℝ≥0∞ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => ε) with hcdef
  have hcm : Measurable c := measurable_const.indicator measurableSet_Ioc
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), μ {x | t ≤ g x} ≤ ν {x | t ≤ g x} + c t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · rw [hcdef, Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
      exact h.left (hAm t)
    · have hempty : {x | t ≤ g x} = (∅ : Set Ω) := by
        ext x
        simpa using lt_of_le_of_lt (hg1 x) (not_le.1 ht1)
      simp [hempty]
  -- The slack integrates to exactly `ε`, because `(0, 1]` has Lebesgue measure one.
  have hc : ∫⁻ t in Set.Ioi (0 : ℝ), c t = ε := by
    rw [hcdef, lintegral_indicator_const measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self]
    simp
  calc ∫⁻ x, f x ∂μ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t ≤ g x} := cake μ
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (ν {x | t ≤ g x} + c t) := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht using hbound t ht
    _ = (∫⁻ t in Set.Ioi (0 : ℝ), ν {x | t ≤ g x}) + ∫⁻ t in Set.Ioi (0 : ℝ), c t :=
        lintegral_add_right _ hcm
    _ = ∫⁻ x, f x ∂ν + ε := by rw [← cake ν, hc]

/-- **Kernel data processing.** Running two measures one step through the same Markov
kernel cannot increase the total variation distance between them:

  `TVLe μ ν ε → TVLe (μ.bind κ) (ν.bind κ) ε`.

This is the randomised counterpart of `Arlib.Kernel.TVLe.map`, and the form a sampler needs:
if the law of the current state is within `ε` of the target, it is still within `ε` after
another step of the chain, however many steps have already been taken. Combined with
`Arlib.Kernel.TVLe.trans` it is what lets a mixing-time bound be stated for one step and
used for many. -/
theorem TVLe.bind {κ : Kernel Ω Ω} [IsMarkovKernel κ] (h : TVLe μ ν ε) :
    TVLe (μ.bind κ) (ν.bind κ) ε := by
  have key : ∀ {ρ σ : Measure Ω}, TVLe ρ σ ε → ∀ S : Set Ω, MeasurableSet S →
      ρ.bind κ S ≤ σ.bind κ S + ε := by
    intro ρ σ hρσ S hS
    rw [Measure.bind_apply hS (Kernel.measurable κ),
      Measure.bind_apply hS (Kernel.measurable κ)]
    exact hρσ.lintegral_le (Kernel.measurable_coe κ hS) fun x => prob_le_one
  exact fun S hS => ⟨key h S hS, key h.symm S hS⟩

end Arlib.Kernel
