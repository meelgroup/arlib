/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Techniques.TotalVariation
import Arlib.MarkovChains.Continuous.TotalVariation

/-
# Bridging the finite and the measure-theoretic total variation distance

Two total variation developments live in this library, on two different kinds of object,
and the first thing anyone needs to know about them is whether they use the same
normalisation. They do. This file records that fact, with proof, and supplies the
translation.

## The two conventions, and the factor relating them

* **Finite.** `Arlib.MarkovChains.tvDist`, defined at
  `Arlib/MarkovChains/Techniques/TotalVariation.lean:143` as

    `tvDist μ ν = (1 / 2) * ∑ x, |μ x - ν x|`,

  i.e. **half** the `L¹` distance between the two mass functions.

* **Measure-theoretic.** `Arlib.Kernel.TVLe`, defined at
  `Arlib/MarkovChains/Continuous/TotalVariation.lean:96` as

    `TVLe μ ν ε ↔ ∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`,

  i.e. a bound on the supremum `sup_S |μ S - ν S|` over measurable events.

**The factor is `1`.** The half in the finite definition is exactly what makes the two
agree: for probability mass functions

  `(1 / 2) * ∑ x, |μ x - ν x| = sup_{A : Finset Ω} (Pr μ A - Pr ν A)`,

the supremum being attained at `A = {x | ν x ≤ μ x}`. That identity is already proved in
the finite file, as `Arlib.MarkovChains.tvDist_eq_Pr_sub`
(`Arlib/MarkovChains/Techniques/TotalVariation.lean:211`) together with
`Arlib.MarkovChains.Pr_sub_le_tvDist` (`:231`), and it is the whole content of the bridge.
Had the finite file used the unhalved `L¹` distance `∑ x, |μ x - ν x|`, every statement
below would carry a `2`; it does not, so none of them do.

Concretely, `tvLe_toMeasure_iff` below reads

  `tvDist μ ν ≤ ε ↔ TVLe (toMeasure μ) (toMeasure ν) (ENNReal.ofReal ε)`,

with the *same* `ε` on both sides and no constant anywhere. It is an `iff`, not merely an
implication, so it also certifies that neither side is the weaker notion: no factor is
being silently absorbed.

## The translation of objects

`TVLe` speaks about `MeasureTheory.Measure`, `tvDist` about `Arlib.MarkovChains.FinDist`.
Nothing in the library previously converted between them, so `Arlib.Kernel.toMeasure` is
introduced here: the finite sum of scaled Dirac measures `∑ x, μ x • δ_x`. It is a
probability measure (`instIsProbabilityMeasureToMeasure`) and its value on a `Finset` is
the finite probability `Pr` (`toMeasure_coe_finset`).

## Main definitions

* `Arlib.Kernel.toMeasure` — the measure `∑ x, μ x • δ_x` attached to a `FinDist` on a
  finite measurable space with measurable singletons.

## Main results

* `Arlib.Kernel.toMeasure_coe_finset`, `Arlib.Kernel.toMeasure_apply` — the measure of a
  set is the finite probability of the corresponding `Finset`.
* `Arlib.Kernel.tvLe_toMeasure` — a `tvDist` bound gives a `TVLe` bound, same `ε`.
* `Arlib.Kernel.tvDist_le_of_tvLe` — and conversely.
* `Arlib.Kernel.tvLe_toMeasure_iff` — the two are equivalent: **the conventions coincide,
  the constant is `1`**.
* `Arlib.Kernel.toMeasure_inj` — `toMeasure` is injective, so nothing is lost in the
  translation.
* `Arlib.Kernel.tvLe_of_mixesWithin` — the consumer-facing form: a finite mixing statement
  `MixesWithin P μ ε t` becomes a `TVLe` bound on the law of the chain, from which
  `TVLe.measure_le_add` transfers event probabilities.

## Scope

Deliberately narrow. What is **not** here:

* No transport of the finite *kernel* to a `ProbabilityTheory.Kernel`, and hence no
  statement that the finite data-processing inequality `tvDist_push_le` implies a
  measure-theoretic one. The measure-theoretic side has no kernel data-processing lemma to
  land in (see the `Scope` section of `Continuous.TotalVariation`), so there is nothing to
  bridge to.
* No converse construction: nothing turns a `Measure` on a finite type back into a
  `FinDist`. It would be routine (`fun x => (μ {x}).toReal`) but nothing needs it.
* No transport of the χ² bound, of couplings, or of Pinsker. Those finite results are
  about objects (`chiSq`, couplings) with no counterpart yet on the measure side.
-/

open Arlib.MarkovChains
open scoped BigOperators ENNReal

namespace Arlib.Kernel

open MeasureTheory Finset

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-! ## From a finite distribution to a measure -/

/-- The measure attached to a distribution on a finite type: the finite sum of scaled point
masses `∑ x, μ x • δ_x`.

This is the only construction in the library that crosses from `FinDist` to `Measure`; the
`ENNReal.ofReal` is harmless because a `FinDist` is nonnegative by definition. -/
noncomputable def toMeasure (μ : FinDist Ω) : Measure Ω :=
  ∑ x : Ω, ENNReal.ofReal (μ x) • Measure.dirac x

/-- **The measure of a `Finset` is its finite probability.** The defining computation:
everything else in this file is an application of it. -/
theorem toMeasure_coe_finset (μ : FinDist Ω) (A : Finset Ω) :
    toMeasure μ (↑A : Set Ω) = ENNReal.ofReal (Pr μ A) := by
  classical
  have hterm : ∀ x : Ω, (ENNReal.ofReal (μ x) • Measure.dirac x) (↑A : Set Ω)
      = if x ∈ A then ENNReal.ofReal (μ x) else 0 := by
    intro x
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (by exact_mod_cast hx)]
      simp [hx]
    · rw [Set.indicator_of_not_mem (by exact_mod_cast hx)]
      simp [hx]
  rw [toMeasure, Measure.finset_sum_apply, Finset.sum_congr rfl fun x _ => hterm x,
    Finset.sum_ite_mem, Finset.univ_inter, Pr_apply,
    ENNReal.ofReal_sum_of_nonneg fun x _ => μ.coe_nonneg x]

/-- Every `FinDist` becomes a probability measure. -/
instance instIsProbabilityMeasureToMeasure (μ : FinDist Ω) :
    IsProbabilityMeasure (toMeasure μ) := by
  constructor
  have h := toMeasure_coe_finset μ (Finset.univ : Finset Ω)
  rwa [Finset.coe_univ, Pr_univ, ENNReal.ofReal_one] at h

open scoped Classical in
/-- The measure of an arbitrary set, in terms of the finite probability of the `Finset` it
cuts out.  On a finite type every set is of this form, so this is `toMeasure_coe_finset`
with no hypotheses left. -/
theorem toMeasure_apply (μ : FinDist Ω) (S : Set Ω) :
    toMeasure μ S = ENNReal.ofReal (Pr μ (Finset.univ.filter (fun x => x ∈ S))) := by
  have hS : S = ↑(Finset.univ.filter (fun x => x ∈ S)) := by ext x; simp
  conv_lhs => rw [hS]
  exact toMeasure_coe_finset μ _

/-- The mass of a singleton is the mass function. -/
@[simp] theorem toMeasure_singleton (μ : FinDist Ω) (x : Ω) :
    toMeasure μ {x} = ENNReal.ofReal (μ x) := by
  classical
  have h := toMeasure_coe_finset μ ({x} : Finset Ω)
  rwa [Finset.coe_singleton, Pr_apply, Finset.sum_singleton] at h

/-! ## The bridge

Both directions, so that the equality of conventions is certified rather than asserted. -/

/-- **A finite total variation bound is a measure-theoretic one, with the same `ε`.**

No constant appears: `tvDist` is already the half-`L¹` distance, which *is* the supremum
of `|μ S - ν S|` that `TVLe` bounds. -/
theorem tvLe_toMeasure {μ ν : FinDist Ω} {ε : ℝ} (h : tvDist μ ν ≤ ε) :
    TVLe (toMeasure μ) (toMeasure ν) (ENNReal.ofReal ε) := by
  classical
  have hε : 0 ≤ ε := le_trans (tvDist_nonneg μ ν) h
  intro S _
  have hS : S = ↑(Finset.univ.filter (fun x => x ∈ S)) := by ext x; simp
  rw [hS, toMeasure_coe_finset, toMeasure_coe_finset]
  set A : Finset Ω := Finset.univ.filter (fun x => x ∈ S) with hA
  have hstep : ∀ ρ σ : FinDist Ω, tvDist ρ σ ≤ ε →
      ENNReal.ofReal (Pr ρ A) ≤ ENNReal.ofReal (Pr σ A) + ENNReal.ofReal ε := by
    intro ρ σ hρσ
    have h1 : Pr ρ A ≤ Pr σ A + ε := by
      have := Pr_sub_le_tvDist ρ σ A
      linarith
    calc ENNReal.ofReal (Pr ρ A) ≤ ENNReal.ofReal (Pr σ A + ε) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (Pr σ A) + ENNReal.ofReal ε :=
          ENNReal.ofReal_add (Pr_nonneg σ A) hε
  exact ⟨hstep μ ν h, hstep ν μ (by rwa [tvDist_comm])⟩

/-- **A measure-theoretic bound is a finite one, with the same `ε`.**

The converse of `tvLe_toMeasure`.  Only the single event `{x | ν x ≤ μ x}` is needed,
because the finite distance is attained there (`tvDist_eq_Pr_sub`). -/
theorem tvDist_le_of_tvLe {μ ν : FinDist Ω} {ε : ℝ} (hε : 0 ≤ ε)
    (h : TVLe (toMeasure μ) (toMeasure ν) (ENNReal.ofReal ε)) : tvDist μ ν ≤ ε := by
  set A : Finset Ω := Finset.univ.filter (fun x => ν x ≤ μ x) with hA
  have h1 := (h (↑A : Set Ω) A.measurableSet).1
  rw [toMeasure_coe_finset, toMeasure_coe_finset,
    ← ENNReal.ofReal_add (Pr_nonneg ν A) hε] at h1
  have h2 : Pr μ A ≤ Pr ν A + ε :=
    (ENNReal.ofReal_le_ofReal_iff (by have := Pr_nonneg ν A; linarith)).mp h1
  rw [tvDist_eq_Pr_sub μ ν, ← hA]
  linarith

/-- **The conventions coincide.**  A `tvDist` bound and a `TVLe` bound on the associated
measures are the *same statement*, with the *same* `ε`: no factor of two is gained or lost
in either direction.

This is the headline of the file.  The `0 ≤ ε` hypothesis is not a normalisation
subtlety — it is only there because `ENNReal.ofReal` truncates negatives, and a negative
`ε` is already impossible on the left by `tvDist_nonneg`. -/
theorem tvLe_toMeasure_iff {μ ν : FinDist Ω} {ε : ℝ} (hε : 0 ≤ ε) :
    tvDist μ ν ≤ ε ↔ TVLe (toMeasure μ) (toMeasure ν) (ENNReal.ofReal ε) :=
  ⟨tvLe_toMeasure, tvDist_le_of_tvLe hε⟩

/-- Nothing is lost in the translation: distinct distributions give distinct measures. -/
theorem toMeasure_inj {μ ν : FinDist Ω} (h : toMeasure μ = toMeasure ν) : μ = ν := by
  refine (tvDist_eq_zero_iff μ ν).mp (le_antisymm ?_ (tvDist_nonneg μ ν))
  refine tvDist_le_of_tvLe le_rfl ?_
  rw [ENNReal.ofReal_zero, h]
  exact TVLe.refl _

theorem toMeasure_injective : Function.Injective (toMeasure : FinDist Ω → Measure Ω) :=
  fun _ _ h => toMeasure_inj h

@[simp] theorem toMeasure_eq_toMeasure_iff {μ ν : FinDist Ω} :
    toMeasure μ = toMeasure ν ↔ μ = ν :=
  ⟨toMeasure_inj, fun h => h ▸ rfl⟩

/-! ## Consequence: finite mixing statements as measure bounds -/

/-- **A finite mixing statement, read as a bound on measures.**  If the chain `P` is
`ε`-mixed towards `μ` after `t` steps, then the law of the chain started at any `x` is
within `TVLe`-distance `ε` of `μ`, as measures.

Composing with `TVLe.measure_le_add` turns this into the statement a sampler's caller
wants: any probability bound proved for the stationary distribution holds for the output of
`t` steps, degraded by exactly `ε`. -/
theorem tvLe_of_mixesWithin [DecidableEq Ω] {P : FinChain Ω} {μ : FinDist Ω} {ε : ℝ} {t : ℕ}
    (h : MixesWithin P μ ε t) (x : Ω) :
    TVLe (toMeasure ((P.iter t).row x)) (toMeasure μ) (ENNReal.ofReal ε) :=
  tvLe_toMeasure (h x)

/-- The transfer lemma, spelled out for a finitely-analysed chain: an event that has
probability at most `p` under the stationary distribution has probability at most `p + ε`
after `t` steps, for any measurable event and any starting state. -/
theorem measure_le_add_of_mixesWithin [DecidableEq Ω] {P : FinChain Ω} {μ : FinDist Ω}
    {ε : ℝ} {t : ℕ} (h : MixesWithin P μ ε t) (x : Ω) {S : Set Ω} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp : toMeasure μ S ≤ p) :
    toMeasure ((P.iter t).row x) S ≤ p + ENNReal.ofReal ε :=
  (tvLe_of_mixesWithin h x).measure_le_add hS hp

end Arlib.Kernel
