/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.Probability.Kernel.Basic

/-
# Total variation distance on a general state space

A sampler for a continuous distribution — a ball walk on a convex body, hit-and-run,
Metropolis on `ℝⁿ` — never returns an exact draw from its target. It returns a draw from
whatever law the chain has reached after finitely many steps. Every downstream statement
about such a sampler is therefore a statement about a measure that is merely *close* to the
target, and "close" has to mean something. Total variation distance is what it means: it is
the unique notion under which a bound on the sampler transfers, with no loss, to a bound on
the probability of **any** measurable event the caller cares about. That transfer is
`Arlib.Kernel.TVLe.measure_le_add`, and it is the reason this file exists.

Mathlib v4.15 has no total variation API for measures — only the Jordan decomposition of a
*signed* measure, from which one could extract `‖μ - ν‖` at the cost of dragging signed
measures through every statement. This file avoids that entirely.

## The bounded form

The distance is not defined. What is defined is the predicate

  `TVLe μ ν ε  ↔  ∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`,

read as "the total variation distance between `μ` and `ν` is at most `ε`". This is the
form every consumer wants — nobody uses the exact distance, they use a bound on it — and
carrying the bound rather than a `sSup` means no supremum bookkeeping: no `le_csSup`
side conditions, no nonemptiness hypotheses, and the metric-space laws below are one-line
consequences of `add_le_add` instead of arguments about suprema.

Everything is valued in `ℝ≥0∞`, consistent with `Arlib.MarkovChains.Continuous.Flow`. In
particular `ε = ⊤` is allowed and is vacuously true (`tvLe_top`), and the triangle
inequality needs no finiteness hypothesis.

Note the convention: with this definition `TVLe μ ν ε` bounds the *unnormalised* quantity
`sup_S |μ S - ν S|`, which for probability measures is the `d_TV` of
`Arlib.MarkovChains.Techniques.TotalVariation`, i.e. **half** the `L¹` distance.

## Scope

This is a foundational layer and deliberately thin. What is **not** proved here:

* No `sSup` definition of the distance itself, and hence no theorem that `TVLe` is
  equivalent to a bound on such a definition. There is nothing deep in this — it is
  omitted because nothing needs it.
* The data-processing inequality for a Markov *kernel* is **now proved**, in
  `Arlib.MarkovChains.Continuous.TVKernel` (`TVLe.bind`). Only the deterministic case
  `TVLe.map` is in this file. The kernel case needs a
  layer-cake argument to move the set-wise bound past a lower integral, which is a genuine
  proof and not attempted.
* No coupling characterisation (TV distance = minimum disagreement probability), no
  Pinsker inequality, and no link to a density or to the Jordan decomposition. The finite
  analogues live in `Arlib.MarkovChains.Techniques.Coupling` and
  `Arlib.MarkovChains.Techniques.Pinsker`.
* No mixing time: nothing here converts a spectral gap or a conductance bound into a
  `TVLe`. That is the theorem this file is the target of, not a theorem it contains.

## Main definitions

* `Arlib.Kernel.TVLe` — `μ` and `ν` are within total variation distance `ε`.

## Main results

* `Arlib.Kernel.TVLe.measure_le_add` — the transfer lemma: a bound on an event under `ν`
  becomes a bound under `μ`, degraded by exactly `ε`. This is the point of the file.
* `Arlib.Kernel.TVLe.refl`, `Arlib.Kernel.TVLe.symm`, `Arlib.Kernel.TVLe.trans`,
  `Arlib.Kernel.TVLe.mono` — the pseudometric laws, `TVLe` being reflexive at `0`,
  symmetric, and satisfying the triangle inequality `ε + δ`.
* `Arlib.Kernel.TVLe.eq_of_zero` — `TVLe μ ν 0` forces `μ = ν`, so the pseudometric
  separates points.
* `Arlib.Kernel.tvLe_of_forall_le` — for probability measures the one-sided bound already
  gives the two-sided one, by complementation.
* `Arlib.Kernel.TVLe.map` — the deterministic data-processing inequality: pushing both
  measures forward along a measurable map cannot increase the distance.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ ν ρ : Measure Ω} {ε ε' δ p : ℝ≥0∞} {S : Set Ω}

/-- **The total variation distance between `μ` and `ν` is at most `ε`**: every measurable
event has almost the same mass under the two measures, with slack `ε`,

  `∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`.

Stated as a bound rather than as an exact distance, because a bound is what every consumer
of a sampler uses and because it avoids a supremum. See the module docstring. -/
def TVLe (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε

theorem tvLe_iff (μ ν : Measure Ω) (ε : ℝ≥0∞) :
    TVLe μ ν ε ↔ ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε := Iff.rfl

/-- The left half of the bound. -/
theorem TVLe.left (h : TVLe μ ν ε) (hS : MeasurableSet S) : μ S ≤ ν S + ε := (h S hS).1

/-- The right half of the bound. -/
theorem TVLe.right (h : TVLe μ ν ε) (hS : MeasurableSet S) : ν S ≤ μ S + ε := (h S hS).2

/-! ## The pseudometric laws -/

/-- **A measure is at distance zero from itself.** -/
@[simp] theorem TVLe.refl (μ : Measure Ω) : TVLe μ μ 0 := by
  intro S _
  simp

/-- **Symmetry.** -/
theorem TVLe.symm (h : TVLe μ ν ε) : TVLe ν μ ε := fun S hS => ⟨(h S hS).2, (h S hS).1⟩

theorem tvLe_comm : TVLe μ ν ε ↔ TVLe ν μ ε := ⟨TVLe.symm, TVLe.symm⟩

/-- **A bound may always be weakened.** -/
theorem TVLe.mono (h : TVLe μ ν ε) (hε : ε ≤ ε') : TVLe μ ν ε' := by
  intro S hS
  exact ⟨(h S hS).1.trans (by gcongr), (h S hS).2.trans (by gcongr)⟩

/-- **Every pair of measures is within distance `⊤`.** The bound is valued in `ℝ≥0∞`, so
there is always a — useless — bound to be had. -/
@[simp] theorem tvLe_top (μ ν : Measure Ω) : TVLe μ ν ⊤ := by
  intro S _
  simp

/-- **The triangle inequality.** Errors add along a chain of approximations: an `ε`-good
sampler for `ν` and a `δ`-good sampler for `ρ` differ by at most `ε + δ`. -/
theorem TVLe.trans (h₁ : TVLe μ ν ε) (h₂ : TVLe ν ρ δ) : TVLe μ ρ (ε + δ) := by
  intro S hS
  obtain ⟨a₁, b₁⟩ := h₁ S hS
  obtain ⟨a₂, b₂⟩ := h₂ S hS
  refine ⟨?_, ?_⟩
  · calc μ S ≤ ν S + ε := a₁
      _ ≤ (ρ S + δ) + ε := by gcongr
      _ = ρ S + (ε + δ) := by ring
  · calc ρ S ≤ ν S + δ := b₂
      _ ≤ (μ S + ε) + δ := by gcongr
      _ = μ S + (ε + δ) := by ring

/-- **The pseudometric separates points**: a sampler with zero error is exact. -/
theorem TVLe.eq_of_zero (h : TVLe μ ν 0) : μ = ν := by
  ext S hS
  obtain ⟨a, b⟩ := h S hS
  rw [add_zero] at a b
  exact le_antisymm a b

theorem tvLe_zero_iff : TVLe μ ν 0 ↔ μ = ν :=
  ⟨TVLe.eq_of_zero, fun h => h ▸ TVLe.refl μ⟩

/-! ## Transferring a bound on an event

The reason the whole notion is worth having: a probability computed for the *target* is
still valid for whatever the sampler actually produced, degraded by exactly the sampler's
error. -/

/-- **Transfer of an upper bound.** If `μ` is within `ε` of `ν` and the event `S` is rare
under `ν`, it is rare under `μ` too, with the probability inflated by `ε`.

This is the lemma a sampler's caller uses: `ν` is the target, `μ` is the law of the
approximate sample, `p` is whatever failure probability the analysis of the target
established. -/
theorem TVLe.measure_le_add (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : ν S ≤ p) :
    μ S ≤ p + ε :=
  (h S hS).1.trans (by gcongr)

/-- **Transfer of a lower bound.** An event that is likely under `ν` cannot be too
unlikely under `μ`. -/
theorem TVLe.le_measure_add (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : p ≤ ν S) :
    p ≤ μ S + ε :=
  hp.trans (h S hS).2

/-- Transfer in the other direction, for convenience: a bound established for `μ` transfers
to `ν`. Just `TVLe.measure_le_add` applied to the symmetric statement. -/
theorem TVLe.measure_le_add' (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : μ S ≤ p) :
    ν S ≤ p + ε :=
  h.symm.measure_le_add hS hp

/-! ## Probability measures -/

/-- **For probability measures one inequality suffices.** Applying the hypothesis to `Sᶜ`
and cancelling the (finite) mass `ν Sᶜ` recovers the reverse bound, so there is no need to
check both directions by hand. -/
theorem tvLe_of_forall_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε) : TVLe μ ν ε := by
  intro S hS
  refine ⟨h S hS, ?_⟩
  have hμ : μ S + μ Sᶜ = 1 := by
    rw [measure_add_measure_compl hS, measure_univ]
  have hν : ν S + ν Sᶜ = 1 := by
    rw [measure_add_measure_compl hS, measure_univ]
  have key : ν S + ν Sᶜ ≤ (μ S + ε) + ν Sᶜ := by
    rw [hν, ← hμ]
    calc μ S + μ Sᶜ ≤ μ S + (ν Sᶜ + ε) := by gcongr; exact h Sᶜ hS.compl
      _ = (μ S + ε) + ν Sᶜ := by ring
  exact ENNReal.le_of_add_le_add_right (measure_ne_top ν Sᶜ) key

/-- The complementary event carries the same bound — immediate, since the definition
already quantifies over all measurable sets, but worth recording so that callers holding a
bound on `S` need not rebuild the measurability of `Sᶜ`. -/
theorem TVLe.compl (h : TVLe μ ν ε) (hS : MeasurableSet S) :
    μ Sᶜ ≤ ν Sᶜ + ε ∧ ν Sᶜ ≤ μ Sᶜ + ε :=
  h Sᶜ hS.compl

/-! ## Data processing, deterministic case -/

/-- **Post-processing cannot increase the distance.** Pushing both measures forward along
a measurable map `f` — reporting `f x` instead of the sample `x` — preserves the bound.

The corresponding statement for a Markov kernel in place of `f` is proved in
`Arlib.MarkovChains.Continuous.TVKernel` as `TVLe.bind`; it is not proved
here; see the module docstring. -/
theorem TVLe.map (h : TVLe μ ν ε) {f : Ω → Ω'} (hf : Measurable f) :
    TVLe (μ.map f) (ν.map f) ε := by
  intro S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  exact h _ (hf hS)

end Arlib.Kernel
