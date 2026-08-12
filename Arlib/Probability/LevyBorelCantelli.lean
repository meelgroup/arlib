/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Lévy–Borel–Cantelli for events adapted one step late

Mathlib has, in `Mathlib/Probability/Martingale/BorelCantelli.lean`:

* `MeasureTheory.ae_mem_limsup_atTop_iff` — **Lévy's generalised Borel–Cantelli**:
  for a filtration `ℱ` and sets `s n` with `s n` measurable w.r.t. `ℱ n`,
  almost surely `ω ∈ limsup s atTop ↔ ∑_{k<n} μ[1_{s (k+1)} | ℱ k] ω → ∞`;
* `MeasureTheory.tendsto_sum_indicator_atTop_iff'` — the same with
  `∑_{k<n} 1_{s (k+1)} ω → ∞` on the left instead of the limsup;

and in `Mathlib/Probability/BorelCantelli.lean`,
`ProbabilityTheory.measure_limsup_eq_one`, the classical **second**
Borel–Cantelli lemma for *independent* sets.

The conditional (Lévy) version is the one that applies to a process whose
successive events are **not** independent — the usual case for a randomized
algorithm, where whether an event occurs at step `t` depends on the whole
history.  But Mathlib's indexing is off by one from the shape such a process
supplies: the event at step `t` is typically decided by randomness drawn *at*
step `t`, hence measurable at `ℱ (t+1)`, while the natural divergence hypothesis
is on the conditional probabilities `μ[1_{E t} | ℱ t]` given the history
*before* it.

This module does that shift once.

## Main statements

* `ae_frequently_of_tendsto_sum_condexp` — events adapted at `t+1` whose
  conditional probabilities given `ℱ t` diverge occur infinitely often a.s.
* `ae_setOf_infinite_of_tendsto_sum_condexp` — the same, as a `Set.Infinite`.
-/
import Mathlib.Probability.Martingale.BorelCantelli

namespace Arlib.Probability

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-- **Lévy–Borel–Cantelli, re-indexed for events adapted one step late.**

Events `E t` with `E t` measurable at time `t+1`, whose conditional
probabilities given the past sum to `∞` almost surely, occur infinitely often
almost surely.

This is `MeasureTheory.ae_mem_limsup_atTop_iff` with the index shifted: that
lemma wants `s n` measurable at `n`, and conditions `s (k+1)` on `ℱ k`, so
taking `s 0 = ∅` and `s (k+1) = E k` turns its hypothesis into ours and its
`limsup s atTop` into `limsup E atTop` (`Filter.limsup_nat_add`), which is
"infinitely often" by `Filter.mem_limsup_iff_frequently_mem`.

Mathematically a restatement; its value is that the shift is done once,
correctly, so that a caller is left with the single estimate
`μ[1_{E t} | ℱ t] ≥ c > 0` to establish. -/
theorem ae_frequently_of_tendsto_sum_condexp {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0} {E : ℕ → Set Ω}
    (hE : ∀ t, MeasurableSet[ℱ (t + 1)] (E t))
    (hdiv : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ∑ t ∈ Finset.range n, (μ[(E t).indicator (1 : Ω → ℝ)|ℱ t]) ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ω ∈ E t := by
  set s : ℕ → Set Ω := fun n => Nat.casesOn n ∅ E with hs
  have hsm : ∀ n, MeasurableSet[ℱ n] (s n) := by
    intro n
    cases n with
    | zero => exact @MeasurableSet.empty Ω (ℱ 0)
    | succ k => exact hE k
  have hshift : limsup E atTop = limsup s atTop := by
    have : (fun i => s (i + 1)) = E := rfl
    rw [← this, limsup_nat_add]
  filter_upwards [MeasureTheory.ae_mem_limsup_atTop_iff μ hsm, hdiv] with ω hω hd
  rw [← mem_limsup_iff_frequently_mem, hshift]
  exact hω.mpr hd

/-- **The same conclusion as a `Set.Infinite`**, which is the form the
divergence criteria of `Arlib.Probability.RobbinsMonro` consume.  The
translation is `Nat.frequently_atTop_iff_infinite`. -/
theorem ae_setOf_infinite_of_tendsto_sum_condexp {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0} {E : ℕ → Set Ω}
    (hE : ∀ t, MeasurableSet[ℱ (t + 1)] (E t))
    (hdiv : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ∑ t ∈ Finset.range n, (μ[(E t).indicator (1 : Ω → ℝ)|ℱ t]) ω) atTop atTop) :
    ∀ᵐ ω ∂μ, {t | ω ∈ E t}.Infinite := by
  filter_upwards [ae_frequently_of_tendsto_sum_condexp hE hdiv] with ω hω
  exact Nat.frequently_atTop_iff_infinite.mp hω

end Arlib.Probability
