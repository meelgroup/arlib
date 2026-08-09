/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.TVKernel
import Arlib.MarkovChains.Continuous.Flow

/-
# Mixing for a Markov kernel on a general state space

`Arlib.MarkovChains.Techniques.TotalVariation` defines `MixesWithin P μ ε t` for a
`FinChain` — a chain on a `Fintype` — as "from every starting state, the law after `t`
steps is within total variation distance `ε` of `μ`". That is the notion every mixing-time
theorem in the finite half of this library concludes with. This file transports it to a
Markov kernel on an arbitrary measurable space, which is what a geometric random walk (ball
walk, hit-and-run, Metropolis on `ℝⁿ`) needs.

Two ingredients make the transport work, and both are already in place. Total variation on a
general space is `Arlib.Kernel.TVLe`, from
`Arlib.MarkovChains.Continuous.TotalVariation` — a *bounded* form, `μ S ≤ ν S + ε` for every
measurable `S`, rather than a supremum. And the data-processing inequality for a kernel is
`Arlib.Kernel.TVLe.bind`, from `Arlib.MarkovChains.Continuous.TVKernel`. The second is what
makes mixing monotone in time: one more step of the chain cannot move the law further from a
measure the chain already fixes.

## The iterated kernel

Mathlib has kernel composition `ProbabilityTheory.Kernel.comp` (`η ∘ₖ κ`), the identity
kernel `ProbabilityTheory.Kernel.id`, associativity, and the unit laws — but no iterate. So
`Arlib.Kernel.iterate κ t` is defined here, by structural recursion on `t`, purely as
`κ ∘ₖ (κ ∘ₖ ⋯)` on top of Mathlib's `comp`; nothing about composition is reproved. Its
`IsMarkovKernel` instance, associativity-shuffling laws (`iterate_succ'`, `iterate_add`) and
the interaction with `MeasureTheory.Measure.bind` come out of Mathlib's `comp_assoc`,
`comp_id`, `id_comp` and `MeasureTheory.Measure.bind_bind`.

## Monotonicity in time, and why it is stated twice

`MixesWithin` quantifies over *all* starting probability measures, so it admits two
independent proofs of monotonicity in `t`, and both are recorded because they say different
things.

* `MixesWithin.succ` and `MixesWithin.mono_time` take the extra step *at the end*: run the
  chain for `t` steps, land within `ε` of `π`, then apply `TVLe.bind`. This needs
  `ProbabilityTheory.Kernel.Invariant κ π`, since the target must not move when the extra
  step is taken. It is the argument the finite `MixesWithin.mono_time` uses, and it is the
  one that generalises to a single fixed starting measure.
* `MixesWithin.mono_time'` takes the extra steps *at the beginning*: the law after `r` extra
  steps is just another starting measure, so the hypothesis applies to it unchanged. This
  needs no invariance at all — it is an artefact of quantifying over every starting measure,
  and it would be unavailable for a Dirac-only definition.

## Scope

**No mixing-time theorem is proved here.** In particular there is **no** conductance ⇒
mixing implication, no Cheeger inequality, no spectral-gap ⇒ mixing bound, and no bound on
`t` of any kind in terms of anything. This file contains only the definition of the iterated
kernel, the definition of `MixesWithin`, and the formal properties those two definitions
have on their own — monotonicity, a triangle bound, and the consequence that a chain which
mixes has an essentially unique invariant probability measure. Everything here is a
consequence of `TVLe.bind` and bookkeeping.

This is the frame such a theorem would land in. `Arlib.Kernel.conductance` is defined in
`Arlib.MarkovChains.Continuous.Flow`; nothing in this library connects it to
`Arlib.Kernel.MixesWithin`, and closing that gap is a genuine piece of mathematics, not a
missing `import`. The finite-state analogues that *are* proved are
`Arlib.MarkovChains.Techniques.Conductance.spectralGap_le_conductance` and
`Arlib.MarkovChains.Techniques.MixingTime.mixesWithin_lazy_of_gap`.

Also absent: no *lower* bound on mixing time, no `t` extracted from `ε` (no mixing-time
function `t_mix(ε)`), no contraction coefficient, and no statement that a mixing chain is
ergodic in any other sense.

## Main definitions

* `Arlib.Kernel.iterate` — `iterate κ t`, the `t`-fold composition of `κ` with itself, built
  from Mathlib's `ProbabilityTheory.Kernel.comp`.
* `Arlib.Kernel.MixesWithin` — `MixesWithin κ π ε t`: from every starting probability
  measure, the law after `t` steps of `κ` is within total variation `ε` of `π`.

## Main results

* `Arlib.Kernel.TVLe.bind_iterate` — data processing for the iterated kernel: `t` steps of
  the same chain cannot increase the distance between two laws. The `t = 1` case is
  `Arlib.Kernel.TVLe.bind`.
* `Arlib.Kernel.MixesWithin.succ`, `Arlib.Kernel.MixesWithin.mono_time` — **monotonicity in
  time** given `ProbabilityTheory.Kernel.Invariant κ π`; the point of the file.
* `Arlib.Kernel.MixesWithin.mono_time'` — monotonicity in time again, with no invariance
  hypothesis; see above.
* `Arlib.Kernel.MixesWithin.mono_eps` — monotonicity in `ε`.
* `Arlib.Kernel.MixesWithin.trans_tvLe` and `Arlib.Kernel.MixesWithin.tvLe_bind` — the
  telescoping bounds: mixing to `π` transfers to any `π'` close to `π`, and any two runs of
  a mixed chain are within `ε + ε` of each other.
* `Arlib.Kernel.MixesWithin.tvLe_of_invariant`,
  `Arlib.Kernel.MixesWithin.eq_of_invariant_of_zero` — a chain that mixes to `π` pins down
  every invariant probability measure to within `ε`, and exactly when `ε = 0`.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {κ : Kernel Ω Ω} {μ ν π π' : Measure Ω} {ε δ : ℝ≥0∞} {t : ℕ}

/-! ## The iterated kernel

Mathlib supplies composition; this section supplies only the iterate. -/

/-- **The `t`-fold composition of a kernel with itself**, `κ^[t]`: one step of `iterate κ t`
is `t` steps of `κ`.

Defined on top of Mathlib's `ProbabilityTheory.Kernel.comp`, with
`ProbabilityTheory.Kernel.id` — the Dirac kernel `x ↦ δ_x` — at `t = 0`, so that the unit
and associativity laws below are immediate from Mathlib's. Mathlib v4.15 has no iterate of
its own.

No notation is introduced: `κ^[t]` is written only in docstrings, as shorthand for
`iterate κ t`. The token `^[ ]` already belongs to `Function.iterate`, and a kernel is a
bundled structure rather than a function, so overloading it would buy nothing but ambiguous
elaboration. -/
noncomputable def iterate (κ : Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | t + 1 => κ ∘ₖ iterate κ t

@[simp] theorem iterate_zero (κ : Kernel Ω Ω) : iterate κ 0 = Kernel.id := rfl

/-- One more step, taken **first**. -/
theorem iterate_succ (κ : Kernel Ω Ω) (t : ℕ) : iterate κ (t + 1) = κ ∘ₖ iterate κ t := rfl

@[simp] theorem iterate_one (κ : Kernel Ω Ω) : iterate κ 1 = κ := by
  rw [iterate_succ, iterate_zero, Kernel.comp_id]

/-- The iterate of a Markov kernel is a Markov kernel: `t` steps of a chain still land
somewhere, with probability one. -/
instance instIsMarkovKernelIterate (κ : Kernel Ω Ω) [IsMarkovKernel κ] (t : ℕ) :
    IsMarkovKernel (iterate κ t) := by
  induction t with
  | zero => rw [iterate_zero]; infer_instance
  | succ n ih => rw [iterate_succ]; exact Kernel.IsMarkovKernel.comp κ (iterate κ n)

/-- One more step, taken **last**. The two ways of peeling a step off agree, by
associativity of composition. -/
theorem iterate_succ' (κ : Kernel Ω Ω) [IsSFiniteKernel κ] (t : ℕ) :
    iterate κ (t + 1) = iterate κ t ∘ₖ κ := by
  induction t with
  | zero => rw [iterate_one, iterate_zero, Kernel.id_comp]
  | succ n ih =>
      calc iterate κ (n + 1 + 1) = κ ∘ₖ iterate κ (n + 1) := iterate_succ κ (n + 1)
        _ = κ ∘ₖ (iterate κ n ∘ₖ κ) := by rw [ih]
        _ = (κ ∘ₖ iterate κ n) ∘ₖ κ := (Kernel.comp_assoc κ (iterate κ n) κ).symm
        _ = iterate κ (n + 1) ∘ₖ κ := by rw [← iterate_succ]

/-- **Steps add.** `κ^[s + t] = κ^[s] ∘ₖ κ^[t]`: run `t` steps, then `s` more. -/
theorem iterate_add (κ : Kernel Ω Ω) [IsSFiniteKernel κ] (s t : ℕ) :
    iterate κ (s + t) = iterate κ s ∘ₖ iterate κ t := by
  induction s with
  | zero => rw [Nat.zero_add, iterate_zero, Kernel.id_comp]
  | succ n ih =>
      rw [show n + 1 + t = (n + t) + 1 by ring, iterate_succ, ih,
        ← Kernel.comp_assoc κ (iterate κ n) (iterate κ t), ← iterate_succ]

/-! ## Pushing a measure through the iterate -/

/-- The identity kernel does nothing to a measure. -/
@[simp] theorem bind_id (μ : Measure Ω) : μ.bind (Kernel.id : Kernel Ω Ω) = μ := by
  have h : ⇑(Kernel.id : Kernel Ω Ω) = Measure.dirac := funext fun a => Kernel.id_apply a
  rw [h, Measure.bind_dirac]

/-- **Composition of kernels is composition of pushforwards.** Running `μ` through `κ` and
then through `η` is running it through `η ∘ₖ κ`. This is Mathlib's
`MeasureTheory.Measure.bind_bind` in kernel notation. -/
theorem bind_comp (μ : Measure Ω) (η κ : Kernel Ω Ω) :
    μ.bind (η ∘ₖ κ) = (μ.bind κ).bind η := by
  have h : ⇑(η ∘ₖ κ) = fun a => (κ a).bind η := rfl
  rw [h, Measure.bind_bind (Kernel.measurable κ) (Kernel.measurable η)]

@[simp] theorem bind_iterate_zero (μ : Measure Ω) (κ : Kernel Ω Ω) :
    μ.bind (iterate κ 0) = μ := by
  rw [iterate_zero, bind_id]

/-- Peel the **last** step off a `t + 1`-step evolution. -/
theorem bind_iterate_succ (μ : Measure Ω) (κ : Kernel Ω Ω) (t : ℕ) :
    μ.bind (iterate κ (t + 1)) = (μ.bind (iterate κ t)).bind κ := by
  rw [iterate_succ, bind_comp]

/-- Peel the **first** step off a `t + 1`-step evolution. -/
theorem bind_iterate_succ' (μ : Measure Ω) (κ : Kernel Ω Ω) [IsSFiniteKernel κ] (t : ℕ) :
    μ.bind (iterate κ (t + 1)) = (μ.bind κ).bind (iterate κ t) := by
  rw [iterate_succ' κ t, bind_comp]

/-- Split a `s + t`-step evolution. -/
theorem bind_iterate_add (μ : Measure Ω) (κ : Kernel Ω Ω) [IsSFiniteKernel κ] (s t : ℕ) :
    μ.bind (iterate κ (s + t)) = (μ.bind (iterate κ t)).bind (iterate κ s) := by
  rw [iterate_add, bind_comp]

/-- **A Markov kernel preserves total mass one.** Needed to feed the law of the chain at an
intermediate time back into `MixesWithin` as a fresh starting measure. -/
theorem isProbabilityMeasure_bind (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Kernel Ω Ω)
    [IsMarkovKernel κ] : IsProbabilityMeasure (μ.bind κ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.measurable κ)]
  simp

/-! ## Invariance along the iterate -/

/-- **An invariant measure is invariant for every iterate.** If one step fixes `π`, so do
`t` steps. -/
theorem bind_iterate_eq_self (hπ : Kernel.Invariant κ π) (t : ℕ) :
    π.bind (iterate κ t) = π := by
  induction t with
  | zero => rw [bind_iterate_zero]
  | succ n ih => rw [bind_iterate_succ, ih, hπ.def]

/-! ## Data processing along the iterate -/

/-- **Iterated data processing.** Running two laws through `t` steps of the same Markov
kernel cannot increase the total variation distance between them.

The `t = 1` case is `Arlib.Kernel.TVLe.bind`, whose proof is the layer-cake argument in
`Arlib.MarkovChains.Continuous.TVKernel`; everything here is induction on top of it. This
is the iterated version that `TVKernel`'s scope section records as absent. -/
theorem TVLe.bind_iterate [IsMarkovKernel κ] (h : TVLe μ ν ε) (t : ℕ) :
    TVLe (μ.bind (iterate κ t)) (ν.bind (iterate κ t)) ε := by
  induction t with
  | zero => rwa [bind_iterate_zero, bind_iterate_zero]
  | succ n ih =>
      rw [bind_iterate_succ, bind_iterate_succ]
      exact ih.bind

/-! ## Mixing -/

/-- **`MixesWithin κ π ε t`**: from *every* starting probability measure `μ`, the law of the
chain after `t` steps,

  `μ.bind κ^[t]`,

is within total variation distance `ε` of `π`.

The general-state-space analogue of `Arlib.MixesWithin`, which quantifies over starting
*states* of a finite chain; here the quantifier ranges over starting *measures*, which on a
space with no distinguished points is the natural form and is what makes the definition
composable — the law at an intermediate time is itself a legitimate starting measure.

Note what is **not** in the definition: no hypothesis that `π` is invariant, and no
hypothesis that `κ` is anything in particular. Invariance of `π` is required only by the
theorems that need it, and is stated there. -/
def MixesWithin (κ : Kernel Ω Ω) (π : Measure Ω) (ε : ℝ≥0∞) (t : ℕ) : Prop :=
  ∀ μ : Measure Ω, IsProbabilityMeasure μ → TVLe (μ.bind (iterate κ t)) π ε

theorem mixesWithin_iff (κ : Kernel Ω Ω) (π : Measure Ω) (ε : ℝ≥0∞) (t : ℕ) :
    MixesWithin κ π ε t ↔
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → TVLe (μ.bind (iterate κ t)) π ε :=
  Iff.rfl

/-- Unfold the definition at one starting measure, with the probability-measure hypothesis
taken from the instance cache. -/
theorem MixesWithin.tvLe (h : MixesWithin κ π ε t) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : TVLe (μ.bind (iterate κ t)) π ε :=
  h μ ‹_›

/-- **Every chain mixes within `⊤`.** The bound is valued in `ℝ≥0∞`, so there is always a
vacuous statement to be made; recorded so that no one mistakes `MixesWithin` alone for
content. -/
@[simp] theorem mixesWithin_top (κ : Kernel Ω Ω) (π : Measure Ω) (t : ℕ) :
    MixesWithin κ π ⊤ t :=
  fun _ _ => tvLe_top _ _

/-- **Mixing at time zero means the chain starts at `π`, from anywhere.** With `ε = 0` this
forces every probability measure to equal `π`, which is only possible on a subsingleton;
the statement is here to make plain that `t = 0` is not vacuous. -/
theorem mixesWithin_zero_iff (κ : Kernel Ω Ω) (π : Measure Ω) (ε : ℝ≥0∞) :
    MixesWithin κ π ε 0 ↔ ∀ μ : Measure Ω, IsProbabilityMeasure μ → TVLe μ π ε := by
  simp [MixesWithin]

/-! ### Monotonicity in the error -/

/-- **A mixing bound may always be weakened.** -/
theorem MixesWithin.mono_eps (h : MixesWithin κ π ε t) (hε : ε ≤ δ) :
    MixesWithin κ π δ t :=
  fun μ hμ => (h μ hμ).mono hε

/-! ### Monotonicity in time

This is where `Arlib.Kernel.TVLe.bind` earns its keep: the extra step is a step of the same
kernel applied to both the current law and to `π`, and `π` does not move. -/

/-- **One more step cannot hurt.** If the chain is `ε`-mixed at time `t` and `π` is
invariant, it is `ε`-mixed at time `t + 1`.

The whole content is `Arlib.Kernel.TVLe.bind`: the law at time `t` is within `ε` of `π`, one
step of `κ` applied to both sides preserves that by data processing, and the right-hand side
is again `π` because `ProbabilityTheory.Kernel.Invariant κ π` says exactly
`π.bind κ = π`. Without invariance the statement is false — an extra step moves `π` too.

For a reversible chain the invariance hypothesis is supplied by
`Arlib.Kernel.Reversible.invariant`. -/
theorem MixesWithin.succ [IsMarkovKernel κ] (hπ : Kernel.Invariant κ π)
    (h : MixesWithin κ π ε t) : MixesWithin κ π ε (t + 1) := by
  intro μ hμ
  rw [bind_iterate_succ]
  have hstep : TVLe ((μ.bind (iterate κ t)).bind κ) (π.bind κ) ε := (h μ hμ).bind
  rwa [hπ.def] at hstep

/-- **Mixing is monotone in time.** An `ε`-mixed chain stays `ε`-mixed at every later time,
by iterating `Arlib.Kernel.MixesWithin.succ`. -/
theorem MixesWithin.mono_time [IsMarkovKernel κ] (hπ : Kernel.Invariant κ π)
    (h : MixesWithin κ π ε t) {t' : ℕ} (htt : t ≤ t') : MixesWithin κ π ε t' := by
  induction t' with
  | zero => rwa [Nat.le_zero.mp htt] at h
  | succ n ih =>
      rcases Nat.lt_or_ge t (n + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).succ hπ
      · rwa [le_antisymm htt hge] at h

/-- **Mixing is monotone in time, without any invariance hypothesis.**

A second, independent proof: put the extra `r` steps at the *front* instead of the back. The
law after `r` steps is again a probability measure, and `MixesWithin` quantifies over every
starting probability measure, so the hypothesis applies to it verbatim.

This is not a strengthening of `Arlib.Kernel.MixesWithin.mono_time` so much as a comment on
the definition: the invariance of `π` is doing no work once the starting measure is
universally quantified. A Dirac-only definition, as in the finite
`Arlib.MixesWithin`, would not admit this argument, and there `mono_time` genuinely
needs stationarity. -/
theorem MixesWithin.mono_time' [IsMarkovKernel κ] (h : MixesWithin κ π ε t) {t' : ℕ}
    (htt : t ≤ t') : MixesWithin κ π ε t' := by
  intro μ hμ
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le htt
  rw [bind_iterate_add]
  have : IsProbabilityMeasure (μ.bind (iterate κ r)) :=
    isProbabilityMeasure_bind (μ := μ) (κ := iterate κ r)
  exact h _ this

/-! ### Telescoping and composition -/

/-- **The target may be moved.** If the chain mixes to `π` and `π` is within `δ` of `π'`,
then the chain mixes to `π'` within `ε + δ`. Errors add, exactly as in
`Arlib.Kernel.TVLe.trans`; this is how a bound proved for an idealised stationary measure
transfers to the measure one actually cares about. -/
theorem MixesWithin.trans_tvLe (h : MixesWithin κ π ε t) (hππ : TVLe π π' δ) :
    MixesWithin κ π' (ε + δ) t :=
  fun μ hμ => (h μ hμ).trans hππ

/-- **Any two runs of a mixed chain agree.** Once the chain is `ε`-mixed, the laws reached
from two different starting measures are within `ε + ε` of each other — the triangle
inequality through `π`.

This is the form in which mixing is used to justify discarding a burn-in: where the sampler
started stops mattering. -/
theorem MixesWithin.tvLe_bind (h : MixesWithin κ π ε t) (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TVLe (μ.bind (iterate κ t)) (ν.bind (iterate κ t)) (ε + ε) :=
  (h.tvLe μ).trans (h.tvLe ν).symm

/-- **Composing a mixing bound with a later one.** If the chain is `ε`-mixed at time `t` and
`δ`-mixed at time `s`, it is `min ε δ`-mixed at time `max t s`: take whichever bound is
better, at a time late enough for both. Immediate from monotonicity in `t` and in `ε`, but
worth recording since combining two separately proved bounds is the common case. -/
theorem MixesWithin.min [IsMarkovKernel κ] (h : MixesWithin κ π ε t)
    {s : ℕ} (h' : MixesWithin κ π δ s) : MixesWithin κ π (min ε δ) (max t s) := by
  rcases le_total ε δ with hle | hle
  · exact (h.mono_time' (le_max_left t s)).mono_eps (le_of_eq (min_eq_left hle).symm)
  · exact (h'.mono_time' (le_max_right t s)).mono_eps (le_of_eq (min_eq_right hle).symm)

/-! ### Consequences for the invariant measure -/

/-- **A mixing chain pins down its invariant measures.** Any invariant probability measure
`π'` is within `ε` of `π`: start the chain *at* `π'`, where it does not move, and apply the
mixing bound to that run. -/
theorem MixesWithin.tvLe_of_invariant (h : MixesWithin κ π ε t) [IsProbabilityMeasure π']
    (hπ' : Kernel.Invariant κ π') : TVLe π' π ε := by
  have := h π' ‹_›
  rwa [bind_iterate_eq_self hπ'] at this

/-- **Exact mixing forces a unique invariant measure.** With `ε = 0` the previous statement
becomes equality, by `Arlib.Kernel.TVLe.eq_of_zero`. -/
theorem MixesWithin.eq_of_invariant_of_zero (h : MixesWithin κ π 0 t)
    [IsProbabilityMeasure π'] (hπ' : Kernel.Invariant κ π') : π' = π :=
  (h.tvLe_of_invariant hπ').eq_of_zero

/-- **The reversible case.** `Arlib.Kernel.Reversible` — detailed balance in integrated form
— supplies the invariance hypothesis of `Arlib.Kernel.MixesWithin.mono_time` via
`Arlib.Kernel.Reversible.invariant`, so a reversible chain's mixing bound is monotone in
time with no separate check of stationarity. This is the intended entry point for a
Metropolis-type sampler, where detailed balance is what one verifies. -/
theorem MixesWithin.mono_time_of_reversible [IsMarkovKernel κ] (hrev : Reversible π κ)
    (h : MixesWithin κ π ε t) {t' : ℕ} (htt : t ≤ t') : MixesWithin κ π ε t' :=
  h.mono_time hrev.invariant htt

end Arlib.Kernel
