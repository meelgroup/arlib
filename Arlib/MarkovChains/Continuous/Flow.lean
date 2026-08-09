/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue

/-
# Ergodic flow, cut and conductance on a general state space

`Arlib.MarkovChains.Techniques.Conductance` develops flow, cut and conductance for
`FinChain` — a chain on a `Fintype`. That is enough for spin systems and combinatorial
chains, but not for the geometric random walks (ball walk, hit-and-run) whose state space
is a convex body in `ℝⁿ`. This file starts the measure-theoretic version, over a Markov
kernel on an arbitrary measurable space.

The definitions are the exact analogues, with sums replaced by lower Lebesgue integrals:

  `flow μ κ A B = ∫⁻ x in A, κ x B ∂μ`,   `cut μ κ A = flow μ κ A Aᶜ`,
  `conductance μ κ A = cut μ κ A / μ A`.

Everything is valued in `ℝ≥0∞`, which is what makes the foundational layer painless:
no integrability side conditions, and `flow` is automatically nonnegative. Real-valued
versions, where they are wanted, should be obtained by `toReal` once finiteness is known.

## Scope

This is the bottom of the stack. What sits above it — a Cheeger-type inequality relating
conductance to a spectral gap or a mixing time, and thence the analysis of the ball walk —
is **not** here. The finite-state analogue of the first of those is
`Arlib.MarkovChains.Techniques.Conductance.spectralGap_le_conductance`; porting it is the
natural next step and is not attempted in this file.

## Main definitions

* `Arlib.Kernel.flow` — the ergodic flow from `A` to `B`.
* `Arlib.Kernel.cut` — the flow out of `A`.
* `Arlib.Kernel.conductance` — the cut normalised by the mass of `A`.

## Main results

* `Arlib.Kernel.flow_add_flow_compl` — `flow A B + flow A Bᶜ = μ A`, the conservation law
  every later identity rests on.
* `Arlib.Kernel.cut_add_flow_self` — `cut A + flow A A = μ A`.
* `Arlib.Kernel.cut_le` — the cut never exceeds the mass it cuts.
* `Arlib.Kernel.conductance_le_one`.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **ergodic flow** from `A` to `B`: the `μ`-mass of one step of `κ` that starts in
`A` and lands in `B`,

  `flow μ κ A B = ∫⁻ x in A, κ x B ∂μ`.

The general-state-space analogue of `Arlib.flow`, with the double sum replaced by a lower
Lebesgue integral. -/
noncomputable def flow (μ : Measure Ω) (κ : Kernel Ω Ω) (A B : Set Ω) : ℝ≥0∞ :=
  ∫⁻ x in A, κ x B ∂μ

theorem flow_apply (μ : Measure Ω) (κ : Kernel Ω Ω) (A B : Set Ω) :
    flow μ κ A B = ∫⁻ x in A, κ x B ∂μ := rfl

/-- No flow out of the empty set. -/
@[simp] theorem flow_empty_left (μ : Measure Ω) (κ : Kernel Ω Ω) (B : Set Ω) :
    flow μ κ ∅ B = 0 := by
  simp [flow]

/-- No flow into the empty set. -/
@[simp] theorem flow_empty_right (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) :
    flow μ κ A ∅ = 0 := by
  simp [flow]

/-- Flow is monotone in its target. -/
theorem flow_mono_right (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) {B C : Set Ω}
    (h : B ⊆ C) : flow μ κ A B ≤ flow μ κ A C :=
  lintegral_mono fun _ => measure_mono h

/-- **All the mass leaves.** For a Markov kernel the flow from `A` into the whole space is
just the mass of `A`. -/
theorem flow_univ_right (μ : Measure Ω) (κ : Kernel Ω Ω) [IsMarkovKernel κ] (A : Set Ω) :
    flow μ κ A Set.univ = μ A := by
  simp [flow, measure_univ]

/-- **The conservation law.** A step out of `A` lands either in `B` or outside it, so the
two flows add up to the mass of `A`.

Every later identity — `cut_add_flow_self`, `cut_le`, `conductance_le_one` — is a
consequence of this. -/
theorem flow_add_flow_compl (μ : Measure Ω) (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    flow μ κ A B + flow μ κ A Bᶜ = μ A := by
  rw [flow, flow, ← lintegral_add_left (Kernel.measurable_coe κ hB)]
  rw [← flow_univ_right μ κ A, flow]
  exact lintegral_congr fun x => measure_add_measure_compl hB

/-- The **cut** across `A`: the flow that escapes `A` in one step. -/
noncomputable def cut (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) : ℝ≥0∞ :=
  flow μ κ A Aᶜ

theorem cut_apply (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) :
    cut μ κ A = flow μ κ A Aᶜ := rfl

/-- **The cut and the flow that stays put partition the mass of `A`.** -/
theorem cut_add_flow_self (μ : Measure Ω) (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    {A : Set Ω} (hA : MeasurableSet A) :
    flow μ κ A A + cut μ κ A = μ A :=
  flow_add_flow_compl μ κ A hA

/-- **The cut never exceeds the mass it cuts.** -/
theorem cut_le (μ : Measure Ω) (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    {A : Set Ω} (hA : MeasurableSet A) : cut μ κ A ≤ μ A := by
  rw [← cut_add_flow_self μ κ hA]
  exact le_add_self

/-- The **conductance** of `A`: the fraction of `A`'s mass that escapes in one step,

  `Φ(A) = cut(A) / μ(A)`.

Lower-bounding this over all `A` of mass at most `1/2` is what drives every mixing-time
argument for a geometric random walk. -/
noncomputable def conductance (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) : ℝ≥0∞ :=
  cut μ κ A / μ A

theorem conductance_apply (μ : Measure Ω) (κ : Kernel Ω Ω) (A : Set Ω) :
    conductance μ κ A = cut μ κ A / μ A := rfl

/-- **Conductance is at most one** — a set cannot lose more than all of its mass. -/
theorem conductance_le_one (μ : Measure Ω) (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    {A : Set Ω} (hA : MeasurableSet A) : conductance μ κ A ≤ 1 :=
  ENNReal.div_le_of_le_mul (by simpa using cut_le μ κ hA)

/-! ## Reversibility -/

/-- **Detailed balance**, in integrated form: the flow from `A` to `B` equals the flow
from `B` to `A`, for all measurable `A, B`.

On a finite state space this is the familiar `μ x · P x y = μ y · P y x` summed over
`A × B`; stating it as an equality of flows avoids needing densities, which a geometric
walk on `ℝⁿ` need not have in convenient form. -/
def Reversible (μ : Measure Ω) (κ : Kernel Ω Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B → flow μ κ A B = flow μ κ B A

/-- **Flow is symmetric for a reversible chain.** -/
theorem Reversible.flow_comm {μ : Measure Ω} {κ : Kernel Ω Ω} (h : Reversible μ κ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    flow μ κ A B = flow μ κ B A := h A B hA hB

/-- **Detailed balance implies stationarity.**

If `μ` is reversible for `κ` then it is invariant: `μ.bind κ = μ`. Taking `B = univ` in
detailed balance turns the flow *into* `A` from everywhere — which is what one step of the
chain puts there — into the flow *out of* `A` to everywhere, and that is just `μ A`.

This is the standard reason detailed balance is worth checking: it is a local, verifiable
condition that certifies the global one. -/
theorem Reversible.invariant {μ : Measure Ω} {κ : Kernel Ω Ω} [IsMarkovKernel κ]
    (h : Reversible μ κ) : _root_.ProbabilityTheory.Kernel.Invariant κ μ := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.measurable κ)]
  have huniv : ∫⁻ x, κ x A ∂μ = flow μ κ Set.univ A := by
    rw [flow, Measure.restrict_univ]
  rw [huniv, h Set.univ A MeasurableSet.univ hA, flow_univ_right]

end Arlib.Kernel
