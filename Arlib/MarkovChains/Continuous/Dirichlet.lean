/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.Flow

/-
# The Dirichlet form on a general state space

`Arlib.MarkovChains.Techniques.Conductance` defines the Dirichlet form of a `FinChain` and
proves `dirichlet_indicator`: the Dirichlet form of the indicator `1_A` is the cut across
`A`. That identity is the hinge of Cheeger's inequality — it is what lets a *variational*
quantity (the spectral gap, an infimum of Rayleigh quotients) be compared with a
*combinatorial* one (the conductance, an infimum of cuts).

This file is the general-state-space analogue, for a Markov kernel:

  `ℰ(f) = ½ ∫∫ (f x − f y)² κ(x,dy) μ(dx)`.

The form is taken in **pair form** as the definition rather than derived from
`⟪f, (I−P)f⟫`. Two payoffs: it is manifestly nonnegative, so it lives in `ℝ≥0∞` alongside
`Arlib.Kernel.flow` with no integrability side conditions; and
`dirichlet_indicator_eq_flow_add` then needs **no stationarity hypothesis**, unlike the
finite version, where the same statement rests on `dirichlet_self_eq_pair`.

## Main definitions

* `Arlib.Kernel.dirichlet` — the Dirichlet form, in pair form.

## Main results

* `Arlib.Kernel.dirichlet_indicator_eq_flow_add` — `ℰ(1_A) = ½(flow A Aᶜ + flow Aᶜ A)`.
* `Arlib.Kernel.dirichlet_indicator` — for a reversible chain, `ℰ(1_A) = cut A`.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **Dirichlet form** of `f`, in pair form:

  `ℰ(f) = ½ ∫∫ (f x − f y)² κ(x,dy) μ(dx)`.

Valued in `ℝ≥0∞` — the integrand is a square, hence nonnegative, so `ENNReal.ofReal`
loses nothing and no integrability hypothesis is needed. -/
noncomputable def dirichlet (μ : Measure Ω) (κ : Kernel Ω Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  (1 / 2) * ∫⁻ x, (∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(κ x)) ∂μ

theorem dirichlet_apply (μ : Measure Ω) (κ : Kernel Ω Ω) (f : Ω → ℝ) :
    dirichlet μ κ f
      = (1 / 2) * ∫⁻ x, (∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(κ x)) ∂μ := rfl

/-- The real-valued indicator of `A`. -/
noncomputable def ind (A : Set Ω) : Ω → ℝ := Set.indicator A (fun _ => (1 : ℝ))

/-- **The inner integral of the pair form, from inside `A`.** The squared difference is
`1` exactly on `Aᶜ`. -/
theorem lintegral_sq_ind_mem {κ : Kernel Ω Ω} {A : Set Ω} (hA : MeasurableSet A)
    {x : Ω} (hx : x ∈ A) :
    ∫⁻ y, ENNReal.ofReal ((ind A x - ind A y) ^ 2) ∂(κ x) = κ x Aᶜ := by
  have hfun : (fun y => ENNReal.ofReal ((ind A x - ind A y) ^ 2))
      = Aᶜ.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_not_mem (by simpa using hy)]
      simp [ind, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_mem (by simpa using hy)]
      simp [ind, Set.indicator_of_mem hx, Set.indicator_of_not_mem hy]
  rw [hfun, lintegral_indicator hA.compl _, setLIntegral_one]

/-- **The inner integral of the pair form, from outside `A`.** The squared difference is
`1` exactly on `A`. -/
theorem lintegral_sq_ind_not_mem {κ : Kernel Ω Ω} {A : Set Ω} (hA : MeasurableSet A)
    {x : Ω} (hx : x ∉ A) :
    ∫⁻ y, ENNReal.ofReal ((ind A x - ind A y) ^ 2) ∂(κ x) = κ x A := by
  have hfun : (fun y => ENNReal.ofReal ((ind A x - ind A y) ^ 2))
      = A.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      simp [ind, Set.indicator_of_not_mem hx, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_not_mem hy]
      simp [ind, Set.indicator_of_not_mem hx, Set.indicator_of_not_mem hy]
  rw [hfun, lintegral_indicator hA _, setLIntegral_one]

/-- **The Dirichlet form of an indicator is the symmetrised cut.**

  `ℰ(1_A) = ½ (flow A Aᶜ + flow Aᶜ A)`.

The pair `(x,y)` contributes exactly when one of the two lies in `A` and the other does
not, and the two ways of doing that are the two flows across the cut.

Unlike the finite-state version, this needs **no stationarity hypothesis** — that
hypothesis is only required there to pass from the inner-product form of the Dirichlet
form to the pair form, and here the pair form *is* the definition. -/
theorem dirichlet_indicator_eq_flow_add (μ : Measure Ω) (κ : Kernel Ω Ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    dirichlet μ κ (ind A) = (1 / 2) * (flow μ κ A Aᶜ + flow μ κ Aᶜ A) := by
  rw [dirichlet_apply]
  congr 1
  rw [← lintegral_add_compl _ hA]
  congr 1
  · refine setLIntegral_congr_fun hA ?_
    filter_upwards with x hx using lintegral_sq_ind_mem hA hx
  · refine setLIntegral_congr_fun hA.compl ?_
    filter_upwards with x hx using lintegral_sq_ind_not_mem hA hx

/-- **The Dirichlet form of an indicator is the cut**, for a reversible chain.

Reversibility is used exactly once, to identify the two flows across the cut. Without it
one still has the symmetrised `dirichlet_indicator_eq_flow_add`.

This is the identity Cheeger's inequality turns on: it equates a Rayleigh-quotient
numerator with a purely combinatorial quantity. -/
theorem dirichlet_indicator {μ : Measure Ω} {κ : Kernel Ω Ω} (h : Reversible μ κ)
    {A : Set Ω} (hA : MeasurableSet A) :
    dirichlet μ κ (ind A) = cut μ κ A := by
  rw [dirichlet_indicator_eq_flow_add μ κ hA, h Aᶜ A hA.compl hA, cut_apply,
    ← two_mul, ← mul_assoc, one_div,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.two_ne_top, one_mul]

end Arlib.Kernel
