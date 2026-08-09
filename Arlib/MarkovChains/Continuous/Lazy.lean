/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpectralGap

/-
# Lazy kernels on a general state space

The **lazy** version of a Markov kernel holds in place with probability `½` and otherwise
takes one step of `κ`:

  `lazy κ x = ½ · δ_x + ½ · κ x`.

This is the measure-theoretic analogue of `Arlib.MarkovChains.FinChain.lazy`, which builds
`½(I + P)` on a finite state space.

## Why laziness

A conductance bound on its own says nothing about mixing: the two-state chain that swaps
deterministically has conductance `1` and never converges, because it is periodic. Laziness
is the standard surgery that removes periodicity — `lazy κ` puts mass `½` on staying put,
so the transition operator can no longer have `-1` in its spectrum — and it is what makes a
Cheeger-type bound convertible into a mixing-time bound at all. Every analysis of a geometric
random walk (ball walk, hit-and-run) is carried out for the lazy chain for exactly this
reason, and pays for it with the factor of two recorded in `cut_lazy` and
`lazy_spectralGapAtLeast` below.

## Main definitions

* `Arlib.Kernel.lazy` — the kernel `x ↦ ½ δ_x + ½ κ x`.

## Main results

* `Arlib.Kernel.isMarkovKernel_lazy` — `lazy κ` is again a Markov kernel.
* `Arlib.Kernel.flow_lazy` — `flow μ (lazy κ) A B = ½ μ (A ∩ B) + ½ flow μ κ A B`.
* `Arlib.Kernel.cut_lazy` — `cut μ (lazy κ) A = ½ cut μ κ A`: the holding part never leaves
  `A`, so it contributes nothing to the cut and laziness halves it exactly.
* `Arlib.Kernel.conductance_lazy` — hence `Φ_{lazy κ}(A) = ½ Φ_κ(A)`.
* `Arlib.Kernel.lazy_reversible`, `Arlib.Kernel.lazy_invariant` — laziness preserves both
  standing hypotheses.
* `Arlib.Kernel.dirichlet_lazy` — the Dirichlet form is halved, hence
  `Arlib.Kernel.lazy_spectralGapAtLeast`: a Poincaré constant `γ` for `κ` becomes `γ/2` for
  `lazy κ`. `Arlib.Kernel.lazy_spectralGapAtLeast_iff` records that nothing is lost, so a gap
  proved for the lazy chain reads back as a gap for the original.

## Scope

Hypotheses that are invisible in the finite analogue and are genuinely needed here:

* `flow_lazy` requires the **target** `B` to be measurable, and `cut_lazy` therefore requires
  `A` to be. On a `Fintype` every set is measurable; here `δ_x B` is only pinned down by
  `Measure.dirac_apply'` when `B` is. (The *source* set of a flow need not be measurable —
  it only restricts the outer integral — which is why `flow_lazy` takes one hypothesis and
  not two.)
* Conversely, `cut_lazy`, `conductance_lazy`, `lazy_reversible` and `lazy_invariant` need
  **no** `IsMarkovKernel` hypothesis, unlike `cut_le` and its relatives in
  `Arlib.MarkovChains.Continuous.Flow`. Halving the cut is a statement about where the
  holding mass goes, not about conservation of mass.

Everything is stated exactly as one would guess from the finite case; no statement had to be
weakened or corrected.

Not proved here: any mixing-time bound. Turning `lazy_spectralGapAtLeast` into a bound on
total variation distance is downstream work. Positive semidefiniteness, which is the point of
the finite `Arlib.MarkovChains.Techniques.Lazy`, has no counterpart in this file, because the
`ℝ≥0∞`-valued development of `Arlib.MarkovChains.Continuous.SpectralGap` carries no signed
inner product to be definite about; the halving of the Dirichlet form is stated directly
instead.
-/

namespace Arlib.Kernel

open MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The lazy kernel -/

/-- The **lazy version** of a kernel: `lazy κ x = ½ δ_x + ½ κ x`, which holds at `x` with
probability `½` and otherwise takes one step of `κ`.

Built by hand from `toFun` together with a measurability proof: `ProbabilityTheory.Kernel`
carries an `Add` instance but no `ℝ≥0∞`-scalar action, so the `½ •` is applied at the level
of measures. -/
noncomputable def lazy (κ : Kernel Ω Ω) : Kernel Ω Ω where
  toFun x := (1 / 2 : ℝ≥0∞) • Measure.dirac x + (1 / 2 : ℝ≥0∞) • κ x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact (((Measure.measurable_coe hs).comp Measure.measurable_dirac).const_mul _).add
      ((Kernel.measurable_coe κ hs).const_mul _)

theorem lazy_apply (κ : Kernel Ω Ω) (x : Ω) :
    lazy κ x = (1 / 2 : ℝ≥0∞) • Measure.dirac x + (1 / 2 : ℝ≥0∞) • κ x := rfl

/-- The value of the lazy kernel on a set. No measurability is needed: both `+` and `•` on
measures are computed pointwise. -/
theorem lazy_apply' (κ : Kernel Ω Ω) (x : Ω) (s : Set Ω) :
    lazy κ x s = 1 / 2 * Measure.dirac x s + 1 / 2 * κ x s := by
  rw [lazy_apply]
  simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- **The lazy version of a Markov kernel is a Markov kernel.** Both halves are probability
measures, and `½ + ½ = 1`. -/
instance isMarkovKernel_lazy (κ : Kernel Ω Ω) [IsMarkovKernel κ] : IsMarkovKernel (lazy κ) :=
  ⟨fun x => ⟨by
    rw [lazy_apply', measure_univ, measure_univ, mul_one, ENNReal.add_halves]⟩⟩

/-! ## Flow, cut and conductance -/

/-- `½` is finite — the side condition that lets `½` be pulled out of a lower integral. -/
theorem one_div_two_ne_top : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- The `μ`-integral over `A` of the Dirac mass of `B` counts exactly the points of `A` that
lie in `B`. -/
theorem lintegral_dirac_apply (μ : Measure Ω) (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ x in A, Measure.dirac x B ∂μ = μ (A ∩ B) := by
  have hpt : ∀ x : Ω, Measure.dirac x B = B.indicator (fun _ => (1 : ℝ≥0∞)) x := fun x =>
    Measure.dirac_apply' x hB
  simp_rw [hpt]
  rw [lintegral_indicator hB _, setLIntegral_one, Measure.restrict_apply hB, Set.inter_comm]

/-- **The flow of the lazy kernel.** The holding half moves mass from `A` into `B` only where
`A` and `B` already overlap, so

  `flow μ (lazy κ) A B = ½ μ (A ∩ B) + ½ flow μ κ A B`.

Only the *target* `B` needs to be measurable; see the module docstring. -/
theorem flow_lazy (μ : Measure Ω) (κ : Kernel Ω Ω) {A B : Set Ω} (hB : MeasurableSet B) :
    flow μ (lazy κ) A B = 1 / 2 * μ (A ∩ B) + 1 / 2 * flow μ κ A B := by
  have hmeas : Measurable fun x : Ω => 1 / 2 * Measure.dirac x B :=
    ((Measure.measurable_coe hB).comp Measure.measurable_dirac).const_mul _
  rw [flow]
  simp_rw [lazy_apply' κ _ B]
  rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ one_div_two_ne_top,
    lintegral_const_mul' _ _ one_div_two_ne_top, lintegral_dirac_apply μ A hB, flow]

/-- **Laziness halves the cut exactly.**

  `cut μ (lazy κ) A = ½ cut μ κ A`.

The holding half of the kernel never leaves `A`, so it contributes `μ (A ∩ Aᶜ) = 0` to the
flow across the boundary; only the moving half, weighted by `½`, escapes.

This is where the factor of two in every lazy-chain mixing bound comes from. Note that no
`IsMarkovKernel` hypothesis is needed. -/
theorem cut_lazy (μ : Measure Ω) (κ : Kernel Ω Ω) {A : Set Ω} (hA : MeasurableSet A) :
    cut μ (lazy κ) A = 1 / 2 * cut μ κ A := by
  rw [cut_apply, flow_lazy μ κ hA.compl, Set.inter_compl_self, measure_empty, mul_zero,
    zero_add, cut_apply]

/-- **Laziness halves the conductance exactly**: `Φ_{lazy κ}(A) = ½ Φ_κ(A)`.

Immediate from `cut_lazy`, since the normalisation `μ A` is untouched. -/
theorem conductance_lazy (μ : Measure Ω) (κ : Kernel Ω Ω) {A : Set Ω} (hA : MeasurableSet A) :
    conductance μ (lazy κ) A = 1 / 2 * conductance μ κ A := by
  rw [conductance_apply, cut_lazy μ κ hA, conductance_apply, mul_div_assoc]

/-! ## Laziness preserves the standing hypotheses -/

/-- **Laziness preserves reversibility.** The extra holding term is `½ μ (A ∩ B)`, symmetric
in `A` and `B` on the nose. -/
theorem lazy_reversible {μ : Measure Ω} {κ : Kernel Ω Ω} (h : Reversible μ κ) :
    Reversible μ (lazy κ) := by
  intro A B hA hB
  rw [flow_lazy μ κ hB, flow_lazy μ κ hA, h A B hA hB, Set.inter_comm]

/-- **Laziness preserves invariance.** One step of `lazy κ` leaves half of `μ` where it is and
pushes the other half through `κ`, which returns `μ`; the two halves reassemble.

No `IsMarkovKernel` hypothesis is required. -/
theorem lazy_invariant {μ : Measure Ω} {κ : Kernel Ω Ω}
    (h : _root_.ProbabilityTheory.Kernel.Invariant κ μ) :
    _root_.ProbabilityTheory.Kernel.Invariant (lazy κ) μ := by
  ext A hA
  have hbindκ : μ.bind κ A = ∫⁻ x, κ x A ∂μ := Measure.bind_apply hA (Kernel.measurable κ)
  have hdirac : ∫⁻ x, Measure.dirac x A ∂μ = μ A := by
    simpa using lintegral_dirac_apply μ Set.univ hA
  have hmeas : Measurable fun x : Ω => 1 / 2 * Measure.dirac x A :=
    ((Measure.measurable_coe hA).comp Measure.measurable_dirac).const_mul _
  rw [Measure.bind_apply hA (Kernel.measurable (lazy κ))]
  simp_rw [lazy_apply' κ _ A]
  rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ one_div_two_ne_top,
    lintegral_const_mul' _ _ one_div_two_ne_top, ← hbindκ, h, hdirac, ← add_mul,
    ENNReal.add_halves, one_mul]

/-! ## The Dirichlet form and the spectral gap -/

/-- A function vanishing at `x` has zero lower integral against `δ_x`, with **no**
measurability hypothesis: every measurable simple minorant is bounded at `x` by the value of
the function there, namely `0`.

This is what lets `dirichlet_lazy` be stated for arbitrary `f : Ω → ℝ`, matching
`Arlib.Kernel.SpectralGapAtLeast`, which quantifies over all real functions. -/
theorem lintegral_dirac_eq_zero {g : Ω → ℝ≥0∞} {x : Ω} (hx : g x = 0) :
    ∫⁻ y, g y ∂(Measure.dirac x) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  rw [lintegral]
  refine iSup₂_le fun s hs => ?_
  have h1 : s.lintegral (Measure.dirac x) = s x := by
    rw [← SimpleFunc.lintegral_eq_lintegral, lintegral_dirac' _ s.measurable]
  rw [h1, ← hx]
  exact hs x

/-- **Laziness halves the Dirichlet form**: `ℰ_{lazy κ}(f) = ½ ℰ_κ(f)`.

The holding half contributes `(f x − f x)² = 0` to the pair form, so only the moving half
survives, weighted by `½`. Holds for every `f : Ω → ℝ`, measurable or not. -/
theorem dirichlet_lazy (μ : Measure Ω) (κ : Kernel Ω Ω) (f : Ω → ℝ) :
    dirichlet μ (lazy κ) f = 1 / 2 * dirichlet μ κ f := by
  have hinner : ∀ x : Ω,
      ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(lazy κ x)
        = 1 / 2 * ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(κ x) := by
    intro x
    have hzero : ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(Measure.dirac x) = 0 :=
      lintegral_dirac_eq_zero (by simp)
    rw [lazy_apply, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      hzero, mul_zero, zero_add]
  rw [dirichlet_apply, dirichlet_apply]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ one_div_two_ne_top]

/-- Rearrangement used twice below: `γ/2 · a = ½ · (γ · a)`. -/
theorem div_two_mul (γ a : ℝ≥0∞) : γ / 2 * a = 1 / 2 * (γ * a) := by
  rw [div_eq_mul_inv, one_div, mul_comm γ ((2 : ℝ≥0∞)⁻¹), mul_assoc]

/-- **Laziness halves the spectral gap.** A Poincaré constant `γ` for `κ` yields the constant
`γ/2` for `lazy κ`: the variance is untouched and the Dirichlet form is halved.

This is the quantitative cost of removing periodicity, and the reason mixing-time bounds for
lazy walks carry a factor of two. -/
theorem lazy_spectralGapAtLeast {μ : Measure Ω} {κ : Kernel Ω Ω} {γ : ℝ≥0∞}
    (h : SpectralGapAtLeast μ κ γ) : SpectralGapAtLeast μ (lazy κ) (γ / 2) := by
  intro f
  rw [dirichlet_lazy, div_two_mul]
  exact mul_le_mul_left' (h f) _

/-- **The halving loses nothing.** `lazy κ` has Poincaré constant at least `γ/2` exactly when
`κ` has Poincaré constant at least `γ`, so a gap proved for the lazy chain can be read back as
a gap for the original.

The forward direction cancels the finite nonzero factor `½` from both sides. -/
theorem lazy_spectralGapAtLeast_iff {μ : Measure Ω} {κ : Kernel Ω Ω} {γ : ℝ≥0∞} :
    SpectralGapAtLeast μ (lazy κ) (γ / 2) ↔ SpectralGapAtLeast μ κ γ := by
  refine ⟨fun h f => ?_, lazy_spectralGapAtLeast⟩
  have hf := h f
  rw [dirichlet_lazy, div_two_mul] at hf
  exact (ENNReal.mul_le_mul_left (by norm_num) one_div_two_ne_top).mp hf

end Arlib.Kernel
