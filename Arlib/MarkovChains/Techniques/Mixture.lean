/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Convex combinations of chains

A convex combination of Markov kernels is again a Markov kernel: "toss a coin,
then take a step of whichever chain came up".  This is not a curiosity but the
way the chains this development cares about are *built*.  The Glauber dynamics
on a spin system is, by definition, the uniform average over the vertices `v` of
the single-site heat-bath update at `v`; heat-bath block dynamics is the uniform
average over blocks.  And the proof in the monograph — Chen–Štefankovič–Vigoda,
*Spectral Independence and Local-to-Global Techniques for Optimal Mixing of
Markov Chains*, arXiv:2307.13826 (2023), cited below as [CSV23] — that
heat-bath block dynamics is
positive semidefinite is exactly the observation that each single-block update
is PSD together with the fact that *a mixture of PSD kernels is PSD*.

This module supplies that algebra once and in general, so that the concrete
chains in `Chains/` can inherit stationarity, reversibility, positive
semidefiniteness and Poincaré inequalities from their constituents for free.

* `FinKernel.mix θ _ _ K L` — the two-way mixture `θ K + (1 - θ) L`, with
  `act_mix`, `ip_act_mix`, `mix_stationary`, `mix_reversible`, `dirichlet_mix`,
  **`mix_nonnegDefinite`** and `mix_spectralGapAtLeast`.
* `FinKernel.avg K` — the **uniform average** `(1 / |ι|) ∑ i, K i` over a
  finite nonempty index type, with the same list of lemmas.  This is the form
  downstream code should prefer: no hypotheses are carried in the data, so terms
  built from it are defeq across different proof terms.
* **`avg_nonnegDefinite`** — the statement [CSV23] uses for the positive
  semidefiniteness of heat-bath block dynamics: an average of positive
  semidefinite chains is positive semidefinite.  (`docs/dev/MarkovChains-ROADMAP.md` attributes the
  positive semidefiniteness of Glauber dynamics to Dyer–Greenhill–Ullrich; the
  precise reference is not recorded anywhere in this library.)
* **`avg_spectralGapAtLeast_of_single`** — the form that actually gets used for
  Glauber dynamics: if *one* constituent has a Poincaré constant `γ` and all the
  others are merely stationary, the average has Poincaré constant `γ / |ι|`.
  Each Dirichlet form is nonnegative, so the average is at least `1 / |ι|` times
  any single one.
* `FinKernel.mixWeights w _ _ K` — the general weighted mixture `∑ i, w i · K i`,
  of which `avg` is the special case `w ≡ 1 / |ι|` (`avg_eq_mixWeights`).

The lazy chain is a mixture too: `FinChain.lazy P = mix (1/2) _ _ (id Ω) P`,
recorded here as `lazy_eq_mix`.  `Arlib.MarkovChains.Techniques.Lazy` is left as
it stands — its proofs are self-contained and short — but new constructions of
this shape should go through `mix` or `avg`.

Both `mix` and `mixWeights` are forced to carry their hypotheses (`0 ≤ θ ≤ 1`,
respectively nonnegativity and normalisation of `w`) in the data, since they are
genuinely needed for the `P_nonneg` and `P_sum` fields; `Chains.TwoState` makes
the same compromise.  `avg` needs none, which is why it is the preferred form.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Lazy
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The two-way mixture -/

/-- The **mixture** of two chains: `mix θ K L = θ · K + (1 - θ) · L`, the chain
that takes a step of `K` with probability `θ` and a step of `L` otherwise.

The bounds `0 ≤ θ ≤ 1` have to sit in the data because they are what makes the
matrix nonnegative.  For the hypothesis-free version see `FinKernel.avg`. -/
def FinKernel.mix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (K L : FinChain Ω) : FinChain Ω where
  P x y := θ * K x y + (1 - θ) * L x y
  P_nonneg x y :=
    add_nonneg (mul_nonneg hθ0 (K.coe_nonneg x y))
      (mul_nonneg (by linarith) (L.coe_nonneg x y))
  P_sum x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, K.sum_coe x, L.sum_coe x]
    ring

theorem FinKernel.mix_apply (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (K L : FinChain Ω) (x y : Ω) :
    FinKernel.mix θ hθ0 hθ1 K L x y = θ * K x y + (1 - θ) * L x y := rfl

/-- The mixture acts as the corresponding combination of the two actions:
`(θK + (1-θ)L) f = θ · K f + (1 - θ) · L f`. -/
theorem FinKernel.act_mix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (K L : FinChain Ω) (f : Ω → ℝ) :
    (FinKernel.mix θ hθ0 hθ1 K L).act f = fun x => θ * K.act f x + (1 - θ) * L.act f x := by
  funext x
  show ∑ y, (θ * K x y + (1 - θ) * L x y) * f y = _
  have step : ∀ y : Ω, (θ * K x y + (1 - θ) * L x y) * f y
      = θ * (K x y * f y) + (1 - θ) * (L x y * f y) := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- The quadratic form of a mixture is the mixture of the quadratic forms. -/
theorem ip_act_mix (μ : FinDist Ω) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (K L : FinChain Ω) (f : Ω → ℝ) :
    ip μ f ((FinKernel.mix θ hθ0 hθ1 K L).act f)
      = θ * ip μ f (K.act f) + (1 - θ) * ip μ f (L.act f) := by
  rw [FinKernel.act_mix]
  simp only [ip]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ## The standing hypotheses pass to a mixture -/

/-- A distribution stationary for both constituents is stationary for the mixture. -/
theorem mix_stationary {μ : FinDist Ω} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {K L : FinChain Ω} (hK : Stationary μ K) (hL : Stationary μ L) :
    Stationary μ (FinKernel.mix θ hθ0 hθ1 K L) := by
  intro y
  have step : ∀ x : Ω, μ x * FinKernel.mix θ hθ0 hθ1 K L x y
      = θ * (μ x * K x y) + (1 - θ) * (μ x * L x y) := fun x => by
    rw [FinKernel.mix_apply]; ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hK y, hL y]
  ring

/-- A chain reversible with respect to `μ` mixed with another such chain is again
reversible with respect to `μ`. -/
theorem mix_reversible {μ : FinDist Ω} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {K L : FinChain Ω} (hK : Reversible μ K) (hL : Reversible μ L) :
    Reversible μ (FinKernel.mix θ hθ0 hθ1 K L) := by
  intro x y
  rw [FinKernel.mix_apply, FinKernel.mix_apply]
  have h1 := hK x y
  have h2 := hL x y
  nlinarith [h1, h2]

/-! ## The Dirichlet form, positive semidefiniteness and the gap -/

/-- The Dirichlet form of a mixture is the mixture of the Dirichlet forms. -/
theorem dirichlet_mix (μ : FinDist Ω) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (K L : FinChain Ω) (f : Ω → ℝ) :
    dirichlet μ (FinKernel.mix θ hθ0 hθ1 K L) f f
      = θ * dirichlet μ K f f + (1 - θ) * dirichlet μ L f f := by
  simp only [dirichlet_apply]
  rw [ip_act_mix]
  ring

/-- **A mixture of positive semidefinite chains is positive semidefinite.**
The two-index case of the fact the monograph uses to prove that heat-bath block
dynamics is PSD. -/
theorem mix_nonnegDefinite {μ : FinDist Ω} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {K L : FinChain Ω} (hK : NonnegDefinite μ K) (hL : NonnegDefinite μ L) :
    NonnegDefinite μ (FinKernel.mix θ hθ0 hθ1 K L) := by
  intro f
  rw [ip_act_mix]
  exact add_nonneg (mul_nonneg hθ0 (hK f)) (mul_nonneg (by linarith) (hL f))

/-- A Poincaré inequality with constant `γ` for both constituents gives one with
constant `γ` for the mixture. -/
theorem mix_spectralGapAtLeast {μ : FinDist Ω} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {K L : FinChain Ω} {γ : ℝ} (hK : SpectralGapAtLeast μ K γ) (hL : SpectralGapAtLeast μ L γ) :
    SpectralGapAtLeast μ (FinKernel.mix θ hθ0 hθ1 K L) γ := by
  intro f
  rw [dirichlet_mix]
  have a := mul_le_mul_of_nonneg_left (hK f) hθ0
  have b := mul_le_mul_of_nonneg_left (hL f) (by linarith : (0 : ℝ) ≤ 1 - θ)
  linarith

/-! ## The lazy chain as a mixture -/

section DecEq

variable [DecidableEq Ω]

/-- **The lazy chain is a mixture**: `P_lazy = mix (1/2) (id) P`.  This is the
sense in which `Arlib.MarkovChains.Techniques.Lazy` is a special case of the
present module. -/
theorem lazy_eq_mix (P : FinChain Ω) :
    P.lazy = FinKernel.mix (1 / 2) (by norm_num) (by norm_num) (FinKernel.id Ω) P :=
  FinKernel.ext' fun x y => by
    rw [FinChain.lazy_apply, FinKernel.mix_apply]
    show _ = 1 / 2 * (if x = y then 1 else 0) + (1 - 1 / 2) * P x y
    ring

end DecEq

/-! ## The uniform average over a finite index type

This is the form the concrete chains need: the Glauber dynamics is the uniform
average of the single-site updates, and heat-bath block dynamics the uniform
average of the block updates.  No hypotheses appear in the data. -/

section Avg

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The **uniform average** of a family of chains:
`avg K = (1 / |ι|) ∑ i, K i`, the chain that picks an index uniformly at random
and takes a step of the corresponding chain. -/
noncomputable def FinKernel.avg (K : ι → FinChain Ω) : FinChain Ω where
  P x y := (1 / (Fintype.card ι : ℝ)) * ∑ i, K i x y
  P_nonneg x y :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (K i).coe_nonneg x y)
  P_sum x := by
    have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hrow : ∀ i : ι, ∑ y, K i x y = 1 := fun i => (K i).sum_coe x
    rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp

theorem FinKernel.avg_apply (K : ι → FinChain Ω) (x y : Ω) :
    FinKernel.avg K x y = (1 / (Fintype.card ι : ℝ)) * ∑ i, K i x y := rfl

/-- The average acts as the average of the actions. -/
theorem FinKernel.act_avg (K : ι → FinChain Ω) (f : Ω → ℝ) :
    (FinKernel.avg K).act f = fun x => (1 / (Fintype.card ι : ℝ)) * ∑ i, (K i).act f x := by
  funext x
  show ∑ y, ((1 / (Fintype.card ι : ℝ)) * ∑ i, K i x y) * f y = _
  have step : ∀ y : Ω, ((1 / (Fintype.card ι : ℝ)) * ∑ i, K i x y) * f y
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, K i x y * f y := fun y => by
    rw [mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun y _ => step y, ← Finset.mul_sum, Finset.sum_comm]
  rfl

/-- The quadratic form of an average is the average of the quadratic forms. -/
theorem ip_act_avg (μ : FinDist Ω) (K : ι → FinChain Ω) (f : Ω → ℝ) :
    ip μ f ((FinKernel.avg K).act f)
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, ip μ f ((K i).act f) := by
  rw [FinKernel.act_avg]
  simp only [ip]
  calc ∑ x, μ x * f x * ((1 / (Fintype.card ι : ℝ)) * ∑ i, (K i).act f x)
      = ∑ x, ∑ i, (1 / (Fintype.card ι : ℝ)) * (μ x * f x * (K i).act f x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ x, (1 / (Fintype.card ι : ℝ)) * (μ x * f x * (K i).act f x) := Finset.sum_comm
    _ = (1 / (Fintype.card ι : ℝ)) * ∑ i, ∑ x, μ x * f x * (K i).act f x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- A distribution stationary for every member of the family is stationary for
the average. -/
theorem avg_stationary {μ : FinDist Ω} {K : ι → FinChain Ω} (h : ∀ i, Stationary μ (K i)) :
    Stationary μ (FinKernel.avg K) := by
  intro y
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have step : ∀ x : Ω, μ x * FinKernel.avg K x y
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, μ x * K i x y := fun x => by
    rw [FinKernel.avg_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun x _ => step x, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => h i y]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A family of chains all reversible with respect to `μ` averages to a chain
reversible with respect to `μ`. -/
theorem avg_reversible {μ : FinDist Ω} {K : ι → FinChain Ω} (h : ∀ i, Reversible μ (K i)) :
    Reversible μ (FinKernel.avg K) := by
  intro x y
  rw [FinKernel.avg_apply, FinKernel.avg_apply, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show μ x * ((1 / (Fintype.card ι : ℝ)) * K i x y)
      = (1 / (Fintype.card ι : ℝ)) * (μ x * K i x y) by ring, h i x y]
  ring

/-- The Dirichlet form of an average is the average of the Dirichlet forms. -/
theorem dirichlet_avg (μ : FinDist Ω) (K : ι → FinChain Ω) (f : Ω → ℝ) :
    dirichlet μ (FinKernel.avg K) f f
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, dirichlet μ (K i) f f := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [dirichlet_apply]
  rw [ip_act_avg, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **An average of positive semidefinite chains is positive semidefinite.**

This is the algebraic content of the monograph's proof that heat-bath block
dynamics is PSD: the block dynamics is the uniform average of the single-block
updates, each of which is PSD. -/
theorem avg_nonnegDefinite {μ : FinDist Ω} {K : ι → FinChain Ω}
    (h : ∀ i, NonnegDefinite μ (K i)) : NonnegDefinite μ (FinKernel.avg K) := by
  intro f
  rw [ip_act_avg]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => h i f)

/-- If every member of the family satisfies the Poincaré inequality with constant
`γ`, so does the average. -/
theorem avg_spectralGapAtLeast {μ : FinDist Ω} {K : ι → FinChain Ω} {γ : ℝ}
    (h : ∀ i, SpectralGapAtLeast μ (K i) γ) : SpectralGapAtLeast μ (FinKernel.avg K) γ := by
  intro f
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hle : ∑ _i : ι, γ * Var μ f ≤ ∑ i, dirichlet μ (K i) f f :=
    Finset.sum_le_sum fun i _ => h i f
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
  rw [dirichlet_avg]
  have hrw : γ * Var μ f
      = (1 / (Fintype.card ι : ℝ)) * ((Fintype.card ι : ℝ) * (γ * Var μ f)) := by
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ### One good constituent is enough

The Dirichlet form of every stationary chain is nonnegative, so the average of
the Dirichlet forms is at least `1 / |ι|` times any single one.  This is the
shape in which the estimate is used for the Glauber dynamics, where a Poincaré
inequality is available for one site (or one block) at a time. -/

/-- The Dirichlet form of the average dominates `1 / |ι|` times that of any
single constituent, provided all of them are stationary. -/
theorem dirichlet_avg_ge_single {μ : FinDist Ω} {K : ι → FinChain Ω}
    (h : ∀ i, Stationary μ (K i)) (i₀ : ι) (f : Ω → ℝ) :
    (1 / (Fintype.card ι : ℝ)) * dirichlet μ (K i₀) f f
      ≤ dirichlet μ (FinKernel.avg K) f f := by
  rw [dirichlet_avg]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.single_le_sum (fun i _ => dirichlet_self_nonneg (h i) f) (Finset.mem_univ i₀)

/-- **One constituent with a spectral gap suffices.**  If a single `K i₀`
satisfies the Poincaré inequality with constant `γ` and all the others are merely
stationary, then the uniform average satisfies it with constant `γ / |ι|`. -/
theorem avg_spectralGapAtLeast_of_single {μ : FinDist Ω} {K : ι → FinChain Ω} {γ : ℝ}
    (hstat : ∀ i, Stationary μ (K i)) (i₀ : ι) (hgap : SpectralGapAtLeast μ (K i₀) γ) :
    SpectralGapAtLeast μ (FinKernel.avg K) (γ / (Fintype.card ι : ℝ)) := by
  intro f
  have hrw : γ / (Fintype.card ι : ℝ) * Var μ f
      = (1 / (Fintype.card ι : ℝ)) * (γ * Var μ f) := by ring
  rw [hrw]
  refine le_trans (mul_le_mul_of_nonneg_left (hgap f) (by positivity)) ?_
  exact dirichlet_avg_ge_single hstat i₀ f

end Avg

/-! ## The general weighted mixture

`mix` and `avg` are both instances of a convex combination `∑ i, w i · K i` with
arbitrary weights.  The general version is recorded for completeness; `avg` is
the special case of constant weights (`avg_eq_mixWeights`). -/

section Weighted

variable {ι : Type*} [Fintype ι]

/-- The **weighted mixture** `∑ i, w i · K i` of a family of chains along a
probability vector `w`. -/
def FinKernel.mixWeights (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (K : ι → FinChain Ω) : FinChain Ω where
  P x y := ∑ i, w i * K i x y
  P_nonneg x y := Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) ((K i).coe_nonneg x y)
  P_sum x := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ y, w i * K i x y = ∑ i, w i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, (K i).sum_coe x, mul_one]
      _ = 1 := hw1

theorem FinKernel.mixWeights_apply (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (K : ι → FinChain Ω) (x y : Ω) :
    FinKernel.mixWeights w hw0 hw1 K x y = ∑ i, w i * K i x y := rfl

/-- The weighted mixture acts as the corresponding combination of the actions. -/
theorem FinKernel.act_mixWeights (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (K : ι → FinChain Ω) (f : Ω → ℝ) :
    (FinKernel.mixWeights w hw0 hw1 K).act f = fun x => ∑ i, w i * (K i).act f x := by
  funext x
  show ∑ y, (∑ i, w i * K i x y) * f y = _
  have step : ∀ y : Ω, (∑ i, w i * K i x y) * f y = ∑ i, w i * (K i x y * f y) := fun y => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]; rfl

/-- The quadratic form of a weighted mixture is the corresponding combination of
the quadratic forms. -/
theorem ip_act_mixWeights (μ : FinDist Ω) (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (K : ι → FinChain Ω) (f : Ω → ℝ) :
    ip μ f ((FinKernel.mixWeights w hw0 hw1 K).act f)
      = ∑ i, w i * ip μ f ((K i).act f) := by
  rw [FinKernel.act_mixWeights]
  simp only [ip]
  calc ∑ x, μ x * f x * ∑ i, w i * (K i).act f x
      = ∑ x, ∑ i, w i * (μ x * f x * (K i).act f x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ x, w i * (μ x * f x * (K i).act f x) := Finset.sum_comm
    _ = ∑ i, w i * ∑ x, μ x * f x * (K i).act f x :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- A distribution stationary for every member of the family is stationary for
any weighted mixture. -/
theorem mixWeights_stationary {μ : FinDist Ω} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {K : ι → FinChain Ω} (h : ∀ i, Stationary μ (K i)) :
    Stationary μ (FinKernel.mixWeights w hw0 hw1 K) := by
  intro y
  have step : ∀ x : Ω, μ x * FinKernel.mixWeights w hw0 hw1 K x y
      = ∑ i, w i * (μ x * K i x y) := fun x => by
    rw [FinKernel.mixWeights_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
  calc ∑ i, ∑ x, w i * (μ x * K i x y) = ∑ i, w i * μ y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, h i y]
    _ = μ y := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A family of chains all reversible with respect to `μ` has all its weighted
mixtures reversible with respect to `μ`. -/
theorem mixWeights_reversible {μ : FinDist Ω} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {K : ι → FinChain Ω} (h : ∀ i, Reversible μ (K i)) :
    Reversible μ (FinKernel.mixWeights w hw0 hw1 K) := by
  intro x y
  rw [FinKernel.mixWeights_apply, FinKernel.mixWeights_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show μ x * (w i * K i x y) = w i * (μ x * K i x y) by ring, h i x y]
  ring

/-- The Dirichlet form of a weighted mixture is the corresponding combination of
the Dirichlet forms. -/
theorem dirichlet_mixWeights (μ : FinDist Ω) (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (K : ι → FinChain Ω) (f : Ω → ℝ) :
    dirichlet μ (FinKernel.mixWeights w hw0 hw1 K) f f
      = ∑ i, w i * dirichlet μ (K i) f f := by
  simp only [dirichlet_apply]
  rw [ip_act_mixWeights]
  have hsplit : ∑ i, w i * (ip μ f f - ip μ f ((K i).act f))
      = (∑ i, w i) * ip μ f f - ∑ i, w i * ip μ f ((K i).act f) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hw1, one_mul]

/-- **A weighted mixture of positive semidefinite chains is positive
semidefinite.** -/
theorem mixWeights_nonnegDefinite {μ : FinDist Ω} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {K : ι → FinChain Ω} (h : ∀ i, NonnegDefinite μ (K i)) :
    NonnegDefinite μ (FinKernel.mixWeights w hw0 hw1 K) := by
  intro f
  rw [ip_act_mixWeights]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (h i f)

/-- If every member of the family satisfies the Poincaré inequality with constant
`γ`, so does every weighted mixture. -/
theorem mixWeights_spectralGapAtLeast {μ : FinDist Ω} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {K : ι → FinChain Ω} {γ : ℝ}
    (h : ∀ i, SpectralGapAtLeast μ (K i) γ) :
    SpectralGapAtLeast μ (FinKernel.mixWeights w hw0 hw1 K) γ := by
  intro f
  rw [dirichlet_mixWeights]
  have hle : ∑ i, w i * (γ * Var μ f) ≤ ∑ i, w i * dirichlet μ (K i) f f :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i f) (hw0 i)
  rw [← Finset.sum_mul, hw1, one_mul] at hle
  exact hle

/-- The uniform average is the weighted mixture with constant weights. -/
theorem avg_eq_mixWeights [Nonempty ι] (K : ι → FinChain Ω) :
    FinKernel.avg K
      = FinKernel.mixWeights (fun _ => 1 / (Fintype.card ι : ℝ)) (fun _ => by positivity)
          (by
            have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            field_simp) K :=
  FinKernel.ext' fun x y => by
    rw [FinKernel.avg_apply, FinKernel.mixWeights_apply, Finset.mul_sum]

end Weighted

end Arlib.MarkovChains
