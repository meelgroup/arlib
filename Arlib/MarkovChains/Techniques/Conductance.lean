/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conductance and the easy direction of Cheeger's inequality

The spectral gap is a global analytic quantity: to bound it one must control
`ℰ_P(f)` against `Var_μ(f)` for *every* `f`.  Conductance is the combinatorial
shadow of the same idea, and it is something one can actually estimate on a
concrete chain by counting: the probability, in stationarity, that a single step
escapes a set `A`, normalised by the probability of `A`.  A set with small
conductance is a bottleneck, and a bottleneck forces slow mixing.

That implication — the *easy* half of Cheeger's inequality — is exactly the
Poincaré inequality evaluated at one particular test function, the indicator of
`A`.  For that `f` the Dirichlet form *is* the cut (`dirichlet_indicator`) and
the variance *is* `Pr(A)(1 - Pr(A))` (`Var_indicator`), so the Poincaré
inequality reads off as a bound on `γ` with no analysis at all.  This makes the
module a good fit for the no-eigenvalue discipline of this development (ROADMAP
§1.2), and it gives `Chains/` modules the tool they need to certify *lower*
bounds on mixing time.  The hard direction of Cheeger genuinely needs more
machinery and is deliberately out of scope here.

* `flow μ P A B` — the stationary ergodic flow `∑_{x ∈ A} ∑_{y ∈ B} μ(x) P(x,y)`
  from `A` to `B`, with `flow_univ_right`, `flow_univ_left_of_stationary`, and
  **`flow_comm`** — detailed balance summed over a rectangle.  `flow_comm` is
  the one and only place reversibility enters this file.
* `cut μ P A = flow μ P A Aᶜ` — the probability of crossing the cut in one step,
  and `cut_eq_Pr_sub`.
* **`dirichlet_indicator`** — for `f` the indicator of `A` and `P` reversible,
  `ℰ_P(f) = cut μ P A`.  Its stationary-only precursor
  `dirichlet_indicator_eq_flow_add` gives the symmetrised form
  `½(flow A Aᶜ + flow Aᶜ A)`.
* `Var_indicator` — `Var_μ(1_A) = Pr(A)(1 - Pr(A))`, needing no hypothesis on
  `μ` or `P` at all.
* `conductance μ P A = cut μ P A / Pr μ A`, with `conductance_nonneg` and
  `conductance_le_one`.
* **`spectralGap_mul_le_cut`** — `γ · Pr(A)(1 - Pr(A)) ≤ cut μ P A`, the
  un-normalised statement, with no constraint whatsoever on `Pr(A)`.
* **`spectralGap_le_conductance`** — the headline: for `0 < Pr(A) ≤ ½` and
  `0 ≤ γ`, a chain with spectral gap at least `γ` satisfies `γ ≤ 2 Φ(A)`.
* `not_spectralGapAtLeast_of_lt` — the contrapositive, which is the shape a
  slow-mixing argument actually applies.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Dirichlet
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Ergodic flow

The *flow* from `A` to `B` is the stationary probability that a single step of
the chain starts in `A` and lands in `B`.  It is the only quantity this module
needs, and every statement below is an identity or inequality about it. -/

/-- The **ergodic flow** from `A` to `B`: `∑_{x ∈ A} ∑_{y ∈ B} μ(x) P(x,y)`,
the probability that one step of the chain, started from `μ`, goes from `A`
to `B`. -/
def flow (μ : FinDist Ω) (P : FinChain Ω) (A B : Finset Ω) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, μ x * P x y

theorem flow_apply (μ : FinDist Ω) (P : FinChain Ω) (A B : Finset Ω) :
    flow μ P A B = ∑ x ∈ A, ∑ y ∈ B, μ x * P x y := rfl

/-- Flow is a sum of products of nonnegative numbers. -/
theorem flow_nonneg (μ : FinDist Ω) (P : FinChain Ω) (A B : Finset Ω) :
    0 ≤ flow μ P A B :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y)

@[simp] theorem flow_empty_left (μ : FinDist Ω) (P : FinChain Ω) (B : Finset Ω) :
    flow μ P ∅ B = 0 := rfl

@[simp] theorem flow_empty_right (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    flow μ P A ∅ = 0 := Finset.sum_eq_zero fun _ _ => rfl

/-- Everything flows somewhere: `flow μ P A univ = Pr μ A`.  This is row
stochasticity of `P`, and needs no hypothesis on `μ`. -/
theorem flow_univ_right (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    flow μ P A univ = Pr μ A := by
  rw [flow_apply, Pr_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, P.sum_coe x, mul_one]

/-- Everything flows from somewhere, *provided `μ` is stationary*:
`flow μ P univ B = Pr μ B`.  This is the only content of stationarity that the
flow calculus uses. -/
theorem flow_univ_left_of_stationary {μ : FinDist Ω} {P : FinChain Ω}
    (h : Stationary μ P) (B : Finset Ω) : flow μ P univ B = Pr μ B := by
  rw [flow_apply, Pr_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [h y]

/-- **Flow is symmetric for a reversible chain.**  Summing detailed balance
`μ(x) P(x,y) = μ(y) P(y,x)` over the rectangle `A × B` gives
`flow μ P A B = flow μ P B A`.

This is the sole use of reversibility in this file; everything downstream that
mentions `Reversible` does so only to invoke this lemma. -/
theorem flow_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P)
    (A B : Finset Ω) : flow μ P A B = flow μ P B A := by
  rw [flow_apply, flow_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => h x y

section Compl

variable [DecidableEq Ω]

/-! ## The cut

The *cut* of `A` is the flow out of `A`: the stationary probability that one
step of the chain leaves `A`.  It is the numerator of the conductance and, by
`dirichlet_indicator`, the Dirichlet form of the indicator of `A`. -/

/-- The **cut** across `A`: the flow from `A` to its complement, i.e. the
stationary probability that a single step escapes `A`. -/
def cut (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) : ℝ := flow μ P A Aᶜ

theorem cut_apply (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    cut μ P A = flow μ P A Aᶜ := rfl

theorem cut_nonneg (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) : 0 ≤ cut μ P A :=
  flow_nonneg μ P A Aᶜ

/-- The cut is what is left of `Pr μ A` after subtracting the flow that stays
inside `A`.  In particular `cut μ P A ≤ Pr μ A`. -/
theorem cut_eq_Pr_sub (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    cut μ P A = Pr μ A - flow μ P A A := by
  have key : flow μ P A A + cut μ P A = Pr μ A := by
    rw [← flow_univ_right μ P A, cut_apply, flow_apply, flow_apply, flow_apply,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_add_sum_compl A _
  linarith

/-- The cut never exceeds the mass of the set it cuts. -/
theorem cut_le_Pr (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    cut μ P A ≤ Pr μ A := by
  have h := flow_nonneg μ P A A
  have := cut_eq_Pr_sub μ P A
  linarith

/-! ## The Dirichlet form and the variance of an indicator

Both halves of the Poincaré inequality can be evaluated in closed form at the
indicator of a set.  This is the entire content of the easy direction of
Cheeger's inequality; the rest is arithmetic. -/

/-- **Symmetrised form of the Dirichlet form of an indicator.**  For a
*stationary* `μ`,
`ℰ_P(1_A) = ½ (flow μ P A Aᶜ + flow μ P Aᶜ A)`.

In the pair form `½ ∑_{x,y} μ(x) P(x,y) (1_A x - 1_A y)²` the summand is
`μ(x) P(x,y)` when exactly one of `x`, `y` lies in `A`, and `0` otherwise; the
two ways of "exactly one" are the two flows. -/
theorem dirichlet_indicator_eq_flow_add {μ : FinDist Ω} {P : FinChain Ω}
    (h : Stationary μ P) (A : Finset Ω) :
    dirichlet μ P (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun x => if x ∈ A then (1 : ℝ) else 0)
      = (1 / 2) * (flow μ P A Aᶜ + flow μ P Aᶜ A) := by
  rw [dirichlet_self_eq_pair h]
  congr 1
  have key : ∀ x : Ω, ∑ y, μ x * P x y *
      ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2
      = if x ∈ A then ∑ y ∈ Aᶜ, μ x * P x y else ∑ y ∈ A, μ x * P x y := by
    intro x
    rw [← Finset.sum_add_sum_compl A (fun y => μ x * P x y *
      ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2)]
    by_cases hx : x ∈ A
    · have h1 : ∑ y ∈ A, μ x * P x y *
          ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2 = 0 :=
        Finset.sum_eq_zero fun y hy => by rw [if_pos hx, if_pos hy]; ring
      have h2 : ∑ y ∈ Aᶜ, μ x * P x y *
          ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2
          = ∑ y ∈ Aᶜ, μ x * P x y :=
        Finset.sum_congr rfl fun y hy => by
          rw [if_pos hx, if_neg (Finset.mem_compl.mp hy)]; ring
      rw [h1, h2, zero_add, if_pos hx]
    · have h1 : ∑ y ∈ A, μ x * P x y *
          ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2
          = ∑ y ∈ A, μ x * P x y :=
        Finset.sum_congr rfl fun y hy => by rw [if_neg hx, if_pos hy]; ring
      have h2 : ∑ y ∈ Aᶜ, μ x * P x y *
          ((if x ∈ A then (1 : ℝ) else 0) - (if y ∈ A then (1 : ℝ) else 0)) ^ 2 = 0 :=
        Finset.sum_eq_zero fun y hy => by
          rw [if_neg hx, if_neg (Finset.mem_compl.mp hy)]; ring
      rw [h1, h2, add_zero, if_neg hx]
  rw [Finset.sum_congr rfl fun x _ => key x, flow_apply, flow_apply,
    ← Finset.sum_add_sum_compl A
      (fun x => if x ∈ A then ∑ y ∈ Aᶜ, μ x * P x y else ∑ y ∈ A, μ x * P x y)]
  congr 1
  · exact Finset.sum_congr rfl fun x hx => if_pos hx
  · exact Finset.sum_congr rfl fun x hx => if_neg (Finset.mem_compl.mp hx)

/-- **The Dirichlet form of an indicator is the cut.**  For `P` reversible with
respect to `μ` and `f = 1_A`,
`ℰ_P(f) = cut μ P A`.

Reversibility is used exactly once, to identify the two flows across the cut
(`flow_comm`); without it one still has the symmetrised
`dirichlet_indicator_eq_flow_add`, which needs only stationarity. -/
theorem dirichlet_indicator {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P)
    (A : Finset Ω) :
    dirichlet μ P (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun x => if x ∈ A then (1 : ℝ) else 0)
      = cut μ P A := by
  rw [dirichlet_indicator_eq_flow_add h.stationary A, flow_comm h Aᶜ A, cut_apply]
  ring

/-- **The variance of an indicator** is `Pr(A) (1 - Pr(A))`.  No hypothesis on
`μ` or `P` is needed: the indicator is idempotent, so `⟪1_A, 1_A⟫_μ = Pr μ A`,
and its mean is `Pr μ A` as well. -/
theorem Var_indicator (μ : FinDist Ω) (A : Finset Ω) :
    Var μ (fun x => if x ∈ A then (1 : ℝ) else 0) = Pr μ A * (1 - Pr μ A) := by
  have hEx : Ex μ (fun x => if x ∈ A then (1 : ℝ) else 0) = Pr μ A :=
    (Pr_eq_Ex_indicator μ A).symm
  have hip : ip μ (fun x => if x ∈ A then (1 : ℝ) else 0)
      (fun x => if x ∈ A then (1 : ℝ) else 0) = Pr μ A := by
    have step : ∀ x : Ω, μ x * (if x ∈ A then (1 : ℝ) else 0) *
        (if x ∈ A then (1 : ℝ) else 0) = if x ∈ A then μ x else 0 := by
      intro x; by_cases hx : x ∈ A <;> simp [hx]
    rw [ip_apply, Finset.sum_congr rfl fun x _ => step x, Finset.sum_ite_mem,
      Finset.univ_inter, Pr_apply]
  rw [Var_eq_ip_sub_sq, hip, hEx]
  ring

/-! ## Conductance -/

/-- The **conductance** of a set `A`: the conditional probability that the chain
leaves `A` in one step, given that it starts in `A` distributed according to
`μ`.  Unlike the spectral gap this is a quantity one can estimate on a concrete
chain by counting. -/
noncomputable def conductance (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) : ℝ :=
  cut μ P A / Pr μ A

theorem conductance_apply (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    conductance μ P A = cut μ P A / Pr μ A := rfl

theorem conductance_nonneg (μ : FinDist Ω) (P : FinChain Ω) (A : Finset Ω) :
    0 ≤ conductance μ P A :=
  div_nonneg (cut_nonneg μ P A) (Pr_nonneg μ A)

/-- Conductance is a conditional probability, hence at most `1`. -/
theorem conductance_le_one (μ : FinDist Ω) (P : FinChain Ω) {A : Finset Ω}
    (hpos : 0 < Pr μ A) : conductance μ P A ≤ 1 := by
  rw [conductance_apply, div_le_one hpos]
  exact cut_le_Pr μ P A

/-! ## The easy direction of Cheeger's inequality

Instantiate the Poincaré inequality at the indicator of `A`.  The left-hand side
is `γ · Pr(A)(1 - Pr(A))` by `Var_indicator` and the right-hand side is
`cut μ P A` by `dirichlet_indicator`; that is the whole proof.  The hard
direction of Cheeger — a small gap forces a small cut — is not proved here and
is out of scope for this module. -/

/-- **A bottleneck bounds the gap, un-normalised form.**  If `P` is reversible
with respect to `μ` and has spectral gap at least `γ`, then for *every* set `A`

`γ · Pr(A) (1 - Pr(A)) ≤ cut μ P A`.

There is no constraint on `Pr(A)` and no sign condition on `γ`; this is simply
the Poincaré inequality read at `f = 1_A`, and it is the form a `Chains/` module
will apply. -/
theorem spectralGap_mul_le_cut {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hgap : SpectralGapAtLeast μ P γ) (A : Finset Ω) :
    γ * (Pr μ A * (1 - Pr μ A)) ≤ cut μ P A := by
  have h := hgap (fun x => if x ∈ A then (1 : ℝ) else 0)
  rwa [Var_indicator, dirichlet_indicator hrev] at h

/-- **The easy direction of Cheeger's inequality.**  Let `P` be reversible with
respect to `μ`, let `A` satisfy `0 < Pr(A) ≤ ½`, and suppose `P` has spectral
gap at least `γ ≥ 0`.  Then

`γ ≤ 2 Φ(A)`,

where `Φ(A) = conductance μ P A`.  A set with small conductance is a bottleneck,
and a bottleneck caps the gap; contrapositively (`not_spectralGapAtLeast_of_lt`)
exhibiting one bad cut certifies slow mixing.

The proof is the Poincaré inequality at `f = 1_A` together with
`1 - Pr(A) ≥ ½`.  No eigenvalue appears, and the only use of reversibility is
`flow_comm`. -/
theorem spectralGap_le_conductance {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : 0 ≤ γ)
    {A : Finset Ω} (hpos : 0 < Pr μ A) (hhalf : Pr μ A ≤ 1 / 2) :
    γ ≤ 2 * conductance μ P A := by
  have hcut := spectralGap_mul_le_cut hrev hgap A
  have hne : Pr μ A ≠ 0 := ne_of_gt hpos
  have hprod : 0 ≤ γ * Pr μ A * (1 - 2 * Pr μ A) :=
    mul_nonneg (mul_nonneg hγ hpos.le) (by linarith)
  have hmain : 0 ≤ 2 * cut μ P A - γ * Pr μ A := by nlinarith [hcut, hprod]
  have hdiv : 0 ≤ (2 * cut μ P A - γ * Pr μ A) / Pr μ A := div_nonneg hmain hpos.le
  have heq : (2 * cut μ P A - γ * Pr μ A) / Pr μ A = 2 * conductance μ P A - γ := by
    rw [conductance_apply]
    field_simp
  rw [heq] at hdiv
  linarith

/-- **The slow-mixing shape.**  If some set `A` with `0 < Pr(A) ≤ ½` has
conductance so small that `2 Φ(A) < γ`, then `P` does *not* satisfy the Poincaré
inequality with constant `γ`.  This is the contrapositive of
`spectralGap_le_conductance`, and it is how a bottleneck is turned into a lower
bound on mixing time. -/
theorem not_spectralGapAtLeast_of_lt {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hγ : 0 ≤ γ) {A : Finset Ω} (hpos : 0 < Pr μ A)
    (hhalf : Pr μ A ≤ 1 / 2) (hlt : 2 * conductance μ P A < γ) :
    ¬ SpectralGapAtLeast μ P γ := fun hgap =>
  absurd (spectralGap_le_conductance hrev hgap hγ hpos hhalf) (not_le.mpr hlt)

end Compl

end Arlib.MarkovChains
