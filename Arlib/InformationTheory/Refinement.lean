/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Basic

/-!
# Bounds on a conditional law descend from any refinement of the conditioning

An adaptive lower-bound argument computes the law of the next observation given
*everything the process has done so far* — every coin, every internal draw — because that is
the only level at which the law has a closed form. What the information-theoretic bound then
consumes is the law of the next observation given only the *public transcript*, which is a
coarsening: many coin histories produce the same transcript.

Passing from the fine conditioning to the coarse one is usually described as an obstruction,
on the grounds that the fine conditional laws differ from cell to cell and so "do not
collapse to a single law". They do not have to. The coarse conditional law is a **convex
mixture** of the fine ones, with weights the conditional masses of the cells, and every
bound of the two shapes an argument of this kind actually uses — a pointwise upper bound
`p(z) ≤ c`, and an upper bound `∑_{z ∈ B} p(z) ≤ δ` on the mass of a set of outcomes — is
preserved by convex mixtures. So a bound proved uniformly over the fine cells descends to
the coarse conditioning for free.

That is the content of this file. It is elementary; it is recorded because the mistake it
prevents is not.

## Setup

`W : P.Ω → ι` is the fine conditioning variable (the full history), `g : ι → α` a statistic
of it, and `fun ω => g (W ω)` the coarse conditioning variable (the public transcript). `Z`
is the observation.

## Main results

* `dist_comp_eq_sum_fiber`, `dist_pair_comp_eq_sum_fiber` — the coarse law is the sum of the
  fine laws over the fibre `g⁻¹(a)`.
* `dist_pair_comp_eq_sum_mul_condDist` — **the mixture identity**: the coarse joint law is
  `∑_{u ∈ g⁻¹(a)} P(W = u) · P(Z = b | W = u)`.
* `condDist_comp_le` — **the payoff**: a pointwise bound `P(Z = b | W = u) ≤ c` holding for
  every reachable `u` in the fibre gives `P(Z = b | g(W) = a) ≤ c`.
* `condDist_comp_sum_le` — the same for the mass of a set `B` of outcomes, which is the form
  a "the exceptional letters carry mass at most `δ`" step needs.
* `condDist_comp_le_of_exceptional` — the version with an exceptional set of *cells*: if the
  bound is only known on the cells outside `Bad`, the conclusion picks up
  `P(W ∈ Bad, g(W) = a) / P(g(W) = a)`. This is what one gets when the fine bound holds only
  on a good event of the process's own randomness.

## Scope

Nothing here says the fine conditional laws resemble each other, and nothing here transfers
a *lower* bound: a mixture can only be pushed up by its largest component, so a lower bound
on every cell does descend (by the same argument with the inequality reversed) but a
two-sided estimate does not become a two-sided estimate on the mixture with the same
constants unless both directions are assumed. Only the upper-bound direction is proved here,
because it is the one that is used.
-/

open scoped BigOperators
open Arlib.Probability

namespace Arlib

namespace InformationTheory

variable {α β ι : Type} {P : FinProb}

section

variable [DecidableEq α] [DecidableEq β] [DecidableEq ι] [Fintype ι]

/-- The coarse law is the sum of the fine laws over the fibre. -/
theorem dist_comp_eq_sum_fiber (W : P.Ω → ι) (g : ι → α) (a : α) :
    dist P (fun ω => g (W ω)) a
      = ∑ u ∈ Finset.univ.filter (fun u => g u = a), dist P W u := by
  simp only [dist]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun u => g u = a)) (W ω) (fun _ => P.mass ω)]
  simp [Finset.mem_filter]

/-- The coarse *joint* law is the sum of the fine joint laws over the fibre. -/
theorem dist_pair_comp_eq_sum_fiber (Z : P.Ω → β) (W : P.Ω → ι) (g : ι → α) (a : α) (b : β) :
    dist P (pair (fun ω => g (W ω)) Z) (a, b)
      = ∑ u ∈ Finset.univ.filter (fun u => g u = a), dist P (pair W Z) (u, b) := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hz : Z ω = b
  · have hcongr : ∀ u ∈ Finset.univ.filter (fun u => g u = a),
        (if (W ω, Z ω) = (u, b) then P.mass ω else 0)
          = (if W ω = u then P.mass ω else 0) := by
      intro u _
      by_cases hw : W ω = u
      · rw [if_pos (by rw [hw, hz]), if_pos hw]
      · rw [if_neg (by simp [Prod.ext_iff, hw]), if_neg hw]
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_ite_eq (Finset.univ.filter (fun u => g u = a)) (W ω) (fun _ => P.mass ω)]
    simp [Finset.mem_filter, hz, Prod.ext_iff]
  · rw [if_neg (by simp [Prod.ext_iff, hz])]
    exact (Finset.sum_eq_zero fun u _ => if_neg (by simp [Prod.ext_iff, hz])).symm

/-- **The mixture identity.** The coarse joint law is a nonnegative combination of the fine
conditional laws, with weights the fine marginal masses. Everything else in this file is a
corollary. -/
theorem dist_pair_comp_eq_sum_mul_condDist (Z : P.Ω → β) (W : P.Ω → ι) (g : ι → α)
    (a : α) (b : β) :
    dist P (pair (fun ω => g (W ω)) Z) (a, b)
      = ∑ u ∈ Finset.univ.filter (fun u => g u = a), dist P W u * condDist P Z W u b := by
  rw [dist_pair_comp_eq_sum_fiber]
  exact Finset.sum_congr rfl fun u _ => dist_pair_eq_mul_condDist Z W u b

/-- **A pointwise upper bound on the conditional law descends to any coarsening.**

If, for every reachable value `u` of the fine conditioning variable compatible with the
coarse value `a`, the conditional probability of the outcome `b` is at most `c`, then the
same holds after coarsening. No relation between the fine cells is needed: the coarse law is
their convex mixture.

The hypothesis `0 ≤ c` is used only on the null cell `P(g(W) = a) = 0`, where `condDist` is
`0` by convention. -/
theorem condDist_comp_le (Z : P.Ω → β) (W : P.Ω → ι) (g : ι → α) (a : α) (b : β) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ u, g u = a → dist P W u ≠ 0 → condDist P Z W u b ≤ c) :
    condDist P Z (fun ω => g (W ω)) a b ≤ c := by
  by_cases ha : dist P (fun ω => g (W ω)) a = 0
  · rw [condDist, if_pos ha]; exact hc
  · have hapos : 0 < dist P (fun ω => g (W ω)) a :=
      lt_of_le_of_ne (dist_nonneg _ _) (Ne.symm ha)
    have hnum : dist P (pair (fun ω => g (W ω)) Z) (a, b)
        ≤ c * dist P (fun ω => g (W ω)) a := by
      rw [dist_pair_comp_eq_sum_mul_condDist, dist_comp_eq_sum_fiber, Finset.mul_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      have hg : g u = a := (Finset.mem_filter.mp hu).2
      by_cases hw : dist P W u = 0
      · rw [hw]; simp
      · rw [mul_comm c (dist P W u)]
        exact mul_le_mul_of_nonneg_left (h u hg hw) (dist_nonneg _ _)
    rw [condDist, if_neg ha, div_le_iff₀ hapos]
    exact hnum

/-- **An upper bound on the mass of a set of outcomes descends to any coarsening.** This is
the form used when a "middle regime" of outcomes has to be shown to carry small conditional
mass: proving it for every fine history proves it for the public transcript. -/
theorem condDist_comp_sum_le (Z : P.Ω → β) (W : P.Ω → ι) (g : ι → α) (a : α) (B : Finset β)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ u, g u = a → dist P W u ≠ 0 → ∑ b ∈ B, condDist P Z W u b ≤ δ) :
    ∑ b ∈ B, condDist P Z (fun ω => g (W ω)) a b ≤ δ := by
  by_cases ha : dist P (fun ω => g (W ω)) a = 0
  · have hzero : ∀ b ∈ B, condDist P Z (fun ω => g (W ω)) a b = 0 := by
      intro b _; rw [condDist, if_pos ha]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact hδ
  · have hapos : 0 < dist P (fun ω => g (W ω)) a :=
      lt_of_le_of_ne (dist_nonneg _ _) (Ne.symm ha)
    have hsum : ∑ b ∈ B, condDist P Z (fun ω => g (W ω)) a b
        = (∑ b ∈ B, dist P (pair (fun ω => g (W ω)) Z) (a, b))
            / dist P (fun ω => g (W ω)) a := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by rw [condDist, if_neg ha]
    rw [hsum, div_le_iff₀ hapos]
    have hstep : ∑ b ∈ B, dist P (pair (fun ω => g (W ω)) Z) (a, b)
        = ∑ u ∈ Finset.univ.filter (fun u => g u = a),
            dist P W u * ∑ b ∈ B, condDist P Z W u b := by
      rw [Finset.sum_congr rfl fun b _ => dist_pair_comp_eq_sum_mul_condDist Z W g a b,
        Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    rw [hstep, dist_comp_eq_sum_fiber, Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have hg : g u = a := (Finset.mem_filter.mp hu).2
    by_cases hw : dist P W u = 0
    · rw [hw]; simp
    · rw [mul_comm δ (dist P W u)]
      exact mul_le_mul_of_nonneg_left (h u hg hw) (dist_nonneg _ _)

/-- The joint law of a pair is at most the marginal law of the first coordinate: the event
`{X = a, Z = b}` is contained in `{X = a}`. Stated here because the `Fintype β`-free form is
what the exceptional-set lemma needs. -/
private theorem dist_pair_le_dist (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    dist P (pair X Z) (a, b) ≤ dist P X a := by
  simp only [dist, pair]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases h1 : X ω = a
  · by_cases h2 : Z ω = b <;> simp [h1, h2, P.mass_nonneg ω]
  · simp [h1, Prod.ext_iff]

/-- A conditional probability is at most `1`. -/
private theorem condDist_le_one_aux (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    condDist P Z X a b ≤ 1 := by
  rw [condDist]
  split
  · norm_num
  · rename_i ha
    exact div_le_one_of_le₀ (dist_pair_le_dist Z X a b) (dist_nonneg _ _)

/-- **The version with an exceptional set of cells.**

In practice a fine-history bound is available only on a good event of the process's own
randomness — the histories on which a concentration lemma holds. Then the coarse conditional
probability exceeds `c` by at most the conditional mass of the bad cells. Nothing is assumed
about the bad cells beyond `condDist ≤ 1`, which always holds. -/
theorem condDist_comp_le_of_exceptional (Z : P.Ω → β) (W : P.Ω → ι) (g : ι → α) (a : α)
    (b : β) (Bad : Finset ι) {c : ℝ} (hc : 0 ≤ c)
    (ha : dist P (fun ω => g (W ω)) a ≠ 0)
    (h : ∀ u, g u = a → dist P W u ≠ 0 → u ∉ Bad → condDist P Z W u b ≤ c) :
    condDist P Z (fun ω => g (W ω)) a b
      ≤ c + (∑ u ∈ Bad, dist P W u) / dist P (fun ω => g (W ω)) a := by
  have hapos : 0 < dist P (fun ω => g (W ω)) a :=
    lt_of_le_of_ne (dist_nonneg _ _) (Ne.symm ha)
  have hnum : dist P (pair (fun ω => g (W ω)) Z) (a, b)
      ≤ c * dist P (fun ω => g (W ω)) a + ∑ u ∈ Bad, dist P W u := by
    rw [dist_pair_comp_eq_sum_mul_condDist, dist_comp_eq_sum_fiber, Finset.mul_sum]
    have hsplit : ∀ u ∈ Finset.univ.filter (fun u => g u = a),
        dist P W u * condDist P Z W u b
          ≤ c * dist P W u + (if u ∈ Bad then dist P W u else 0) := by
      intro u hu
      have hg : g u = a := (Finset.mem_filter.mp hu).2
      by_cases hbad : u ∈ Bad
      · rw [if_pos hbad]
        have h1 : dist P W u * condDist P Z W u b ≤ dist P W u * 1 :=
          mul_le_mul_of_nonneg_left (condDist_le_one_aux Z W u b) (dist_nonneg _ _)
        have h2 : 0 ≤ c * dist P W u := mul_nonneg hc (dist_nonneg _ _)
        rw [mul_one] at h1
        linarith
      · rw [if_neg hbad, add_zero]
        by_cases hw : dist P W u = 0
        · rw [hw]; simp
        · rw [mul_comm c (dist P W u)]
          exact mul_le_mul_of_nonneg_left (h u hg hw hbad) (dist_nonneg _ _)
    refine le_trans (Finset.sum_le_sum hsplit) ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add_left ?_ _
    calc ∑ u ∈ Finset.univ.filter (fun u => g u = a), (if u ∈ Bad then dist P W u else 0)
        ≤ ∑ u : ι, (if u ∈ Bad then dist P W u else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ => ?_
          split <;> [exact dist_nonneg _ _; exact le_refl 0]
      _ = ∑ u ∈ Bad, dist P W u := by
          rw [← Finset.sum_filter]
          exact Finset.sum_congr (by ext u; simp) fun _ _ => rfl
  rw [condDist, if_neg ha, div_le_iff₀ hapos, add_mul, div_mul_cancel₀ _ (ne_of_gt hapos)]
  linarith [hnum]

/-! ### The form the variational bound consumes

`Arlib.InformationTheory.condI_le_log_add_of_ratio_le_on` and its `_of_mass_le` companion
take their hypotheses conditioned on `pair X W` — the source variable together with the
*public* history. These two corollaries discharge exactly those hypotheses from the
corresponding statements about a refinement `V` of the pair, which is where an adaptive
process actually has a closed form for its next-step law. -/

section Pair

/-- **The `hgood` hypothesis descends from a refinement.** If `V` refines the pair `(X, W)`
via `g`, a pointwise ratio bound proved for every reachable value of `V` gives the same
bound conditioned on `(X, W)`. -/
theorem condDist_pair_le_of_refine {γ : Type} [DecidableEq γ]
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (V : P.Ω → ι) (g : ι → α × γ)
    (hVg : ∀ ω, g (V ω) = (X ω, W ω)) (a : α) (w : γ) (b : β) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, g v = (a, w) → dist P V v ≠ 0 → condDist P Z V v b ≤ c) :
    condDist P Z (pair X W) (a, w) b ≤ c := by
  have hfun : pair X W = fun ω => g (V ω) := funext fun ω => (hVg ω).symm
  rw [hfun]
  exact condDist_comp_le Z V g (a, w) b hc h

/-- **The `hmass` hypothesis descends from a refinement.** The same for the conditional mass
of a set of outcomes — the "exceptional letters are rare" step. -/
theorem condDist_pair_sum_le_of_refine {γ : Type} [DecidableEq γ]
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (V : P.Ω → ι) (g : ι → α × γ)
    (hVg : ∀ ω, g (V ω) = (X ω, W ω)) (a : α) (w : γ) (B : Finset β) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ v, g v = (a, w) → dist P V v ≠ 0 → ∑ b ∈ B, condDist P Z V v b ≤ δ) :
    ∑ b ∈ B, condDist P Z (pair X W) (a, w) b ≤ δ := by
  have hfun : pair X W = fun ω => g (V ω) := funext fun ω => (hVg ω).symm
  rw [hfun]
  exact condDist_comp_sum_le Z V g (a, w) B hδ h

end Pair

end

end InformationTheory

end Arlib
