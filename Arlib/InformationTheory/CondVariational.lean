/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Gibbs

/-!
# The conditional golden formula and the conditional variational bound

This is the conditional counterpart of `Variational.lean`, and it is what
query-complexity lower bounds actually consume. In those arguments one bounds the
information a *single* new answer `Z` reveals about the secret `X` *given* the
prefix `W` of answers already seen; the quantity to bound is therefore the
conditional mutual information `I(X ; Z | W)`, not `I(X ; Z)`.

Exactly as in the unconditional case, that conditional information is *an
average of Kullback–Leibler divergences*,

    `I(X ; Z | W) = ∑_{a, w} P_{X,W}(a, w) * KL(P_{Z | X = a, W = w} ‖ P_{Z | W = w})`,

and replacing the inner reference law `P_{Z | W = w}` by an *arbitrary* auxiliary
kernel `Q : βW → βZ → ℝ` only increases the average, the excess being the
nonnegative quantity `∑_w P_W(w) * KL(P_{Z | W = w} ‖ Q w)`. Hence for any kernel
`Q` whatsoever,

    `I(X ; Z | W) ≤ max over (a, w) of KL(P_{Z | X = a, W = w} ‖ Q w)`.

The point, again, is that `Q` is unconstrained: one picks whichever reference
kernel makes the conditional divergences easy to estimate — typically the law of
`Z` under a null model, which does not depend on `w` at all — and no optimality
of `Q` needs to be argued.

## Main results

* `Arlib.InformationTheory.condI_eq_sum_KL` — conditional mutual information as
  an average KL divergence.
* `Arlib.InformationTheory.sum_KL_eq_condI_add_sum_KL` — the conditional golden
  formula.
* `Arlib.InformationTheory.condI_le_of_KL_le` — the conditional variational upper
  bound, in the form lower-bound proofs consume.
* `Arlib.InformationTheory.condI_le_log_of_ratio_le` — the pointwise form: a
  bound `P_{Z | X = a, W = w}(b) ≤ r * Q w b` on the likelihood ratio gives
  `I(X ; Z | W) ≤ log r`.

## Implementation notes

There are three coordinates here rather than two, so the joint law lives on
`α × βZ × βW` and one has to be careful about *which* coordinate is being summed
out. The whole file is organised around a single fixed layout: the joint law is
always `dist P (pair X (pair Z W))` evaluated at `(a, b, w)`, and every triple sum
is written in the order `∑ a, ∑ w, ∑ b`. That layout is chosen so that the four
entropies produced by the computation,

    `-H(X, Z, W) + H(X, W) + H(Z, W) - H(W)`,

are literally the four entropies that `condI P X Z W` unfolds to — no relabelling
along `Equiv.prodAssoc` is needed anywhere.

Marginalising is then three lemmas: summing out `b` (the middle coordinate) gives
`dist P (pair X W)` and needs a direct argument from the definition of `dist`,
whereas summing out `a` (the first coordinate) is `dist_pair_marginal'` applied
with `pair Z W` in the second slot.

As in `Variational.lean`, the degenerate cells are split off first: the pointwise
identity behind the computation (`log_ratio_split`) is *unconditionally* true
because every term carries the joint law as a factor, and on the cells where that
factor is nonzero all five of `dist P (pair X W) (a, w)`, `dist P (pair Z W) (b, w)`,
`dist P W w` and the two conditional laws are nonzero, so `Real.log_div` applies
with no side conditions and the identity is `ring`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

variable {α β γ : Type}

/-! ### Reindexing laws

Two random variables that cut the sample space the same way have the same law.
This is the cheap way to move between the groupings `((X, W), Z)` — the one
`condDist P Z (pair X W)` is stated in — and `(X, (Z, W))` — the one all the sums
below are indexed by. -/

/-- Two laws agree at points with the same fibre. -/
private theorem dist_congr_of_iff {σ τ : Type} [DecidableEq σ] [DecidableEq τ]
    {P : FinProb} {X : P.Ω → σ} {Y : P.Ω → τ} {s : σ} {t : τ}
    (h : ∀ ω, X ω = s ↔ Y ω = t) : dist P X s = dist P Y t := by
  simp only [dist]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hx : X ω = s
  · rw [if_pos hx, if_pos ((h ω).mp hx)]
  · rw [if_neg hx, if_neg fun hc => hx ((h ω).mpr hc)]

/-- Regrouping the triple: `((X, W), Z)` at `((a, w), b)` is `(X, (Z, W))` at
`(a, b, w)`. -/
private theorem dist_reassoc [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (a : α) (b : β)
    (w : γ) :
    dist P (pair (pair X W) Z) ((a, w), b) = dist P (pair X (pair Z W)) (a, b, w) := by
  refine dist_congr_of_iff fun ω => ?_
  simp only [pair, Prod.mk.injEq]
  tauto

/-- Swapping a pair: `(W, Z)` at `(w, b)` is `(Z, W)` at `(b, w)`. -/
private theorem dist_swap [DecidableEq β] [DecidableEq γ]
    {P : FinProb} (Z : P.Ω → β) (W : P.Ω → γ) (b : β) (w : γ) :
    dist P (pair W Z) (w, b) = dist P (pair Z W) (b, w) := by
  refine dist_congr_of_iff fun ω => ?_
  simp only [pair, Prod.mk.injEq]
  tauto

/-- If the event `X = s` is contained in the event `Y = t`, the law of `X` at `s`
is dominated by the law of `Y` at `t`. -/
private theorem dist_le_dist_of_imp {σ τ : Type} [DecidableEq σ] [DecidableEq τ]
    {P : FinProb} (X : P.Ω → σ) (Y : P.Ω → τ) (s : σ) (t : τ)
    (h : ∀ ω, X ω = s → Y ω = t) : dist P X s ≤ dist P Y t := by
  simp only [dist]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hx : X ω = s
  · rw [if_pos hx, if_pos (h ω hx)]
  · rw [if_neg hx]
    by_cases hy : Y ω = t
    · rw [if_pos hy]; exact P.mass_nonneg ω
    · rw [if_neg hy]

/-! ### Marginalising the triple law -/

/-- Summing the law of `(X, Z, W)` over the *middle* coordinate gives the law of
`(X, W)`. This is not an instance of `dist_pair_marginal`, so it is proved
directly from the definition of `dist`. -/
private theorem sum_dist_triple_mid [DecidableEq α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ)
    (a : α) (w : γ) :
    ∑ b, dist P (pair X (pair Z W)) (a, b, w) = dist P (pair X W) (a, w) := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hx : X ω = a
  · by_cases hw : W ω = w
    · simp [hx, hw, Prod.ext_iff]
    · simp [hw, Prod.ext_iff]
  · simp [hx, Prod.ext_iff]

/-- Summing the law of `(X, Z, W)` over the first *two* coordinates gives the law
of `W`. -/
private theorem sum_dist_triple_fst_mid [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β)
    (W : P.Ω → γ) (w : γ) :
    ∑ a, ∑ b, dist P (pair X (pair Z W)) (a, b, w) = dist P W w := by
  have h : ∀ a : α, ∑ b, dist P (pair X (pair Z W)) (a, b, w)
      = dist P (pair X W) (a, w) := fun a => sum_dist_triple_mid X Z W a w
  simp only [h]
  exact dist_pair_marginal' X W w

/-! ### Entropy as a plain sum -/

/-- Entropy written without `Real.negMulLog`, which is the form the computation
below produces. -/
private theorem H_eq_neg_sum [Fintype α] [DecidableEq α] {P : FinProb}
    (X : P.Ω → α) : H P X = -∑ a, dist P X a * Real.log (dist P X a) := by
  rw [H_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Real.negMulLog_eq_neg]

/-! ### Non-degeneracy on a non-null cell -/

/-- On a non-null cell of the joint law of `(X, Z, W)`, all three marginals of
interest and both conditional laws are nonzero. This is what licenses the
unconditional use of `Real.log_div` below. -/
private theorem ne_zero_of_triple_ne_zero [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) (a : α) (b : β) (w : γ)
    (hJ : dist P (pair X (pair Z W)) (a, b, w) ≠ 0) :
    dist P (pair X W) (a, w) ≠ 0 ∧ dist P (pair Z W) (b, w) ≠ 0 ∧ dist P W w ≠ 0
      ∧ condDist P Z (pair X W) (a, w) b ≠ 0 ∧ condDist P Z W w b ≠ 0 := by
  have hpos : 0 < dist P (pair X (pair Z W)) (a, b, w) :=
    lt_of_le_of_ne (dist_nonneg _ _) (Ne.symm hJ)
  have hle_XW : dist P (pair X (pair Z W)) (a, b, w) ≤ dist P (pair X W) (a, w) :=
    dist_le_dist_of_imp _ _ _ _ fun ω hω => by
      simp only [pair, Prod.mk.injEq] at hω ⊢
      exact ⟨hω.1, hω.2.2⟩
  have hle_ZW : dist P (pair X (pair Z W)) (a, b, w) ≤ dist P (pair Z W) (b, w) :=
    dist_le_dist_of_imp _ _ _ _ fun ω hω => by
      simp only [pair, Prod.mk.injEq] at hω ⊢
      exact hω.2
  have hle_W : dist P (pair X (pair Z W)) (a, b, w) ≤ dist P W w :=
    dist_le_dist_of_imp _ _ _ _ fun ω hω => by
      simp only [pair, Prod.mk.injEq] at hω
      exact hω.2.2
  have hZW : dist P (pair Z W) (b, w) ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos hle_ZW)
  refine ⟨ne_of_gt (lt_of_lt_of_le hpos hle_XW), hZW,
    ne_of_gt (lt_of_lt_of_le hpos hle_W), ?_, ?_⟩
  · intro h
    exact hJ (by
      rw [← dist_reassoc X Z W a b w,
        dist_pair_eq_mul_condDist Z (pair X W) (a, w) b, h, mul_zero])
  · intro h
    refine hZW ?_
    have hWZ := dist_pair_eq_mul_condDist Z W w b
    rw [h, mul_zero, dist_swap Z W b w] at hWZ
    exact hWZ

/-! ### The two bridging computations -/

/-- The `(X, W)`-average of a conditional KL divergence against an arbitrary
kernel `Q`, rewritten as a triple sum against the joint law. This is the
conditional analogue of `Variational.lean`'s `sum_mul_KLdist_eq`. -/
private theorem sum_mul_KLdist_eq_cond [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ) :
    ∑ aw : α × γ, dist P (pair X W) aw *
        KLdist (condDist P Z (pair X W) aw) (Q aw.2)
      = ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z (pair X W) (a, w) b / Q w b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [KLdist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← dist_reassoc X Z W a b w, dist_pair_eq_mul_condDist Z (pair X W) (a, w) b]
  ring

/-- The pointwise splitting identity behind the whole file: on every cell,
`log (P_{Z|X,W} / P_{Z|W})` decomposes into the four log-terms whose joint-law
averages are the four entropies making up `condI`. The identity is
unconditional — on a null cell both sides vanish because every term carries the
joint law as a factor. -/
private theorem log_ratio_split [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) (a : α) (b : β) (w : γ) :
    dist P (pair X (pair Z W)) (a, b, w) *
        Real.log (condDist P Z (pair X W) (a, w) b / condDist P Z W w b)
      = dist P (pair X (pair Z W)) (a, b, w) *
            Real.log (dist P (pair X (pair Z W)) (a, b, w))
        - dist P (pair X (pair Z W)) (a, b, w) *
            Real.log (dist P (pair X W) (a, w))
        - dist P (pair X (pair Z W)) (a, b, w) *
            Real.log (dist P (pair Z W) (b, w))
        + dist P (pair X (pair Z W)) (a, b, w) * Real.log (dist P W w) := by
  by_cases hJ : dist P (pair X (pair Z W)) (a, b, w) = 0
  · simp [hJ]
  · obtain ⟨hXW, hZW, hW, hc1, hc2⟩ := ne_zero_of_triple_ne_zero X Z W a b w hJ
    have hc1eq : condDist P Z (pair X W) (a, w) b
        = dist P (pair X (pair Z W)) (a, b, w) / dist P (pair X W) (a, w) := by
      rw [← dist_reassoc X Z W a b w]
      simp [condDist, hXW]
    have hc2eq : condDist P Z W w b
        = dist P (pair Z W) (b, w) / dist P W w := by
      rw [← dist_swap Z W b w]
      simp [condDist, hW]
    rw [Real.log_div hc1 hc2, hc1eq, hc2eq, Real.log_div hJ hXW, Real.log_div hZW hW]
    ring

/-! ### The four joint-law averages -/

/-- Averaging `log` of the joint law against the joint law is minus the joint
entropy `H(X, Z, W)`. -/
private theorem sum_awb_log_joint [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) :
    ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
        Real.log (dist P (pair X (pair Z W)) (a, b, w))
      = -H P (pair X (pair Z W)) := by
  rw [H_eq_neg_sum, neg_neg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Averaging `log` of the `(X, W)` marginal against the joint law is minus
`H(X, W)`. -/
private theorem sum_awb_log_XW [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) :
    ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
        Real.log (dist P (pair X W) (a, w))
      = -H P (pair X W) := by
  rw [H_eq_neg_sum, neg_neg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_mul, sum_dist_triple_mid X Z W a w]

/-- Averaging `log` of the `(Z, W)` marginal against the joint law is minus
`H(Z, W)`. -/
private theorem sum_awb_log_ZW [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) :
    ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
        Real.log (dist P (pair Z W) (b, w))
      = -H P (pair Z W) := by
  calc ∑ a : α, ∑ w : γ, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P (pair Z W) (b, w))
      = ∑ a : α, ∑ b : β, ∑ w : γ, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P (pair Z W) (b, w)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b : β, ∑ a : α, ∑ w : γ, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P (pair Z W) (b, w)) := Finset.sum_comm
    _ = ∑ b : β, ∑ w : γ, ∑ a : α, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P (pair Z W) (b, w)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b : β, ∑ w : γ,
          dist P (pair Z W) (b, w) * Real.log (dist P (pair Z W) (b, w)) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_mul, dist_pair_marginal' X (pair Z W) (b, w)]
    _ = -H P (pair Z W) := by
        rw [H_eq_neg_sum, neg_neg, Fintype.sum_prod_type]

/-- Averaging `log` of the `W` marginal against the joint law is minus `H(W)`. -/
private theorem sum_awb_log_W [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) :
    ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) * Real.log (dist P W w)
      = -H P W := by
  rw [H_eq_neg_sum, neg_neg]
  calc ∑ a : α, ∑ w : γ, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P W w)
      = ∑ w : γ, ∑ a : α, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (dist P W w) := Finset.sum_comm
    _ = ∑ w : γ, dist P W w * Real.log (dist P W w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have h : ∑ a : α, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (dist P W w)
            = (∑ a : α, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w)) *
                Real.log (dist P W w) := by
          simp only [Finset.sum_mul]
        rw [h, sum_dist_triple_fst_mid X Z W w]

/-! ### Conditional mutual information as an average divergence -/

/-- **Conditional mutual information as an average KL divergence.** Averaging
over the pair `(X, W)`, the divergence from the law of `Z` given `(X, W)` to the
law of `Z` given `W` alone is exactly `I(X ; Z | W)`.

This is the conditional analogue of `I_eq_sum_KL`. -/
theorem condI_eq_sum_KL {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) :
    condI P X Z W = ∑ aw : α × γ, dist P (pair X W) aw *
      KLdist (condDist P Z (pair X W) aw) (condDist P Z W aw.2) := by
  rw [sum_mul_KLdist_eq_cond X Z W (condDist P Z W)]
  have hsplit :
      ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z (pair X W) (a, w) b / condDist P Z W w b)
        = (∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (dist P (pair X (pair Z W)) (a, b, w)))
          - (∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (dist P (pair X W) (a, w)))
          - (∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (dist P (pair Z W) (b, w)))
          + ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (dist P W w) := by
    simp only [log_ratio_split X Z W]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, sum_awb_log_joint X Z W, sum_awb_log_XW X Z W, sum_awb_log_ZW X Z W,
    sum_awb_log_W X Z W, condI_def, condH_def, condH_def, H₂_def, H₂_def]
  ring

/-- **The conditional golden formula.** Replacing the reference kernel
`P_{Z | W = w}` by an arbitrary kernel `Q` raises the `(X, W)`-average of the
conditional divergence by exactly `∑_w P_W(w) * KL(P_{Z | W = w} ‖ Q w)`, which is
nonnegative by Gibbs. This is the conditional analogue of `sum_KL_eq_I_add_KL`. -/
theorem sum_KL_eq_condI_add_sum_KL {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ)
    (hQ : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0) :
    ∑ aw : α × γ, dist P (pair X W) aw *
        KLdist (condDist P Z (pair X W) aw) (Q aw.2)
      = condI P X Z W + ∑ w, dist P W w * KLdist (condDist P Z W w) (Q w) := by
  rw [sum_mul_KLdist_eq_cond X Z W Q, condI_eq_sum_KL X Z W,
    sum_mul_KLdist_eq_cond X Z W (condDist P Z W)]
  have hsplit :
      ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z (pair X W) (a, w) b / Q w b)
        = (∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (condDist P Z (pair X W) (a, w) b / condDist P Z W w b))
          + ∑ a, ∑ w, ∑ b, dist P (pair X (pair Z W)) (a, b, w) *
              Real.log (condDist P Z W w b / Q w b) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun b _ => ?_
    by_cases hJ : dist P (pair X (pair Z W)) (a, b, w) = 0
    · simp [hJ]
    · obtain ⟨hXW, hZW, hW, hc1, hc2⟩ := ne_zero_of_triple_ne_zero X Z W a b w hJ
      rw [Real.log_div hc1 (hQ w b hc2), Real.log_div hc1 hc2,
        Real.log_div hc2 (hQ w b hc2)]
      ring
  rw [hsplit]
  congr 1
  calc ∑ a : α, ∑ w : γ, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z W w b / Q w b)
      = ∑ w : γ, ∑ a : α, ∑ b : β, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z W w b / Q w b) := Finset.sum_comm
    _ = ∑ w : γ, ∑ b : β, ∑ a : α, dist P (pair X (pair Z W)) (a, b, w) *
          Real.log (condDist P Z W w b / Q w b) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w : γ, ∑ b : β, dist P (pair Z W) (b, w) *
          Real.log (condDist P Z W w b / Q w b) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul, dist_pair_marginal' X (pair Z W) (b, w)]
    _ = ∑ w : γ, dist P W w * KLdist (condDist P Z W w) (Q w) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [KLdist, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← dist_swap Z W b w, dist_pair_eq_mul_condDist Z W w b]
        ring

/-- **The conditional variational upper bound.** This is the form the per-step
lower-bound argument consumes: choose any reference kernel `Q`, bound
`KL(P_{Z | X = a, W = w} ‖ Q w)` uniformly over the non-null cells `(a, w)`, and
the same bound holds for `I(X ; Z | W)`.

Conditional analogue of `I_le_of_KL_le`; the hypothesis `hQ0` is the same
absolute-continuity side condition, stated fibrewise. -/
theorem condI_le_of_KL_le {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb} (X : P.Ω → α)
    (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ) (hQ : ∀ w, IsProbDist (Q w))
    (hQ0 : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0) (c : ℝ)
    (h : ∀ a w, dist P (pair X W) (a, w) ≠ 0 →
      KLdist (condDist P Z (pair X W) (a, w)) (Q w) ≤ c) :
    condI P X Z W ≤ c := by
  have hgolden := sum_KL_eq_condI_add_sum_KL X Z W Q hQ0
  have hKL : 0 ≤ ∑ w, dist P W w * KLdist (condDist P Z W w) (Q w) := by
    refine Finset.sum_nonneg fun w _ => ?_
    by_cases hw : dist P W w = 0
    · simp [hw]
    · exact mul_nonneg (dist_nonneg _ _)
        (KLdist_nonneg (isProbDist_condDist Z W w hw) (hQ w)
          fun b hb => not_not.mp fun hne => hQ0 w b hne hb)
  have hbound : ∑ aw : α × γ, dist P (pair X W) aw *
        KLdist (condDist P Z (pair X W) aw) (Q aw.2)
      ≤ ∑ _aw : α × γ, dist P (pair X W) _aw * c := by
    refine Finset.sum_le_sum ?_
    rintro ⟨a, w⟩ -
    dsimp only
    by_cases haw : dist P (pair X W) (a, w) = 0
    · simp [haw]
    · exact mul_le_mul_of_nonneg_left (h a w haw) (dist_nonneg _ _)
  rw [← Finset.sum_mul, dist_sum, one_mul] at hbound
  linarith

/-! ### The pointwise form -/

/-- If `p` is dominated by `r` times `q` pointwise, with `r ≥ 1`, then
`KL(p ‖ q) ≤ log r`. This is monotonicity of `log` applied termwise, followed by
`∑ p = 1`; it is the step that turns a bound on a likelihood *ratio* into a bound
on a divergence. -/
private theorem KLdist_le_log_of_pointwise {β : Type} [Fintype β] {p q : β → ℝ}
    (hp : IsProbDist p) (hq : ∀ b, 0 ≤ q b) {r : ℝ} (hr : 1 ≤ r)
    (h : ∀ b, p b ≤ r * q b) : KLdist p q ≤ Real.log r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hterm : ∀ b, p b * Real.log (p b / q b) ≤ p b * Real.log r := by
    intro b
    rcases eq_or_lt_of_le (hp.nonneg b) with hpb | hpb
    · rw [← hpb]; simp
    · have hqb : 0 < q b := by
        rcases eq_or_lt_of_le (hq b) with h0 | h0
        · exact absurd (h b) (by rw [← h0, mul_zero]; exact not_le.mpr hpb)
        · exact h0
      have hdiv : p b / q b ≤ r :=
        div_le_of_le_mul₀ (hq b) (le_of_lt hr0) (h b)
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hpb hqb) hdiv) (le_of_lt hpb)
  calc KLdist p q = ∑ b, p b * Real.log (p b / q b) := rfl
    _ ≤ ∑ _b : β, p _b * Real.log r := Finset.sum_le_sum fun b _ => hterm b
    _ = Real.log r := by rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]

/-- **The pointwise conditional variational bound.** If the likelihood ratio of
the conditional law of `Z` against the reference kernel is bounded by `r ≥ 1`
pointwise — `P_{Z | X = a, W = w}(b) ≤ r * Q w b` for all `a`, `w`, `b` — then
`I(X ; Z | W) ≤ log r`.

This is exactly the shape a per-step query lower bound verifies: one exhibits `r`
by comparing a single answer's conditional law against a null model. -/
theorem condI_le_log_of_ratio_le {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ)
    (hQ : ∀ w, IsProbDist (Q w))
    (hQ0 : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0) {r : ℝ} (hr : 1 ≤ r)
    (h : ∀ a w b, condDist P Z (pair X W) (a, w) b ≤ r * Q w b) :
    condI P X Z W ≤ Real.log r :=
  condI_le_of_KL_le X Z W Q hQ hQ0 (Real.log r) fun a w haw =>
    KLdist_le_log_of_pointwise (isProbDist_condDist Z (pair X W) (a, w) haw)
      (hQ w).nonneg hr fun b => h a w b

end InformationTheory
end Arlib
