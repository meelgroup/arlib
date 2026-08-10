/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Submodular
import Arlib.InformationTheory.Entropy

/-!
# Support bounds on conditional entropy

A query lower bound argues that, conditioned on everything the algorithm has
seen, the hidden parameter is still confined to a set of at most `k` candidates,
so it retains at least — and at most — `log k` nats of uncertainty. The upper
half of that statement is `condH_le_log_of_support`, the main result of this
file. Alongside it sit the nonnegativity and monotonicity facts the same
argument consumes.

## Main results

* `Arlib.InformationTheory.condH_nonneg` — `0 ≤ H(X | Y)`.
* `Arlib.InformationTheory.I_le_H_left`, `Arlib.InformationTheory.I_le_H_right` —
  `I(X ; Y) ≤ H(X)` and `I(X ; Y) ≤ H(Y)`.
* `Arlib.InformationTheory.condI_le_condH` — `I(X ; Y | Z) ≤ H(X | Z)`.
* `Arlib.InformationTheory.condI_le_H_mid` — `I(X ; Y | Z) ≤ H(Y)`.
* `Arlib.InformationTheory.condH_le_log_of_support` — if every positive-probability
  value of `Y` is compatible with at most `k` values of `X`, then
  `H(X | Y) ≤ log k`.

## Implementation notes

`condH` is *defined* as `H(X, Y) - H(Y)`, so both the nonnegativity result and
the support bound are statements about the single sum

`∑ b, ((∑ a, negMulLog (dist (X, Y) (a, b))) - negMulLog (dist Y b))`,

and both are proved slicewise in `b`.

For nonnegativity the slice bound is termwise monotonicity of `log`: the joint
law is dominated by the marginal, `dist (X,Y) (a,b) ≤ dist Y b`, so
`-p log p ≥ -p log (dist Y b)`, and summing over `a` reassembles
`negMulLog (dist Y b)` on the right.

For the support bound the slice is handled by `sum_negMulLog_le_card`, an
unnormalised maximum-entropy bound over an arbitrary `Finset` rather than over
all of `α`. It is the same `log x ≤ x - 1` estimate as `Hdist_le_log_card`, with
`Fintype.card α` replaced by `s.card`; restricting to the support is what turns
`log (card α)` into `log k`. The `dist Y b = 0` slices contribute exactly `0`,
which is why the hypothesis only quantifies over the values of `Y` that actually
occur.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Domination of the joint law by a marginal -/

/-- The joint law is dominated by the law of the second coordinate. This is the
one-line consequence of marginalisation that the slicewise arguments below need;
`Submodular.lean` proves the same fact, but privately. -/
private lemma dist_pair_le_snd {α β : Type} [Fintype α] [DecidableEq α]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) (a : α) (b : β) :
    dist P (pair X Y) (a, b) ≤ dist P Y b := by
  rw [← dist_pair_marginal' X Y b]
  exact Finset.single_le_sum (f := fun a' : α => dist P (pair X Y) (a', b))
    (fun c _ => dist_nonneg _ _) (Finset.mem_univ a)

/-! ### Slicing a conditional entropy -/

/-- `H(X | Y)` written as a single sum over the values of `Y`, each slice being
the joint entropy sum of that slice minus the marginal's own term. Every result
in this file is a slicewise bound on this expression. -/
private lemma condH_eq_sum_slice {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    condH P X Y = ∑ b : β,
      ((∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b)))
        - Real.negMulLog (dist P Y b)) := by
  simp only [condH_def, H₂_def, H_def]
  have hjoint : ∑ t : α × β, Real.negMulLog (dist P (pair X Y) t)
      = ∑ b : β, ∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b)) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hjoint, ← Finset.sum_sub_distrib]

/-! ### Nonnegativity of conditional entropy -/

/-- The slice bound behind `condH_nonneg`: the entropy sum of a slice of the
joint law is at least the marginal's own `negMulLog` term.

Termwise, `dist (X,Y) (a,b) ≤ dist Y b` gives
`-p log p ≥ -p log (dist Y b)`, and the right-hand sides sum, over `a`, to
`negMulLog (dist Y b)` by marginalisation. -/
private lemma negMulLog_marginal_le {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) (b : β) :
    Real.negMulLog (dist P Y b)
      ≤ ∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b)) := by
  have hterm : ∀ a : α,
      -(dist P (pair X Y) (a, b)) * Real.log (dist P Y b)
        ≤ Real.negMulLog (dist P (pair X Y) (a, b)) := by
    intro a
    rcases eq_or_lt_of_le (dist_nonneg (pair X Y) (a, b)) with h0 | h0
    · rw [← h0, Real.negMulLog_zero]
      simp
    · have hneg : Real.negMulLog (dist P (pair X Y) (a, b))
          = -(dist P (pair X Y) (a, b) * Real.log (dist P (pair X Y) (a, b))) :=
        congrFun Real.negMulLog_eq_neg _
      have hlog : Real.log (dist P (pair X Y) (a, b)) ≤ Real.log (dist P Y b) :=
        Real.log_le_log h0 (dist_pair_le_snd X Y a b)
      rw [hneg]
      nlinarith
  have hrw : Real.negMulLog (dist P Y b)
      = ∑ a : α, -(dist P (pair X Y) (a, b)) * Real.log (dist P Y b) := by
    simp only [neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, dist_pair_marginal' X Y b,
      Real.negMulLog_eq_neg]
  rw [hrw]
  exact Finset.sum_le_sum fun a _ => hterm a

/-- Conditional entropy is nonnegative. -/
theorem condH_nonneg {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) : 0 ≤ condH P X Y := by
  rw [condH_eq_sum_slice X Y]
  refine Finset.sum_nonneg fun b _ => ?_
  linarith [negMulLog_marginal_le X Y b]

/-! ### Mutual information is dominated by either entropy -/

/-- Mutual information is at most the entropy of either argument. -/
theorem I_le_H_left {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) : I P X Y ≤ H P X := by
  rw [I_def]
  linarith [condH_nonneg X Y]

/-- Mutual information is at most the entropy of its second argument. This is
`I_le_H_left` transported across the symmetry of `I`, which in turn is the
symmetry of joint entropy (`H₂_comm`). -/
theorem I_le_H_right {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) : I P X Y ≤ H P Y := by
  have h1 : 0 ≤ condH P Y X := condH_nonneg Y X
  rw [condH_def, H₂_comm Y X] at h1
  rw [I_eq_add_sub]
  linarith

/-! ### Conditional mutual information -/

/-- Swapping the first two coordinates of a triple is a relabelling, so it leaves
entropy unchanged. -/
private lemma H_triple_swap {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    H P (pair X (pair Y Z)) = H P (pair Y (pair X Z)) := by
  have hinj : Function.Injective (fun t : α × β × γ => (t.2.1, t.1, t.2.2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h
    simp only [Prod.mk.injEq]
    exact ⟨h.2.1, h.1, h.2.2⟩
  have hfun :
      (fun ω => (fun t : α × β × γ => (t.2.1, t.1, t.2.2)) (pair X (pair Y Z) ω))
        = pair Y (pair X Z) := rfl
  rw [← hfun]
  exact (H_comp_of_injective (pair X (pair Y Z)) hinj).symm

/-- Conditional mutual information is at most the conditional entropy it refines. -/
theorem condI_le_condH {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) : condI P X Y Z ≤ condH P X Z := by
  rw [condI_def]
  linarith [condH_nonneg X (pair Y Z)]

/-- Conditional mutual information is at most the entropy of the new observation.

Unfolding, this is `I(X ; Y | Z) ≤ H(Y | Z) ≤ H(Y)`; the first step is the
inequality `H(X, Z) ≤ H(X, Y, Z)`, which is `condH_nonneg` for `Y` given
`(X, Z)` after regrouping the triple. -/
theorem condI_le_H_mid {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) : condI P X Y Z ≤ H P Y := by
  have h1 : 0 ≤ condH P Y (pair X Z) := condH_nonneg Y (pair X Z)
  rw [condH_def, H₂_def, ← H_triple_swap X Y Z] at h1
  have h2 : condH P Y Z ≤ H P Y := condH_le_H Y Z
  rw [condH_def, H₂_def] at h2
  simp only [condI_def, condH_def, H₂_def]
  linarith

/-! ### An unnormalised maximum-entropy bound over a `Finset`

`Hdist_le_log_card` bounds the entropy of a probability distribution on all of
`α`. The slices appearing in `condH_le_log_of_support` are neither normalised nor
spread over all of `α`: they have total mass `dist Y b` and live on the support,
whose size is the quantity the hypothesis controls. This is the corresponding
homogeneous, support-restricted bound, proved by the same `log x ≤ x - 1`
estimate applied to `S / (s.card * f a)`. -/

/-- **Unnormalised maximum-entropy bound over a `Finset`.** For a nonnegative `f`
with `∑ a ∈ s, f a = S` and `s` nonempty,

`∑ a ∈ s, negMulLog (f a) - negMulLog S ≤ S * log s.card`.

At `s = univ` and `S = 1` this is `Hdist_le_log_card`. -/
private theorem sum_negMulLog_le_card {α : Type} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (S : ℝ) (hS : ∑ a ∈ s, f a = S) (hs : s.Nonempty) :
    (∑ a ∈ s, Real.negMulLog (f a)) - Real.negMulLog S
      ≤ S * Real.log s.card := by
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun a _ => hf a
  have hN : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hN' : ((s.card : ℝ)) ≠ 0 := ne_of_gt hN
  rcases eq_or_lt_of_le hS0 with hz | hpos
  · -- Total mass zero: every term on `s` vanishes.
    have hall : ∀ a ∈ s, f a = 0 := fun a ha =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hf b).mp (hS.trans hz.symm) a ha
    have h1 : ∑ a ∈ s, Real.negMulLog (f a) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [hall a ha, Real.negMulLog_zero]
    rw [h1, ← hz]
    simp
  · -- Positive total mass: the termwise estimate.
    have hterm : ∀ a ∈ s,
        Real.negMulLog (f a) - f a * Real.log s.card + f a * Real.log S
          ≤ S / (s.card : ℝ) - f a := by
      intro a _
      rcases eq_or_lt_of_le (hf a) with h0 | h0
      · rw [← h0, Real.negMulLog_zero]
        have : (0 : ℝ) ≤ S / (s.card : ℝ) := div_nonneg hS0 (le_of_lt hN)
        linarith
      · have hkey : Real.log (S / ((s.card : ℝ) * f a))
            ≤ S / ((s.card : ℝ) * f a) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hrw : Real.negMulLog (f a) - f a * Real.log s.card + f a * Real.log S
            = f a * Real.log (S / ((s.card : ℝ) * f a)) := by
          rw [Real.negMulLog_eq_neg, Real.log_div (ne_of_gt hpos) (by positivity),
            Real.log_mul hN' (ne_of_gt h0)]
          ring
        have hmul : f a * Real.log (S / ((s.card : ℝ) * f a))
            ≤ f a * (S / ((s.card : ℝ) * f a) - 1) :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt h0)
        have hval : f a * (S / ((s.card : ℝ) * f a) - 1) = S / (s.card : ℝ) - f a := by
          field_simp
          ring
        rw [hrw]
        linarith
    have hsum := Finset.sum_le_sum hterm
    have hL : ∑ a ∈ s, (Real.negMulLog (f a) - f a * Real.log s.card
          + f a * Real.log S)
        = (∑ a ∈ s, Real.negMulLog (f a)) - S * Real.log s.card + S * Real.log S := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, hS]
    have hR : ∑ _a ∈ s, (S / (s.card : ℝ) - f _a) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul]
      field_simp
    rw [hL, hR] at hsum
    have hneg : Real.negMulLog S = -(S * Real.log S) :=
      congrFun Real.negMulLog_eq_neg S
    rw [hneg]
    linarith

/-- The support-restricted form of `sum_negMulLog_le_card`: only the values on
which `f` is nonzero contribute, so a bound on the size of that support bounds
the whole sum. Stated with the support given as an abstract `Finset` `s` together
with its membership characterisation, which keeps the caller free of
decidability bookkeeping. -/
private lemma sum_negMulLog_le_of_support {α : Type} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (S : ℝ) (hS : ∑ a, f a = S) (hS0 : S ≠ 0)
    (k : ℕ) (s : Finset α) (hmem : ∀ a, a ∈ s ↔ f a ≠ 0) (hcard : s.card ≤ k) :
    (∑ a : α, Real.negMulLog (f a)) - Real.negMulLog S ≤ S * Real.log k := by
  have hoff : ∀ a ∈ (Finset.univ : Finset α), a ∉ s → f a = 0 := by
    intro a _ ha
    by_contra hne
    exact ha ((hmem a).mpr hne)
  have hsum_s : ∑ a ∈ s, f a = S :=
    (Finset.sum_subset (Finset.subset_univ s) hoff).trans hS
  have hrestrict : ∑ a : α, Real.negMulLog (f a) = ∑ a ∈ s, Real.negMulLog (f a) :=
    (Finset.sum_subset (Finset.subset_univ s) fun a ha hb => by
      rw [hoff a ha hb, Real.negMulLog_zero]).symm
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hS0
    rw [← hsum_s, he, Finset.sum_empty]
  have hlog : Real.log s.card ≤ Real.log k := by
    refine Real.log_le_log ?_ ?_
    · exact_mod_cast Finset.card_pos.mpr hne
    · exact_mod_cast hcard
  have hS0' : 0 ≤ S := hS ▸ Finset.sum_nonneg fun a _ => hf a
  rw [hrestrict]
  exact le_trans (sum_negMulLog_le_card s f hf S hsum_s hne)
    (mul_le_mul_of_nonneg_left hlog hS0')

/-! ### The support bound -/

/-- **Support bound on conditional entropy.** If, for every value `b` of `Y` that
occurs with positive probability, the values of `X` compatible with it number at
most `k`, then `X` retains at most `log k` nats of uncertainty given `Y`.

The proof is slicewise. A slice with `dist Y b = 0` contributes exactly `0`,
because the joint law is dominated by the marginal and therefore vanishes there.
A slice with `dist Y b ≠ 0` is bounded by `dist Y b * log k` using the
support-restricted maximum-entropy bound. Summing and using `∑ b, dist Y b = 1`
gives `log k`. -/
theorem condH_le_log_of_support {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) (k : ℕ) (hk : 0 < k)
    (hsupp : ∀ b : β, dist P Y b ≠ 0 →
      ((Finset.univ.filter (fun a : α => dist P (pair X Y) (a, b) ≠ 0)).card ≤ k)) :
    condH P X Y ≤ Real.log k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hslice : ∀ b : β,
      ((∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b)))
        - Real.negMulLog (dist P Y b)) ≤ dist P Y b * Real.log k := by
    intro b
    by_cases hb : dist P Y b = 0
    · -- The whole slice of the joint law vanishes.
      have hall : ∀ a : α, dist P (pair X Y) (a, b) = 0 := by
        intro a
        have hle := dist_pair_le_snd X Y a b
        rw [hb] at hle
        exact le_antisymm hle (dist_nonneg _ _)
      simp [hall, hb, Real.negMulLog_zero]
    · refine sum_negMulLog_le_of_support (fun a : α => dist P (pair X Y) (a, b))
        (fun a => dist_nonneg _ _) (dist P Y b) (dist_pair_marginal' X Y b) hb k
        (Finset.univ.filter (fun a : α => dist P (pair X Y) (a, b) ≠ 0))
        (fun a => by simp) (hsupp b hb)
  rw [condH_eq_sum_slice X Y]
  refine le_trans (Finset.sum_le_sum fun b _ => hslice b) ?_
  rw [← Finset.sum_mul, dist_sum, one_mul]

end InformationTheory
end Arlib
