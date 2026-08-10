/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Submodular
import Arlib.InformationTheory.Uniform

/-!
# Fano's inequality

Fano's inequality is the converse half of the source-coding picture, and the tool
that turns an information bound into a *query* lower bound: if an estimate `X̂`
of a hidden parameter `X` carries little information about `X`, then it must be
wrong often.

The error event itself — `Arlib.Probability.errIndicator X Xhat`, the
`Bool`-valued indicator of `X ≠ X̂`, and `Arlib.Probability.errProb X Xhat`, its
probability — carries no information-theoretic content and lives in
`Arlib.Probability.Law`; both are re-exported by `Arlib.InformationTheory.Basic`
under their old `Arlib.InformationTheory` spellings.

## Main results

* `Arlib.InformationTheory.fano_condH_le` — `H(X | X̂) ≤ log 2 + Pe · log |α|`.
* `Arlib.InformationTheory.fano_errProb_ge` — the same, solved for `Pe`.
* `Arlib.InformationTheory.fano_uniform` — for uniform `X`,
  `Pe ≥ 1 - (I(X ; X̂) + log 2) / log |α|`.

## Implementation notes

The argument is the textbook one, split into three independent pieces.

*Bookkeeping.* Writing `E` for the error indicator, `E` is a function of the pair
`(X, X̂)`, so `H(X, E, X̂) = H(X, X̂)`; since `condH` is *defined* as a difference
of entropies, this turns into the exact identity

`H(X | X̂) = H(X | E, X̂) + H(E | X̂)`

with no inequality reasoning at all (`condH_split`). The second term is at most
`H(E) ≤ log 2` by `condH_le_H` and `H_bool_le_log_two`.

*The quantitative step.* `H(X | E, X̂) ≤ Pe · log |α|` is proved directly from the
definition rather than through a conditional-distribution API. Unfolding, the
left-hand side is a single sum over the value `b` of the conditioning variable of

`(∑ a, negMulLog (dist (X, Y) (a, b))) - negMulLog (dist Y b)`,

and it suffices to bound that slicewise. On the slices where no error occurred
`X` is *determined* by the conditioning variable, so the slice sum collapses to a
single term and the contribution is exactly `0`; on the remaining slices the
generic bound `sum_negMulLog_le` — an unnormalised form of the maximum-entropy
bound, proved by the same `log x ≤ x - 1` estimate as `Hdist_le_log_card` — gives
`dist Y b · log |α|`. Summing the surviving slices reproduces `Pe`.

This is packaged as `condH_le_of_det`, which is stated for an arbitrary
conditioning variable `Y`, an arbitrary `Bool`-valued "bad slice" predicate and
an arbitrary reconstruction map; Fano is the instance where `Y = (E, X̂)`, the
bad slices are the ones with `E = 1`, and the reconstruction is `X̂` itself.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### An unnormalised maximum-entropy bound

`Hdist_le_log_card` bounds the entropy of a *probability* distribution. The slice
sums appearing below are not normalised — they have total mass `dist Y b` rather
than `1` — so we need the homogeneous form of that bound. It is proved by exactly
the argument of `Hdist_le_log_card`: the termwise estimate `log x ≤ x - 1` applied
to `S / (N * f a)`, whose bounds sum to zero. -/

/-- **Unnormalised maximum-entropy bound.** For a nonnegative `f : α → ℝ` with
total mass `S`,

`∑ a, negMulLog (f a) - negMulLog S ≤ S * log (card α)`.

At `S = 1` this is `Hdist_le_log_card`; the general case is the same statement
scaled by `S`. -/
private theorem sum_negMulLog_le {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (S : ℝ) (hS : ∑ a, f a = S) :
    (∑ a, Real.negMulLog (f a)) - Real.negMulLog S
      ≤ S * Real.log (Fintype.card α) := by
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun a _ => hf a
  have hN : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := α)
  have hN' : ((Fintype.card α : ℝ)) ≠ 0 := ne_of_gt hN
  rcases eq_or_lt_of_le hS0 with hz | hpos
  · -- Total mass zero: every term vanishes.
    have hall : ∀ a, f a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hf b).mp (hS.trans hz.symm) a
        (Finset.mem_univ a)
    simp [hall, ← hz]
  · -- Positive total mass: the termwise estimate.
    have hterm : ∀ a : α,
        Real.negMulLog (f a) - f a * Real.log (Fintype.card α) + f a * Real.log S
          ≤ S / (Fintype.card α : ℝ) - f a := by
      intro a
      rcases eq_or_lt_of_le (hf a) with h0 | h0
      · rw [← h0, Real.negMulLog_zero]
        have : (0 : ℝ) ≤ S / (Fintype.card α : ℝ) := div_nonneg hS0 (le_of_lt hN)
        linarith
      · have hkey : Real.log (S / ((Fintype.card α : ℝ) * f a))
            ≤ S / ((Fintype.card α : ℝ) * f a) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hrw : Real.negMulLog (f a) - f a * Real.log (Fintype.card α)
              + f a * Real.log S
            = f a * Real.log (S / ((Fintype.card α : ℝ) * f a)) := by
          rw [Real.negMulLog_eq_neg, Real.log_div (ne_of_gt hpos) (by positivity),
            Real.log_mul hN' (ne_of_gt h0)]
          ring
        have hmul : f a * Real.log (S / ((Fintype.card α : ℝ) * f a))
            ≤ f a * (S / ((Fintype.card α : ℝ) * f a) - 1) :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt h0)
        have hval : f a * (S / ((Fintype.card α : ℝ) * f a) - 1)
            = S / (Fintype.card α : ℝ) - f a := by
          field_simp
          ring
        rw [hrw]
        linarith
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hterm a)
    have hL : ∑ a : α, (Real.negMulLog (f a) - f a * Real.log (Fintype.card α)
          + f a * Real.log S)
        = (∑ a, Real.negMulLog (f a)) - S * Real.log (Fintype.card α)
          + S * Real.log S := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, hS]
    have hR : ∑ _a : α, (S / (Fintype.card α : ℝ) - f _a) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hS,
        nsmul_eq_mul]
      field_simp
    rw [hL, hR] at hsum
    have hneg : Real.negMulLog S = -(S * Real.log S) :=
      congrFun Real.negMulLog_eq_neg S
    rw [hneg]
    linarith

/-! ### Conditional entropy under partial determinism -/

/-- If the conditioning variable `Y` *determines* `X` off a distinguished set of
"bad" values, then `H(X | Y)` is at most the probability of landing in a bad
value, times `log (card α)`.

This is the quantitative heart of Fano's inequality. The proof unfolds `condH`
into a single sum over the values `b` of `Y` and bounds it slicewise: a good
slice contributes exactly `0` (the slice law is a point mass), and a bad slice is
bounded by `sum_negMulLog_le`. -/
private theorem condH_le_of_det {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β)
    (bad : β → Bool) (rec : β → α)
    (hdet : ∀ ω, bad (Y ω) = false → X ω = rec (Y ω)) :
    condH P X Y
      ≤ (∑ b, if bad b = true then dist P Y b else 0) * Real.log (Fintype.card α) := by
  -- Unfold both entropies into sums.
  simp only [condH_def, H₂_def, H_def]
  have hjoint : ∑ t : α × β, Real.negMulLog (dist P (pair X Y) t)
      = ∑ b : β, ∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b)) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hjoint, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  cases hbb : bad b with
  | true =>
      -- A bad slice: the unnormalised maximum-entropy bound.
      rw [if_pos (rfl : (true : Bool) = true)]
      exact sum_negMulLog_le (fun a => dist P (pair X Y) (a, b))
        (fun a => dist_nonneg _ _) (dist P Y b) (dist_pair_marginal' X Y b)
  | false =>
      -- A good slice: `X` is determined, so the slice law is a point mass.
      have hzero : ∀ a : α, a ≠ rec b → dist P (pair X Y) (a, b) = 0 := by
        intro a ha
        simp only [dist]
        refine Finset.sum_eq_zero fun ω _ => ?_
        by_cases hc : pair X Y ω = (a, b)
        · exfalso
          have hY : Y ω = b := congrArg Prod.snd hc
          have hX : X ω = a := congrArg Prod.fst hc
          have hd := hdet ω (by rw [hY]; exact hbb)
          rw [hY, hX] at hd
          exact ha hd
        · rw [if_neg hc]
      have hmarg : dist P (pair X Y) (rec b, b) = dist P Y b := by
        rw [← dist_pair_marginal' X Y b]
        refine (Finset.sum_eq_single (rec b) (fun a _ ha => hzero a ha) ?_).symm
        intro hm
        exact absurd (Finset.mem_univ (rec b)) hm
      have hsingle : ∑ a : α, Real.negMulLog (dist P (pair X Y) (a, b))
          = Real.negMulLog (dist P Y b) := by
        rw [← hmarg]
        refine Finset.sum_eq_single (rec b) (fun a _ ha => ?_) ?_
        · rw [hzero a ha, Real.negMulLog_zero]
        · intro hm
          exact absurd (Finset.mem_univ (rec b)) hm
      rw [hsingle, if_neg (by simp : ¬ ((false : Bool) = true)), zero_mul, sub_self]

/-! ### Step 1: the error indicator is a function of the pair -/

/-- Adjoining the error indicator to `(X, X̂)` adds nothing: the triple
`(X, E, X̂)` is `(X, X̂)` relabelled by the injection `(a, b) ↦ (a, (a ≠ b, b))`. -/
private theorem H_pair_errIndicator {α : Type} [Fintype α] [DecidableEq α]
    {P : FinProb} (X Xhat : P.Ω → α) :
    H P (pair X (pair (errIndicator X Xhat) Xhat)) = H P (pair X Xhat) := by
  have hinj : Function.Injective
      (fun p : α × α => (p.1, (decide (p.1 ≠ p.2), p.2))) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    simp only [Prod.mk.injEq]
    exact ⟨h.1, h.2.2⟩
  have h := H_comp_of_injective (f := fun p : α × α => (p.1, (decide (p.1 ≠ p.2), p.2)))
    (pair X Xhat) hinj
  have hfun : (fun ω => (fun p : α × α => (p.1, (decide (p.1 ≠ p.2), p.2)))
        (pair X Xhat ω))
      = pair X (pair (errIndicator X Xhat) Xhat) := rfl
  rw [← hfun]
  exact h

/-! ### Step 2: the exact chain-rule split -/

/-- The chain rule, specialised to the error indicator. Because `condH` is
*defined* as a difference of entropies and `H_pair_errIndicator` is an equality,
this split is exact, not an inequality. -/
private theorem condH_split {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X Xhat : P.Ω → α) :
    condH P X Xhat
      = condH P X (pair (errIndicator X Xhat) Xhat)
        + condH P (errIndicator X Xhat) Xhat := by
  simp only [condH_def, H₂_def]
  rw [H_pair_errIndicator X Xhat]
  ring

/-! ### Step 3: the quantitative bound, instantiated -/

/-- `H(X | E, X̂) ≤ Pe · log |α|`: conditioned on knowing whether an error
occurred and on the estimate, `X` is fully determined unless an error occurred,
and errors have probability `Pe`. -/
private theorem condH_pair_errIndicator_le {α : Type} [Fintype α] [DecidableEq α]
    [Nonempty α] {P : FinProb} (X Xhat : P.Ω → α) :
    condH P X (pair (errIndicator X Xhat) Xhat)
      ≤ errProb X Xhat * Real.log (Fintype.card α) := by
  have hdet : ∀ ω, (fun s : Bool × α => s.1) (pair (errIndicator X Xhat) Xhat ω) = false
      → X ω = (fun s : Bool × α => s.2) (pair (errIndicator X Xhat) Xhat ω) := by
    intro ω hω
    have h' : errIndicator X Xhat ω = false := hω
    simp only [errIndicator, decide_eq_false_iff_not, not_not] at h'
    exact h'
  have hmain := condH_le_of_det X (pair (errIndicator X Xhat) Xhat)
    (fun s : Bool × α => s.1) (fun s : Bool × α => s.2) hdet
  -- Identify the bad-slice mass with the error probability.
  have herr : (∑ s : Bool × α,
        if (fun t : Bool × α => t.1) s = true
        then dist P (pair (errIndicator X Xhat) Xhat) s else 0)
      = errProb X Xhat := by
    have hsplit : (∑ s : Bool × α,
          if (fun t : Bool × α => t.1) s = true
          then dist P (pair (errIndicator X Xhat) Xhat) s else 0)
        = ∑ e : Bool, ∑ y : α,
            (if e = true then dist P (pair (errIndicator X Xhat) Xhat) (e, y) else 0) :=
      Fintype.sum_prod_type _
    rw [hsplit, Fintype.sum_bool]
    have hT : (∑ y : α,
          (if (true : Bool) = true
           then dist P (pair (errIndicator X Xhat) Xhat) (true, y) else 0))
        = dist P (errIndicator X Xhat) true := by
      refine (Finset.sum_congr rfl fun y _ => if_pos rfl).trans ?_
      exact dist_pair_marginal _ _ true
    have hF : (∑ y : α,
          (if (false : Bool) = true
           then dist P (pair (errIndicator X Xhat) Xhat) (false, y) else 0)) = 0 := by
      refine (Finset.sum_congr rfl fun y _ => if_neg (by simp)).trans ?_
      simp
    rw [hT, hF, add_zero]
    rfl
  rw [herr] at hmain
  exact hmain

/-! ### Fano's inequality -/

/-- **Fano's inequality.** The conditional entropy of `X` given an estimate `X̂` is
controlled by the error probability. -/
theorem fano_condH_le {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X Xhat : P.Ω → α) :
    condH P X Xhat ≤ Real.log 2 + errProb X Xhat * Real.log (Fintype.card α) := by
  have hne : Nonempty α := (isProbDist_dist X).nonempty
  have h1 := condH_split X Xhat
  have h2 := condH_pair_errIndicator_le X Xhat
  have h3 : condH P (errIndicator X Xhat) Xhat ≤ Real.log 2 :=
    le_trans (condH_le_H _ _) (H_bool_le_log_two _)
  linarith

/-- **Fano's inequality**, error-probability form. -/
theorem fano_errProb_ge {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X Xhat : P.Ω → α) (hcard : 1 < Fintype.card α) :
    (H P X - I P X Xhat - Real.log 2) / Real.log (Fintype.card α) ≤ errProb X Xhat := by
  have hlog : 0 < Real.log (Fintype.card α) := by
    refine Real.log_pos ?_
    exact_mod_cast hcard
  have h := fano_condH_le X Xhat
  rw [condH_eq_sub] at h
  rw [div_le_iff₀ hlog]
  linarith

/-- **Fano for a uniform hidden parameter** — the form a query lower bound uses:
if `X` is uniform on `α`, a small mutual information forces a large error
probability. -/
theorem fano_uniform {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {P : FinProb}
    (X Xhat : P.Ω → α) (hunif : dist P X = unifDist α) (hcard : 1 < Fintype.card α) :
    1 - (I P X Xhat + Real.log 2) / Real.log (Fintype.card α) ≤ errProb X Xhat := by
  have hlog : 0 < Real.log (Fintype.card α) := by
    refine Real.log_pos ?_
    exact_mod_cast hcard
  have hlog' : Real.log (Fintype.card α) ≠ 0 := ne_of_gt hlog
  have hHX : H P X = Real.log (Fintype.card α) := H_of_dist_eq_unif X hunif
  have h := fano_errProb_ge X Xhat hcard
  rw [hHX] at h
  have heq : (Real.log (Fintype.card α) - I P X Xhat - Real.log 2)
        / Real.log (Fintype.card α)
      = 1 - (I P X Xhat + Real.log 2) / Real.log (Fintype.card α) := by
    field_simp
    ring
  rw [heq] at h
  exact h

end InformationTheory
end Arlib
