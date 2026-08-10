/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.FinProb

/-!
# Laws of random variables on a finite probability space

The *law* (distribution) of a random variable `X : P.Ω → α` on a finite
probability space `P : FinProb` is the function `a ↦ Pr[X = a]`.  This file sets
up that law, its joint and conditional forms, and the two distinguished laws that
recur everywhere: the uniform distribution and the law of an error indicator.

## Layering

These are **probability** notions, not information-theoretic ones: nothing here
mentions entropy, and `Arlib.Probability` itself needs them
(`Arlib.Probability.FinProbProd`, `Arlib.Probability.Conditioning`,
`Arlib.Probability.SequentialCond`).  They used to live in
`Arlib.InformationTheory.{Basic, Uniform, Fano}`, which made
`Arlib.Probability` and `Arlib.InformationTheory` mutually importing.  They are
here now, and `Arlib/InformationTheory/Basic.lean` re-exports every name under
its old `Arlib.InformationTheory` spelling, so the information-theory modules are
unaffected.

## Design

We work with random variables `X : P.Ω → α` on a shared finite probability space
`P : FinProb`, rather than with abstract distributions. This is what makes the
conditional statements usable: the arguments downstream condition on a growing
prefix of a transcript, and expressing those as marginals of one joint law on a
common space is far cheaper than juggling a tower of conditional distributions.

The two workhorses are `pair` (bundle two random variables into one valued in a
product) and `dist_pair_marginal` (summing a joint law over one coordinate gives
the marginal law). Nearly every identity downstream — the chain rules in
particular — is those two facts plus algebra.

## Main definitions

* `Arlib.Probability.IsProbDist p` — `p` is a probability distribution.
* `Arlib.Probability.dist P X` — the law of `X`, a function `α → ℝ`.
* `Arlib.Probability.pair X Y` — the joint random variable `ω ↦ (X ω, Y ω)`.
* `Arlib.Probability.condDist P Z X a` — the law of `Z` given `X = a`.
* `Arlib.Probability.unifDist α` — the uniform distribution on `α`.
* `Arlib.Probability.errIndicator X Xhat` / `errProb X Xhat` — the error event of
  an estimate and its probability.

Everything here is proved from first principles with no `sorry`.
-/

open scoped BigOperators
open Finset

namespace Arlib.Probability

variable {P : FinProb} {α β γ : Type}

/-! ### Probability distributions -/

/-- A nonnegative function summing to `1`. The laws produced by `dist` satisfy
this, and it is the hypothesis form used by results (such as Gibbs' inequality)
that do not need an ambient probability space. -/
structure IsProbDist [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_eq_one : ∑ a, p a = 1

namespace IsProbDist

variable [Fintype α] {p : α → ℝ}

theorem le_one (hp : IsProbDist p) (a : α) : p a ≤ 1 := by
  have h : p a ≤ ∑ b, p b :=
    Finset.single_le_sum (f := p) (fun b _ => hp.nonneg b) (Finset.mem_univ a)
  simpa [hp.sum_eq_one] using h

/-- A probability distribution lives on a nonempty type: an empty sum cannot
be `1`. -/
theorem nonempty (hp : IsProbDist p) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hz : (∑ a : α, p a) = 0 := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rw [hp.sum_eq_one] at hz
  exact one_ne_zero hz

end IsProbDist

/-! ### The law of a random variable -/

/-- The law of the random variable `X`: `dist P X a` is the probability that
`X` takes the value `a`. -/
noncomputable def dist (P : FinProb) [DecidableEq α] (X : P.Ω → α) : α → ℝ :=
  fun a => ∑ ω, if X ω = a then P.mass ω else 0

section

variable [DecidableEq α]

theorem dist_nonneg (X : P.Ω → α) (a : α) : 0 ≤ dist P X a := by
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : X ω = a <;> simp [h, P.mass_nonneg ω]

variable [Fintype α]

@[simp] theorem dist_sum (X : P.Ω → α) : ∑ a, dist P X a = 1 := by
  simp only [dist]
  rw [Finset.sum_comm]
  calc ∑ ω, ∑ a, (if X ω = a then P.mass ω else 0)
      = ∑ ω, P.mass ω := Finset.sum_congr rfl fun ω _ => by simp
    _ = 1 := P.mass_sum

theorem isProbDist_dist (X : P.Ω → α) : IsProbDist (dist P X) :=
  ⟨dist_nonneg X, dist_sum X⟩

theorem dist_le_one (X : P.Ω → α) (a : α) : dist P X a ≤ 1 :=
  (isProbDist_dist X).le_one a

end

/-! ### Pairing -/

/-- Two random variables bundled into one valued in the product. -/
def pair (X : P.Ω → α) (Y : P.Ω → β) : P.Ω → α × β := fun ω => (X ω, Y ω)

@[simp] theorem pair_apply (X : P.Ω → α) (Y : P.Ω → β) (ω : P.Ω) :
    pair X Y ω = (X ω, Y ω) := rfl

section

variable [DecidableEq α] [DecidableEq β]

/-- **Marginalisation.** Summing the joint law over the second coordinate
recovers the law of the first. -/
theorem dist_pair_marginal [Fintype β] (X : P.Ω → α) (Y : P.Ω → β) (a : α) :
    ∑ b, dist P (pair X Y) (a, b) = dist P X a := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = a
  · simp [h]
  · simp [h, Prod.ext_iff]

/-- **Marginalisation**, second coordinate. -/
theorem dist_pair_marginal' [Fintype α] (X : P.Ω → α) (Y : P.Ω → β) (b : β) :
    ∑ a, dist P (pair X Y) (a, b) = dist P Y b := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : Y ω = b
  · simp [h]
  · simp [h, Prod.ext_iff]

/-- The law of a pair, summed over all pairs, is `1` — restated in the curried
form that double sums produce. -/
theorem dist_pair_sum [Fintype α] [Fintype β] (X : P.Ω → α) (Y : P.Ω → β) :
    ∑ a, ∑ b, dist P (pair X Y) (a, b) = 1 := by
  simp [dist_pair_marginal]

end

/-! ### Conditional laws -/

/-- The conditional law of `Z` given `X = a`. On the null event `dist P X a = 0`
this is the zero function; every result about it therefore carries the hypothesis
`dist P X a ≠ 0`, which is the honest scope. -/
noncomputable def condDist (P : FinProb) [DecidableEq α] [DecidableEq β]
    (Z : P.Ω → β) (X : P.Ω → α) (a : α) : β → ℝ :=
  fun b => if dist P X a = 0 then 0 else dist P (pair X Z) (a, b) / dist P X a

section

variable [DecidableEq α] [DecidableEq β]

theorem condDist_nonneg (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    0 ≤ condDist P Z X a b := by
  unfold condDist
  split
  · exact le_refl 0
  · exact div_nonneg (dist_nonneg _ _) (dist_nonneg _ _)

/-- The defining property: joint law = marginal × conditional. -/
theorem dist_pair_eq_mul_condDist (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    dist P (pair X Z) (a, b) = dist P X a * condDist P Z X a b := by
  unfold condDist
  split
  · rename_i h
    -- `dist P X a = 0` forces the joint law to vanish, since it is dominated by it.
    have hle : dist P (pair X Z) (a, b) ≤ dist P X a := by
      calc dist P (pair X Z) (a, b)
          = ∑ ω, if (X ω, Z ω) = (a, b) then P.mass ω else 0 := rfl
        _ ≤ ∑ ω, if X ω = a then P.mass ω else 0 := by
            refine Finset.sum_le_sum fun ω _ => ?_
            by_cases hx : X ω = a
            · by_cases hz : Z ω = b <;> simp [hx, hz, P.mass_nonneg ω]
            · simp [hx, Prod.ext_iff]
        _ = dist P X a := rfl
    have := le_antisymm (h ▸ hle) (dist_nonneg (pair X Z) (a, b))
    simp [h, this]
  · rename_i h
    field_simp

theorem condDist_sum [Fintype β] (Z : P.Ω → β) (X : P.Ω → α) (a : α)
    (ha : dist P X a ≠ 0) : ∑ b, condDist P Z X a b = 1 := by
  have : ∑ b, dist P X a * condDist P Z X a b = dist P X a := by
    simp only [← dist_pair_eq_mul_condDist]
    exact dist_pair_marginal X Z a
  rw [← Finset.mul_sum] at this
  exact mul_left_cancel₀ ha (by simpa using this)

theorem isProbDist_condDist [Fintype β] (Z : P.Ω → β) (X : P.Ω → α) (a : α)
    (ha : dist P X a ≠ 0) : IsProbDist (condDist P Z X a) :=
  ⟨condDist_nonneg Z X a, condDist_sum Z X a ha⟩

end

/-! ### The uniform distribution -/

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def unifDist (α : Type) [Fintype α] : α → ℝ :=
  fun _ => ((Fintype.card α : ℝ))⁻¹

/-- The uniform distribution is a probability distribution. -/
theorem isProbDist_unifDist {α : Type} [Fintype α] [Nonempty α] :
    IsProbDist (unifDist α) where
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by
    show ∑ _a : α, ((Fintype.card α : ℝ))⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-! ### The error event of an estimate -/

/-- The error indicator of an estimate. -/
def errIndicator {α : Type} [DecidableEq α] {P : FinProb} (X Xhat : P.Ω → α) : P.Ω → Bool :=
  fun ω => decide (X ω ≠ Xhat ω)

/-- The error probability of an estimate. -/
noncomputable def errProb {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X Xhat : P.Ω → α) : ℝ :=
  dist P (errIndicator X Xhat) true

/-- The error probability is the mass of an event, hence nonnegative. -/
theorem errProb_nonneg {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X Xhat : P.Ω → α) : 0 ≤ errProb X Xhat :=
  dist_nonneg _ _

end Arlib.Probability
