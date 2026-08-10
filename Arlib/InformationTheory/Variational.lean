/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Gibbs

/-!
# The golden formula and the variational upper bound on mutual information

This file proves the identity that query-complexity lower-bound arguments use as
their main workhorse. Mutual information is *exactly* the `X`-average of the
Kullback–Leibler divergence from the conditional law of `Z` to its marginal law,

    `I(X ; Z) = ∑ a, P_X(a) * KL(P_{Z|X = a} ‖ P_Z)`,

and replacing the marginal `P_Z` by an *arbitrary* auxiliary distribution `Q`
only increases the average, the excess being exactly `KL(P_Z ‖ Q) ≥ 0`. Hence
for any `Q` whatsoever,

    `I(X ; Z) ≤ max over a of KL(P_{Z|X = a} ‖ Q)`.

This is what makes the bound usable: one is free to pick whichever `Q` makes the
conditional divergences easy to estimate, and no optimality of `Q` is needed.

## Main results

* `Arlib.InformationTheory.I_eq_sum_KL` — mutual information as an average KL
  divergence.
* `Arlib.InformationTheory.sum_KL_eq_I_add_KL` — the golden formula.
* `Arlib.InformationTheory.I_le_of_KL_le` — the variational upper bound in the
  form lower-bound proofs consume.

## Implementation notes

Every proof reduces to a single `Finset.sum_congr` over `α × β` against the joint
law, with the degenerate terms (`dist P (pair X Z) (a, b) = 0`) split off first.
On the complementary branch all three of `dist P X a`, `dist P Z b` and
`condDist P Z X a b` are nonzero, so `Real.log_div` applies without side
conditions and the identity is `ring`. The bridge between sums against the joint
law and sums against a marginal is `dist_pair_marginal` / `dist_pair_marginal'`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

variable {α β : Type}

/-! ### Bridging lemmas -/

/-- Entropy as a sum, with the sign pulled out of the sum. -/
private theorem sum_negMulLog [Fintype α] (p : α → ℝ) :
    ∑ a, Real.negMulLog (p a) = -∑ a, p a * Real.log (p a) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.negMulLog]

/-- Marginalising a sum against the joint law whose summand depends only on the
first coordinate. -/
private theorem sum_pair_mul_left [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (f : α → ℝ) :
    ∑ ab : α × β, dist P (pair X Z) ab * f ab.1 = ∑ a, dist P X a * f a := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← Finset.sum_mul, dist_pair_marginal]

/-- Marginalising a sum against the joint law whose summand depends only on the
second coordinate. -/
private theorem sum_pair_mul_right [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (f : β → ℝ) :
    ∑ ab : α × β, dist P (pair X Z) ab * f ab.2 = ∑ b, dist P Z b * f b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  rw [← Finset.sum_mul, dist_pair_marginal']

/-- The `X`-average of a conditional KL divergence, rewritten as a single sum
against the joint law. -/
private theorem sum_mul_KLdist_eq [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (q : β → ℝ) :
    ∑ a, dist P X a * KLdist (condDist P Z X a) q
      = ∑ ab : α × β, dist P (pair X Z) ab *
          Real.log (condDist P Z X ab.1 ab.2 / q ab.2) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [KLdist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dist_pair_eq_mul_condDist]
  ring

/-- On a non-null cell of the joint law, all three of the marginals and the
conditional law are nonzero. -/
private theorem ne_zero_of_pair_ne_zero [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (a : α) (b : β)
    (hp : dist P (pair X Z) (a, b) ≠ 0) :
    dist P X a ≠ 0 ∧ dist P Z b ≠ 0 ∧ condDist P Z X a b ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hp (by rw [dist_pair_eq_mul_condDist, h, zero_mul])
  · intro h
    refine hp (le_antisymm ?_ (dist_nonneg _ _))
    have hle : dist P (pair X Z) (a, b) ≤ ∑ a', dist P (pair X Z) (a', b) :=
      Finset.single_le_sum (f := fun a' => dist P (pair X Z) (a', b))
        (fun a' _ => dist_nonneg _ _) (Finset.mem_univ a)
    rwa [dist_pair_marginal' X Z b, h] at hle
  · intro h
    exact hp (by rw [dist_pair_eq_mul_condDist, h, mul_zero])

/-! ### Mutual information as an average divergence -/

/-- Mutual information as an average KL divergence from the conditional law to the
marginal law. -/
theorem I_eq_sum_KL {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) :
    I P X Z = ∑ a, dist P X a * KLdist (condDist P Z X a) (dist P Z) := by
  rw [sum_mul_KLdist_eq X Z (dist P Z)]
  have hsplit :
      ∑ ab : α × β, dist P (pair X Z) ab *
          Real.log (condDist P Z X ab.1 ab.2 / dist P Z ab.2)
        = (∑ ab : α × β, dist P (pair X Z) ab * Real.log (dist P (pair X Z) ab))
          - (∑ ab : α × β, dist P (pair X Z) ab * Real.log (dist P X ab.1))
          - ∑ ab : α × β, dist P (pair X Z) ab * Real.log (dist P Z ab.2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a, b⟩ -
    dsimp only
    by_cases hp : dist P (pair X Z) (a, b) = 0
    · simp [hp]
    · obtain ⟨hX, hZ, hc⟩ := ne_zero_of_pair_ne_zero X Z a b hp
      have hceq : condDist P Z X a b = dist P (pair X Z) (a, b) / dist P X a := by
        simp [condDist, hX]
      rw [Real.log_div hc hZ, hceq, Real.log_div hp hX]
      ring
  rw [hsplit, sum_pair_mul_left X Z (fun a => Real.log (dist P X a)),
    sum_pair_mul_right X Z (fun b => Real.log (dist P Z b))]
  rw [I_eq_add_sub, H_def, H_def, H₂_def, H_def, sum_negMulLog, sum_negMulLog,
    sum_negMulLog]
  ring

/-- **The golden formula.** For any auxiliary distribution `Q`, the `X`-average of
`KL(P_{Z|X} ‖ Q)` exceeds the mutual information by exactly `KL(P_Z ‖ Q)`. -/
theorem sum_KL_eq_I_add_KL {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (Q : β → ℝ)
    (hQ : ∀ b, dist P Z b ≠ 0 → Q b ≠ 0) :
    ∑ a, dist P X a * KLdist (condDist P Z X a) Q
      = I P X Z + KLdist (dist P Z) Q := by
  rw [sum_mul_KLdist_eq X Z Q, I_eq_sum_KL X Z, sum_mul_KLdist_eq X Z (dist P Z)]
  have hsplit :
      ∑ ab : α × β, dist P (pair X Z) ab *
          Real.log (condDist P Z X ab.1 ab.2 / Q ab.2)
        = (∑ ab : α × β, dist P (pair X Z) ab *
            Real.log (condDist P Z X ab.1 ab.2 / dist P Z ab.2))
          + ∑ ab : α × β, dist P (pair X Z) ab *
              Real.log (dist P Z ab.2 / Q ab.2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a, b⟩ -
    dsimp only
    by_cases hp : dist P (pair X Z) (a, b) = 0
    · simp [hp]
    · obtain ⟨hX, hZ, hc⟩ := ne_zero_of_pair_ne_zero X Z a b hp
      rw [Real.log_div hc (hQ b hZ), Real.log_div hc hZ, Real.log_div hZ (hQ b hZ)]
      ring
  rw [hsplit]
  congr 1
  simp only [KLdist]
  exact sum_pair_mul_right X Z (fun b => Real.log (dist P Z b / Q b))

/-- **Variational upper bound on mutual information.** This is the form lower-bound
proofs consume: pick any convenient `Q`, bound `KL(P_{Z|X=a} ‖ Q)` uniformly in `a`,
and that bound transfers to `I(X ; Z)`. -/
theorem I_le_of_KL_le {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (Q : β → ℝ)
    (hQ : IsProbDist Q) (hQ0 : ∀ b, dist P Z b ≠ 0 → Q b ≠ 0) (c : ℝ)
    (h : ∀ a, dist P X a ≠ 0 → KLdist (condDist P Z X a) Q ≤ c) :
    I P X Z ≤ c := by
  have hgolden := sum_KL_eq_I_add_KL X Z Q hQ0
  have hKL : 0 ≤ KLdist (dist P Z) Q :=
    KLdist_nonneg (isProbDist_dist Z) hQ fun b hb =>
      not_not.mp fun hne => hQ0 b hne hb
  have hbound : ∑ a, dist P X a * KLdist (condDist P Z X a) Q ≤ ∑ a : α, dist P X a * c := by
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases ha : dist P X a = 0
    · simp [ha]
    · exact mul_le_mul_of_nonneg_left (h a ha) (dist_nonneg _ _)
  rw [← Finset.sum_mul, dist_sum, one_mul] at hbound
  linarith

end InformationTheory
end Arlib
