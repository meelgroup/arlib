/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Relabel
import Arlib.InformationTheory.Gibbs
import Arlib.InformationTheory.Entropy

/-!
# Subadditivity and submodularity of Shannon entropy

This file is the single analytic core of `Arlib.InformationTheory`. Everything
else in the area — the chain rules, the data-processing inequality, Fano's
inequality — is either pure algebra over the definitions in `Defs.lean` or a
relabelling from `Relabel.lean`. The one genuinely *analytic* input is Gibbs'
inequality (`sum_mul_log_div_nonneg`, proved in `Gibbs.lean`), and this file is
where it is cashed in.

The pattern is uniform, and is used exactly twice. To prove that a signed
combination of entropies is nonnegative, one exhibits it as a single sum
`∑ t, p t * log (p t / q t)` for an explicit pair of nonnegative functions with
`∑ q ≤ ∑ p`, and appeals to Gibbs. For subadditivity the comparison law `q` is
the product of the marginals; for submodularity it is the "conditionally
independent coupling"

`q (x, y, z) = dist (X, Z) (x, z) * dist (Y, Z) (y, z) / dist Z z`,

which is sub-normalised precisely because the `dist Z z = 0` slices are dropped.
That is why `sum_mul_log_div_nonneg` was stated with the hypothesis `∑ q ≤ ∑ p`
rather than `∑ q = 1`.

## Main results

* `Arlib.InformationTheory.H₂_le_add` — subadditivity, `H(X, Y) ≤ H(X) + H(Y)`.
* `Arlib.InformationTheory.I_nonneg` — `0 ≤ I(X ; Y)`.
* `Arlib.InformationTheory.condH_le_H` — conditioning reduces entropy.
* `Arlib.InformationTheory.H_submodular` — `H(X,Z) + H(Y,Z) ≥ H(Z) + H(X,Y,Z)`.
* `Arlib.InformationTheory.condI_nonneg` — **the crux**: `0 ≤ I(X ; Y | Z)`.

## Implementation notes

The delicate point in both arguments is turning `log (p / q)` into a difference
of logarithms without incurring `≠ 0` side conditions. This is done termwise: on
the set where `p t = 0` both sides of the target identity vanish (Mathlib's
`0 * log 0 = 0` convention), and off it every law appearing in `q t` is *bounded
below* by `p t`, hence strictly positive, so `Real.log_div` and `Real.log_mul`
apply. The required domination facts (`dist_pair_le_left` and friends) are all
instances of one lemma, `dist_le_dist_of_imp`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Entropy as a plain sum -/

/-- Entropy written without `Real.negMulLog`, which is the form the Gibbs
argument produces. -/
private lemma H_eq_neg_sum {α : Type} [Fintype α] [DecidableEq α] {P : FinProb}
    (X : P.Ω → α) : H P X = -∑ a, dist P X a * Real.log (dist P X a) := by
  rw [H_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Real.negMulLog_eq_neg]

/-! ### Domination of laws -/

section Domination

variable {α β γ : Type} {P : FinProb}

/-- If the event `X = a` is contained in the event `Y = b`, then the law of `X`
at `a` is dominated by the law of `Y` at `b`. Every domination fact used below
is an instance of this. -/
private lemma dist_le_dist_of_imp [DecidableEq α] [DecidableEq β]
    (X : P.Ω → α) (Y : P.Ω → β) (a : α) (b : β)
    (h : ∀ ω, X ω = a → Y ω = b) : dist P X a ≤ dist P Y b := by
  simp only [dist]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hx : X ω = a
  · rw [if_pos hx, if_pos (h ω hx)]
  · rw [if_neg hx]
    by_cases hy : Y ω = b
    · rw [if_pos hy]; exact P.mass_nonneg ω
    · rw [if_neg hy]

private lemma dist_pair_le_left [DecidableEq α] [DecidableEq β]
    (X : P.Ω → α) (Y : P.Ω → β) (a : α) (b : β) :
    dist P (pair X Y) (a, b) ≤ dist P X a :=
  dist_le_dist_of_imp _ _ _ _ fun _ h => congrArg Prod.fst h

private lemma dist_pair_le_right [DecidableEq α] [DecidableEq β]
    (X : P.Ω → α) (Y : P.Ω → β) (a : α) (b : β) :
    dist P (pair X Y) (a, b) ≤ dist P Y b :=
  dist_le_dist_of_imp _ _ _ _ fun _ h => congrArg Prod.snd h

private lemma dist_triple_le_XZ [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) (x : α) (y : β) (z : γ) :
    dist P (pair X (pair Y Z)) (x, y, z) ≤ dist P (pair X Z) (x, z) := by
  refine dist_le_dist_of_imp _ _ _ _ fun ω h => ?_
  simp only [pair, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.2⟩

private lemma dist_triple_le_YZ [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) (x : α) (y : β) (z : γ) :
    dist P (pair X (pair Y Z)) (x, y, z) ≤ dist P (pair Y Z) (y, z) :=
  dist_pair_le_right X (pair Y Z) x (y, z)

private lemma dist_triple_le_Z [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) (x : α) (y : β) (z : γ) :
    dist P (pair X (pair Y Z)) (x, y, z) ≤ dist P Z z :=
  le_trans (dist_triple_le_YZ X Y Z x y z) (dist_pair_le_right Y Z y z)

end Domination

/-! ### Marginalising a triple law -/

/-- Summing the law of `(X, Y, Z)` over the *middle* coordinate gives the law of
`(X, Z)`. This is the three-variable analogue of `dist_pair_marginal`; it cannot
be obtained from that lemma by a single application, so it is proved directly
from the definition of `dist`. -/
private lemma sum_dist_triple_mid {α β γ : Type} [DecidableEq α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ)
    (x : α) (z : γ) :
    ∑ y : β, dist P (pair X (pair Y Z)) (x, y, z) = dist P (pair X Z) (x, z) := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hx : X ω = x
  · by_cases hz : Z ω = z
    · simp [hx, hz, Prod.ext_iff]
    · simp [hz, Prod.ext_iff]
  · simp [hx, Prod.ext_iff]

/-- Summing the law of `(X, Y, Z)` over the first two coordinates gives the law
of `Z`. -/
private lemma sum_dist_triple_XY {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ)
    (z : γ) :
    ∑ x : α, ∑ y : β, dist P (pair X (pair Y Z)) (x, y, z) = dist P Z z := by
  have h : ∀ x : α, ∑ y : β, dist P (pair X (pair Y Z)) (x, y, z)
      = dist P (pair X Z) (x, z) := fun x => sum_dist_triple_mid X Y Z x z
  simp only [h]
  exact dist_pair_marginal' X Z z

/-! ### Reindexing product sums -/

section Reindex

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

private lemma sum_prod3 (f : α × β × γ → ℝ) :
    ∑ t : α × β × γ, f t = ∑ x : α, ∑ y : β, ∑ z : γ, f (x, y, z) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Fintype.sum_prod_type _

private lemma sum_prod3' (f : α × β × γ → ℝ) :
    ∑ t : α × β × γ, f t = ∑ z : γ, ∑ x : α, ∑ y : β, f (x, y, z) := by
  calc ∑ t : α × β × γ, f t
      = ∑ x : α, ∑ y : β, ∑ z : γ, f (x, y, z) := sum_prod3 f
    _ = ∑ x : α, ∑ z : γ, ∑ y : β, f (x, y, z) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z : γ, ∑ x : α, ∑ y : β, f (x, y, z) := Finset.sum_comm

end Reindex

/-! ### Collapsing a joint sum onto a marginal -/

section Bridge

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {P : FinProb}

/-- The bridging identity: weighting `log` of a *marginal* law by the *joint*
law collapses to the marginal's own entropy sum. -/
private lemma sum_joint_mul_log_fst (X : P.Ω → α) (Y : P.Ω → β) :
    ∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P X ab.1)
      = ∑ a, dist P X a * Real.log (dist P X a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∑ b : β, dist P (pair X Y) (a, b) * Real.log (dist P X a)
      = dist P X a * Real.log (dist P X a) := by
    rw [← Finset.sum_mul, dist_pair_marginal]
  exact h

/-- The bridging identity, second coordinate. -/
private lemma sum_joint_mul_log_snd (X : P.Ω → α) (Y : P.Ω → β) :
    ∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P Y ab.2)
      = ∑ b, dist P Y b * Real.log (dist P Y b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : ∑ a : α, dist P (pair X Y) (a, b) * Real.log (dist P Y b)
      = dist P Y b * Real.log (dist P Y b) := by
    rw [← Finset.sum_mul, dist_pair_marginal']
  exact h

/-- Three-variable bridging identity for the `(X, Z)` marginal. -/
private lemma sum_triple_mul_log_XZ (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
        * Real.log (dist P (pair X Z) (t.1, t.2.2))
      = ∑ u : α × γ, dist P (pair X Z) u * Real.log (dist P (pair X Z) u) := by
  have h1 : ∀ (x : α) (z : γ), ∑ y : β,
      dist P (pair X (pair Y Z)) (x, y, z) * Real.log (dist P (pair X Z) (x, z))
      = dist P (pair X Z) (x, z) * Real.log (dist P (pair X Z) (x, z)) := by
    intro x z
    rw [← Finset.sum_mul, sum_dist_triple_mid]
  calc ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
          * Real.log (dist P (pair X Z) (t.1, t.2.2))
      = ∑ x : α, ∑ y : β, ∑ z : γ, dist P (pair X (pair Y Z)) (x, y, z)
          * Real.log (dist P (pair X Z) (x, z)) := sum_prod3 _
    _ = ∑ x : α, ∑ z : γ, ∑ y : β, dist P (pair X (pair Y Z)) (x, y, z)
          * Real.log (dist P (pair X Z) (x, z)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : α, ∑ z : γ,
          dist P (pair X Z) (x, z) * Real.log (dist P (pair X Z) (x, z)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => h1 x z
    _ = ∑ u : α × γ, dist P (pair X Z) u * Real.log (dist P (pair X Z) u) :=
        (Fintype.sum_prod_type
          (fun u : α × γ => dist P (pair X Z) u
            * Real.log (dist P (pair X Z) u))).symm

/-- Three-variable bridging identity for the `Z` marginal. -/
private lemma sum_triple_mul_log_Z (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t * Real.log (dist P Z t.2.2)
      = ∑ z : γ, dist P Z z * Real.log (dist P Z z) := by
  calc ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t * Real.log (dist P Z t.2.2)
      = ∑ z : γ, ∑ x : α, ∑ y : β,
          dist P (pair X (pair Y Z)) (x, y, z) * Real.log (dist P Z z) :=
        sum_prod3' _
    _ = ∑ z : γ, dist P Z z * Real.log (dist P Z z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have h : (∑ x : α, ∑ y : β, dist P (pair X (pair Y Z)) (x, y, z))
              * Real.log (dist P Z z)
            = ∑ x : α, ∑ y : β,
                dist P (pair X (pair Y Z)) (x, y, z) * Real.log (dist P Z z) := by
          simp only [Finset.sum_mul]
        rw [← h, sum_dist_triple_XY]

end Bridge

/-! ### The two comparison laws -/

/-- The product of the marginals, used as the comparison law in the proof of
subadditivity. -/
private noncomputable def prodQ {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    α × β → ℝ :=
  fun ab => dist P X ab.1 * dist P Y ab.2

/-- The "conditionally independent coupling" of `X` and `Y` given `Z`, used as
the comparison law in the proof of submodularity. It is sub-normalised: the
slices on which `dist P Z z = 0` contribute nothing. -/
private noncomputable def subQ {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) : α × β × γ → ℝ :=
  fun t => if dist P Z t.2.2 = 0 then 0
    else dist P (pair X Z) (t.1, t.2.2) * dist P (pair Y Z) t.2 / dist P Z t.2.2

/-! ### Subadditivity -/

/-- **Subadditivity of entropy**: `H(X, Y) ≤ H(X) + H(Y)`. -/
theorem H₂_le_add {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    H₂ P X Y ≤ H P X + H P Y := by
  -- The comparison law is nonnegative.
  have hq : ∀ ab : α × β, 0 ≤ prodQ X Y ab := fun _ =>
    mul_nonneg (dist_nonneg _ _) (dist_nonneg _ _)
  -- It has total mass `1`, so certainly at most that of the joint law.
  have hsum : ∑ ab : α × β, prodQ X Y ab
      ≤ ∑ ab : α × β, dist P (pair X Y) ab := by
    have h1 : ∑ ab : α × β, prodQ X Y ab
        = ∑ a : α, ∑ b : β, dist P X a * dist P Y b := by
      rw [Fintype.sum_prod_type]
      rfl
    have h2 : ∀ a : α, ∑ b : β, dist P X a * dist P Y b = dist P X a := by
      intro a; rw [← Finset.mul_sum, dist_sum, mul_one]
    rw [h1]
    simp only [h2]
    rw [dist_sum, dist_sum]
  -- Absolute continuity: a vanishing product forces a vanishing joint law.
  have hac : ∀ ab : α × β, prodQ X Y ab = 0 → dist P (pair X Y) ab = 0 := by
    rintro ⟨a, b⟩ h
    have h' : dist P X a * dist P Y b = 0 := h
    rcases mul_eq_zero.mp h' with h0 | h0
    · have hle := dist_pair_le_left X Y a b
      rw [h0] at hle
      exact le_antisymm hle (dist_nonneg _ _)
    · have hle := dist_pair_le_right X Y a b
      rw [h0] at hle
      exact le_antisymm hle (dist_nonneg _ _)
  -- Gibbs' inequality.
  have gibbs : 0 ≤ ∑ ab : α × β, dist P (pair X Y) ab
      * Real.log (dist P (pair X Y) ab / prodQ X Y ab) :=
    sum_mul_log_div_nonneg (fun ab : α × β => dist P (pair X Y) ab) (prodQ X Y)
      (fun _ => dist_nonneg _ _) hq hsum hac
  -- Expand the logarithm termwise.
  have key : ∑ ab : α × β, dist P (pair X Y) ab
        * Real.log (dist P (pair X Y) ab / prodQ X Y ab)
      = (∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P (pair X Y) ab))
        - (∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P X ab.1))
        - (∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P Y ab.2)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ab _ => ?_
    obtain ⟨a, b⟩ := ab
    show dist P (pair X Y) (a, b)
          * Real.log (dist P (pair X Y) (a, b) / (dist P X a * dist P Y b))
        = dist P (pair X Y) (a, b) * Real.log (dist P (pair X Y) (a, b))
          - dist P (pair X Y) (a, b) * Real.log (dist P X a)
          - dist P (pair X Y) (a, b) * Real.log (dist P Y b)
    rcases eq_or_lt_of_le (dist_nonneg (pair X Y) (a, b)) with h0 | h0
    · rw [← h0]; ring
    · have hx : 0 < dist P X a := lt_of_lt_of_le h0 (dist_pair_le_left X Y a b)
      have hy : 0 < dist P Y b := lt_of_lt_of_le h0 (dist_pair_le_right X Y a b)
      rw [Real.log_div (ne_of_gt h0) (ne_of_gt (mul_pos hx hy)),
        Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
      ring
  -- Identify the three sums as entropies.
  have e1 : ∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P (pair X Y) ab)
      = -H P (pair X Y) := by
    rw [H_eq_neg_sum]; ring
  have e2 : ∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P X ab.1)
      = -H P X := by
    rw [sum_joint_mul_log_fst, H_eq_neg_sum]; ring
  have e3 : ∑ ab : α × β, dist P (pair X Y) ab * Real.log (dist P Y ab.2)
      = -H P Y := by
    rw [sum_joint_mul_log_snd, H_eq_neg_sum]; ring
  rw [key, e1, e2, e3] at gibbs
  rw [H₂_def]
  linarith

/-- **Mutual information is nonnegative.** -/
theorem I_nonneg {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    0 ≤ I P X Y := by
  rw [I_eq_add_sub]
  linarith [H₂_le_add X Y]

/-- **Conditioning reduces entropy**: `H(X | Y) ≤ H(X)`. -/
theorem condH_le_H {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    condH P X Y ≤ H P X := by
  rw [condH_def]
  linarith [H₂_le_add X Y]

/-! ### Submodularity -/

/-- **Submodularity of entropy**: `H(X, Z) + H(Y, Z) ≥ H(Z) + H(X, Y, Z)`. -/
theorem H_submodular {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    H P (pair X (pair Y Z)) + H P Z ≤ H P (pair X Z) + H P (pair Y Z) := by
  -- The comparison law is nonnegative.
  have hq : ∀ t : α × β × γ, 0 ≤ subQ X Y Z t := by
    intro t
    simp only [subQ]
    split
    · exact le_refl 0
    · exact div_nonneg (mul_nonneg (dist_nonneg _ _) (dist_nonneg _ _))
        (dist_nonneg _ _)
  -- Slicewise it has mass at most `dist P Z z`, with equality off the null set.
  have hzle : ∀ z : γ, ∑ x : α, ∑ y : β, subQ X Y Z (x, y, z) ≤ dist P Z z := by
    intro z
    by_cases hz : dist P Z z = 0
    · have hall : ∀ x : α, ∑ y : β, subQ X Y Z (x, y, z) = 0 := fun _ =>
        Finset.sum_eq_zero fun _ _ => by simp [subQ, hz]
      simp only [hall]
      simp [hz]
    · have hinner : ∀ x : α, ∑ y : β, subQ X Y Z (x, y, z)
          = dist P (pair X Z) (x, z) := by
        intro x
        have h1 : ∀ y : β, subQ X Y Z (x, y, z)
            = dist P (pair X Z) (x, z) * dist P (pair Y Z) (y, z) / dist P Z z := by
          intro y
          show (if dist P Z z = 0 then 0
            else dist P (pair X Z) (x, z) * dist P (pair Y Z) (y, z)
              / dist P Z z) = _
          rw [if_neg hz]
        simp only [h1]
        rw [← Finset.sum_div, ← Finset.mul_sum, dist_pair_marginal' Y Z z,
          mul_div_assoc, div_self hz, mul_one]
      simp only [hinner]
      exact le_of_eq (dist_pair_marginal' X Z z)
  -- Hence its total mass is at most `1`, the mass of the joint law.
  have hsum : ∑ t : α × β × γ, subQ X Y Z t
      ≤ ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t := by
    rw [sum_prod3' (subQ X Y Z), dist_sum]
    calc ∑ z : γ, ∑ x : α, ∑ y : β, subQ X Y Z (x, y, z)
        ≤ ∑ z : γ, dist P Z z := Finset.sum_le_sum fun z _ => hzle z
      _ = 1 := dist_sum Z
  -- Absolute continuity.
  have hac : ∀ t : α × β × γ, subQ X Y Z t = 0
      → dist P (pair X (pair Y Z)) t = 0 := by
    rintro ⟨x, y, z⟩ h
    have hle0 : ∀ c : ℝ, dist P (pair X (pair Y Z)) (x, y, z) ≤ c → c = 0
        → dist P (pair X (pair Y Z)) (x, y, z) = 0 := by
      intro c hc hc0
      rw [hc0] at hc
      exact le_antisymm hc (dist_nonneg _ _)
    by_cases hz : dist P Z z = 0
    · exact hle0 _ (dist_triple_le_Z X Y Z x y z) hz
    · have h' : dist P (pair X Z) (x, z) * dist P (pair Y Z) (y, z)
          / dist P Z z = 0 := by
        have hh : (if dist P Z z = 0 then 0
            else dist P (pair X Z) (x, z) * dist P (pair Y Z) (y, z)
              / dist P Z z) = 0 := h
        rwa [if_neg hz] at hh
      rcases div_eq_zero_iff.mp h' with hAB | hc
      · rcases mul_eq_zero.mp hAB with hA | hB
        · exact hle0 _ (dist_triple_le_XZ X Y Z x y z) hA
        · exact hle0 _ (dist_triple_le_YZ X Y Z x y z) hB
      · exact absurd hc hz
  -- Gibbs' inequality.
  have gibbs : 0 ≤ ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
      * Real.log (dist P (pair X (pair Y Z)) t / subQ X Y Z t) :=
    sum_mul_log_div_nonneg (fun t : α × β × γ => dist P (pair X (pair Y Z)) t)
      (subQ X Y Z) (fun _ => dist_nonneg _ _) hq hsum hac
  -- Expand the logarithm termwise.
  have key : ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
        * Real.log (dist P (pair X (pair Y Z)) t / subQ X Y Z t)
      = (∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
            * Real.log (dist P (pair X (pair Y Z)) t))
        - (∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
            * Real.log (dist P (pair X Z) (t.1, t.2.2)))
        - (∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
            * Real.log (dist P (pair Y Z) t.2))
        + (∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
            * Real.log (dist P Z t.2.2)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨x, y, z⟩ := t
    show dist P (pair X (pair Y Z)) (x, y, z)
          * Real.log (dist P (pair X (pair Y Z)) (x, y, z)
              / (if dist P Z z = 0 then 0
                 else dist P (pair X Z) (x, z) * dist P (pair Y Z) (y, z)
                   / dist P Z z))
        = dist P (pair X (pair Y Z)) (x, y, z)
            * Real.log (dist P (pair X (pair Y Z)) (x, y, z))
          - dist P (pair X (pair Y Z)) (x, y, z)
              * Real.log (dist P (pair X Z) (x, z))
          - dist P (pair X (pair Y Z)) (x, y, z)
              * Real.log (dist P (pair Y Z) (y, z))
          + dist P (pair X (pair Y Z)) (x, y, z) * Real.log (dist P Z z)
    rcases eq_or_lt_of_le (dist_nonneg (pair X (pair Y Z)) (x, y, z)) with h0 | h0
    · rw [← h0]; ring
    · have hXZ : 0 < dist P (pair X Z) (x, z) :=
        lt_of_lt_of_le h0 (dist_triple_le_XZ X Y Z x y z)
      have hYZ : 0 < dist P (pair Y Z) (y, z) :=
        lt_of_lt_of_le h0 (dist_triple_le_YZ X Y Z x y z)
      have hZ : 0 < dist P Z z := lt_of_lt_of_le h0 (dist_triple_le_Z X Y Z x y z)
      rw [if_neg (ne_of_gt hZ)]
      rw [Real.log_div (ne_of_gt h0)
          (ne_of_gt (div_pos (mul_pos hXZ hYZ) hZ)),
        Real.log_div (ne_of_gt (mul_pos hXZ hYZ)) (ne_of_gt hZ),
        Real.log_mul (ne_of_gt hXZ) (ne_of_gt hYZ)]
      ring
  -- Identify the four sums as entropies.
  have e1 : ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
      * Real.log (dist P (pair X (pair Y Z)) t) = -H P (pair X (pair Y Z)) := by
    rw [H_eq_neg_sum]; ring
  have e2 : ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
      * Real.log (dist P (pair X Z) (t.1, t.2.2)) = -H P (pair X Z) := by
    rw [sum_triple_mul_log_XZ, H_eq_neg_sum]; ring
  have e3 : ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
      * Real.log (dist P (pair Y Z) t.2) = -H P (pair Y Z) := by
    rw [sum_joint_mul_log_snd, H_eq_neg_sum]; ring
  have e4 : ∑ t : α × β × γ, dist P (pair X (pair Y Z)) t
      * Real.log (dist P Z t.2.2) = -H P Z := by
    rw [sum_triple_mul_log_Z, H_eq_neg_sum]; ring
  rw [key, e1, e2, e3, e4] at gibbs
  linarith

/-- **THE CRUX: conditional mutual information is nonnegative.** Every inequality
in the development downstream reduces to this one; the chain rules are pure
algebra. -/
theorem condI_nonneg {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    0 ≤ condI P X Y Z := by
  simp only [condI_def, condH_def, H₂_def]
  linarith [H_submodular X Y Z]

end InformationTheory
end Arlib
