/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Medians: the reduction lemma, and the concrete median value

## The reduction (`IsMedian`)

A median-based argument typically reduces "the median of a collection of entries
lands outside the target interval" to "at least half of the entries land outside".

We isolate the reusable, fully-proved combinatorial core:

  **If `m` is a median of `v` and strictly fewer than half of the `v b` lie
  outside an interval `I`, then `m ∈ I`.**

No sorting or committing to a particular tie-breaking `median` implementation is
needed — a median is *any* value with at least half the entries on each side.

## The concrete value (`medianOf`)

Many applications, however, need an actual number.  The second half of this
file supplies one — `medianOf v`, the `⌊n/2⌋`-th order statistic via
`Tuple.sort` — and proves it satisfies `IsMedian`, so that any consumer needing
a concrete median value can use it in place of the abstract predicate.

No `sorry`.
-/
import Arlib.Prelude
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace Arlib.Probability

open Finset
open scoped Classical

/-! ## The median predicate and the reduction lemma -/

section Reduction

variable {γ : ℕ} {v : Fin γ → ℝ}

/-- `m` is a *median* of the finite family `v` when at least half of the entries
are `≤ m` and at least half are `≥ m`. -/
def IsMedian (m : ℝ) (v : Fin γ → ℝ) : Prop :=
  γ ≤ 2 * (Finset.univ.filter (fun b => v b ≤ m)).card ∧
  γ ≤ 2 * (Finset.univ.filter (fun b => m ≤ v b)).card

/-- **Median reduction.**  If `m` is a median of `v` and strictly fewer than
half of the entries fall outside `Set.Icc lo hi`, then `m ∈ [lo, hi]`. -/
theorem median_mem_Icc_of_lt_half_outside
    {m lo hi : ℝ} (hmed : IsMedian m v)
    (hout : 2 * (Finset.univ.filter (fun b => v b ∉ Set.Icc lo hi)).card < γ) :
    m ∈ Set.Icc lo hi := by
  obtain ⟨hle, hge⟩ := hmed
  set Out := Finset.univ.filter (fun b => v b ∉ Set.Icc lo hi) with hOut
  refine ⟨?_, ?_⟩
  · -- lower bound `lo ≤ m`
    by_contra hlt
    push Not at hlt  -- `m < lo`
    -- every entry `≤ m` is `< lo`, hence outside `[lo,hi]`
    have hsub : (Finset.univ.filter (fun b => v b ≤ m)) ⊆ Out := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨hb.1, ?_⟩
      intro hmem
      exact absurd (lt_of_le_of_lt hb.2 hlt) (not_lt.mpr hmem.1)
    have hcard := Finset.card_le_card hsub
    omega
  · -- upper bound `m ≤ hi`
    by_contra hlt
    push Not at hlt  -- `hi < m`
    have hsub : (Finset.univ.filter (fun b => m ≤ v b)) ⊆ Out := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨hb.1, ?_⟩
      intro hmem
      exact absurd (lt_of_lt_of_le hlt hb.2) (not_lt.mpr hmem.2)
    have hcard := Finset.card_le_card hsub
    omega

/-- Contrapositive form: if a median lands *outside* the
interval, then at least half of the entries are outside. -/
theorem half_outside_of_median_not_mem
    {m lo hi : ℝ} (hmed : IsMedian m v)
    (hbad : m ∉ Set.Icc lo hi) :
    γ ≤ 2 * (Finset.univ.filter (fun b => v b ∉ Set.Icc lo hi)).card := by
  by_contra h
  push Not at h
  exact hbad (median_mem_Icc_of_lt_half_outside hmed h)

/-- **Order-statistic median witness.**  Given any permutation `σ` with `v ∘ σ`
monotone (e.g. `Tuple.sort v`) and a position `k` whose index straddles the
middle (`γ ≤ 2·(k+1)` and `γ ≤ 2·(γ-k)`), the value `v (σ k)` is a median of `v`.
The two straddle hypotheses both hold for `k = ⌊γ/2⌋`, so this is the general
lemma from which `isMedian_medianOf` (below) is the `⌊n/2⌋`-th special case. -/
theorem isMedian_of_monotone_sort
    (σ : Equiv.Perm (Fin γ)) (hmono : Monotone (v ∘ σ)) (k : Fin γ)
    (hk1 : γ ≤ 2 * ((k : ℕ) + 1)) (hk2 : γ ≤ 2 * (γ - (k : ℕ))) :
    IsMedian (v (σ k)) v := by
  refine ⟨?_, ?_⟩
  · -- at least half the entries are `≤ v (σ k)`: the sorted prefix `Iic k`
    have hcard :
        (Finset.Iic k).card ≤
          (Finset.univ.filter (fun b => v b ≤ v (σ k))).card := by
      refine Finset.card_le_card_of_injOn σ (fun i hi => ?_) (σ.injective.injOn)
      rw [Finset.mem_coe, Finset.mem_Iic] at hi
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmono hi⟩
    rw [Fin.card_Iic] at hcard
    omega
  · -- at least half the entries are `≥ v (σ k)`: the sorted suffix `Ici k`
    have hcard :
        (Finset.Ici k).card ≤
          (Finset.univ.filter (fun b => v (σ k) ≤ v b)).card := by
      refine Finset.card_le_card_of_injOn σ (fun i hi => ?_) (σ.injective.injOn)
      rw [Finset.mem_coe, Finset.mem_Ici] at hi
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmono hi⟩
    rw [Fin.card_Ici] at hcard
    omega

end Reduction

/-! ## The concrete median value -/

/-- The **median** of a finite family, as an actual value: the `⌊n/2⌋`-th order
statistic, i.e. the value at sorted position `⌊n/2⌋` (`Tuple.sort` sorts
ascending).  `noncomputable` because `Real`'s order is classical. -/
noncomputable def medianOf {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  if h : 0 < n then v (Tuple.sort v ⟨n / 2, Nat.div_lt_self h one_lt_two⟩) else 0

/-- **The defined `median` is a median.**  `medianOf v` satisfies the `IsMedian`
predicate: at least half the entries are `≤ medianOf v` and at least half are
`≥ medianOf v`.  Proof: reindex by the sorting permutation `σ = Tuple.sort v`;
`v ∘ σ` is monotone, so the `⌊n/2⌋+1` positions `≤ ⌊n/2⌋` land below the median
and the `⌈n/2⌉` positions `≥ ⌊n/2⌋` land above. -/
theorem isMedian_medianOf {n : ℕ} (v : Fin n → ℝ) : IsMedian (medianOf v) v := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  set σ := Tuple.sort v with hσ
  set k : Fin n := ⟨n / 2, Nat.div_lt_self hn one_lt_two⟩ with hk
  have hkval : (k : ℕ) = n / 2 := rfl
  have hmono : Monotone (v ∘ σ) := Tuple.monotone_sort v
  have hm : medianOf v = v (σ k) := by unfold medianOf; exact dif_pos hn
  refine ⟨?_, ?_⟩
  · -- lower half: `n ≤ 2 · #{b | v b ≤ medianOf v}`
    have key : (Finset.univ.filter (fun b => v b ≤ v (σ k))).card
        = (Finset.univ.filter (fun b => v (σ b) ≤ v (σ k))).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact (Equiv.sum_comp σ (fun b => if v b ≤ v (σ k) then 1 else 0)).symm
    rw [hm, key]
    have hsub : Finset.Iic k ⊆ Finset.univ.filter (fun b => v (σ b) ≤ v (σ k)) := by
      intro b hb
      rw [Finset.mem_Iic] at hb
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmono hb⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · -- upper half: `n ≤ 2 · #{b | medianOf v ≤ v b}`
    have key : (Finset.univ.filter (fun b => v (σ k) ≤ v b)).card
        = (Finset.univ.filter (fun b => v (σ k) ≤ v (σ b))).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact (Equiv.sum_comp σ (fun b => if v (σ k) ≤ v b then 1 else 0)).symm
    rw [hm, key]
    have hsub : Finset.Ici k ⊆ Finset.univ.filter (fun b => v (σ k) ≤ v (σ b)) := by
      intro b hb
      rw [Finset.mem_Ici] at hb
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmono hb⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Ici] at hcard
    omega

/-- The median of a nonnegative family is nonnegative — it is, after all, one of
the values of `v`. -/
theorem medianOf_nonneg {n : ℕ} (v : Fin n → ℝ) (h : ∀ b, 0 ≤ v b) :
    0 ≤ medianOf v := by
  unfold medianOf
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [dif_neg (by omega)]
  · rw [dif_pos hn]; exact h _

end Arlib.Probability
