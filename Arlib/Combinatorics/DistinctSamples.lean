/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A sharp coupon-collector bound for distinct samples

Draw `B` independent uniform samples from a finite set `S` with `|S| = m`, and
fix a target `N ≤ m`.  We bound the probability that the sample sequence
contains *fewer than `N` distinct values*:

  `Pr[#distinct < N] ≤ N · (1 - 1/N)^B ≤ N · exp (-B/N)`.

Because every sample is uniform on `S`, the statement is purely a *counting*
statement about the finite set of sample sequences

  `Fintype.piFinset (fun _ : Fin B => S) : Finset (Fin B → α)`,

whose cardinality is `|S|^B`; proving it by counting avoids setting up any
measure-theoretic machinery.  "Probability" below always means
`(number of bad sequences) / |S|^B`.

## Main results

* `Arlib.card_filter_lt_distinct_le` — the counting lemma, in the strengthened
  form needed for the induction: for any *seed* `Z ⊆ S` with `|Z| ≤ N`, the
  number of `ω : Fin B → α` with `|Z ∪ ω(univ)| < N` is at most
  `(N - |Z|) · (1 - 1/N)^B · m^B`.
* `Arlib.prob_lt_distinct_le` — probability form `N · (1 - 1/N)^B`.
* `Arlib.prob_lt_distinct_le_exp` — exponential form `N · exp (-B/N)`.
* `Arlib.prob_lt_distinct_le_rpow` — the budget form used by streaming
  algorithms: a budget `B ≥ β · N · logb 2 N` gives failure probability at
  most `N ^ (1 - β)`.

## Why the seed `Z`, and why the induction step is an exact identity

The induction is on `B`, *generalising over the seed* `Z`: peeling the first
coordinate of `ω : Fin (B+1) → α` turns the seed `Z` into `insert y Z` for the
peeled value `y`, so the statement about a fixed seed is not by itself
inductive.  Writing `f Z B` for the count, peeling gives the identity

  `f Z (B+1) = ∑ y ∈ S, f (insert y Z) B`

(`Arlib.card_filter_piFinset_succ` below; the fibres of `ω ↦ ω 0` are in
bijection with the shorter sample sequences via `Fin.cons` / `Fin.tail`).
Splitting the sum at `Z` — `|Z|` terms where `insert y Z = Z`, and `m - |Z|`
terms where `|insert y Z| = |Z| + 1` — and applying the induction hypothesis
gives, with `k = |Z|`, `A = N - k` and `c = 1 - 1/N`,

  `f Z (B+1) ≤ [k·A + (m - k)·(A - 1)] · c^B · m^B = [m·A - (m - k)] · c^B · m^B`.

The remaining step is the *exact algebraic identity*

  `A·c·m - (m·A - (m - k)) = k·(m - N)/N`,

which is `≥ 0` precisely because `N ≤ m`.  This is where — and the only place
where — the hypothesis `N ≤ S.card` is used: it is exactly the statement
`(N - k)/N ≤ (m - k)/m`, i.e. that after seeing `k` distinct values the chance
of a fresh sample is at least the "idealised" `(N - k)/N`.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Prelude
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Arlib.Combinatorics

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## Peeling the first coordinate -/

/-- Peeling the first sample: the sequences of length `B + 1` drawn from `S` and
satisfying `P` are fibred over their first entry `y ∈ S`, and the fibre over `y`
is in bijection (via `Fin.tail` / `Fin.cons y`) with the sequences of length `B`
satisfying `P ∘ Fin.cons y`. -/
theorem card_filter_piFinset_succ (S : Finset α) (B : ℕ)
    (P : (Fin (B + 1) → α) → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin (B + 1) => S).filter P).card
      = ∑ y ∈ S, ((Fintype.piFinset fun _ : Fin B => S).filter
          fun τ => P (Fin.cons y τ)).card := by
  have H : ∀ ω ∈ (Fintype.piFinset fun _ : Fin (B + 1) => S).filter P, ω 0 ∈ S := fun ω hω =>
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp hω).1 0
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun y hy => ?_
  refine Finset.card_nbij' (fun ω => Fin.tail ω) (fun τ => Fin.cons y τ) ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hω ⊢
    obtain ⟨⟨hmem, hP⟩, h0⟩ := hω
    refine ⟨fun i => hmem i.succ, ?_⟩
    rw [← h0, Fin.cons_self_tail]
    exact hP
  · intro τ hτ
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hτ ⊢
    obtain ⟨hmem, hP⟩ := hτ
    refine ⟨⟨?_, hP⟩, by simp⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hy
    · intro j; simpa using hmem j
  · intro ω hω
    simp only [Finset.mem_coe, Finset.mem_filter] at hω
    show Fin.cons y (Fin.tail ω) = ω
    rw [← hω.2]
    exact Fin.cons_self_tail ω
  · intro τ _
    simp

/-- The image of a consed tuple: `Fin.cons y τ` ranges over `y` together with
the range of `τ`. -/
theorem image_cons_univ (y : α) {B : ℕ} (τ : Fin B → α) :
    Finset.image (Fin.cons y τ) Finset.univ = insert y (Finset.image τ Finset.univ) := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
    revert hi
    refine Fin.cases ?_ ?_ i
    · intro h
      rw [Fin.cons_zero] at h
      exact Finset.mem_insert.mpr (Or.inl h.symm)
    · intro j h
      rw [Fin.cons_succ] at h
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩))
  · intro ha
    rcases Finset.mem_insert.mp ha with h | h
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by rw [Fin.cons_zero]; exact h.symm⟩
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, by rw [Fin.cons_succ]; exact hj⟩

/-- If the seed `Z` already has `N` or more elements, no sample sequence can
bring the total below `N`: the filtered set is empty. -/
theorem filter_lt_distinct_eq_empty (S : Finset α) (N B : ℕ) (Z : Finset α)
    (hZ : N ≤ Z.card) :
    ((Fintype.piFinset fun _ : Fin B => S).filter
      fun ω => (Z ∪ Finset.image ω Finset.univ).card < N) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro ω _
  simp only [not_lt]
  exact hZ.trans (Finset.card_le_card Finset.subset_union_left)

/-! ## The counting lemma -/

/-- **Main counting lemma.**  For a seed `Z ⊆ S` with `|Z| ≤ N`, the number of
sample sequences `ω : Fin B → α` from `S` for which `Z` together with the values
of `ω` still contains fewer than `N` elements is at most
`(N - |Z|) · (1 - 1/N)^B · |S|^B`.

The hypothesis `N ≤ S.card` enters only through the numeric inequality
`(N - k)/N ≤ (|S| - k)/|S|` at the end of the induction step. -/
theorem card_filter_lt_distinct_le (S : Finset α) (N : ℕ) (hNS : N ≤ S.card) :
    ∀ (B : ℕ) (Z : Finset α), Z ⊆ S → Z.card ≤ N →
      (((Fintype.piFinset fun _ : Fin B => S).filter
          fun ω => (Z ∪ Finset.image ω Finset.univ).card < N).card : ℝ)
        ≤ ((N - Z.card : ℕ) : ℝ) * (1 - 1 / (N : ℝ)) ^ B * (S.card : ℝ) ^ B := by
  have hc0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      have : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
  have hm0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  intro B
  induction B with
  | zero =>
    intro Z hZS hZN
    rcases lt_or_ge Z.card N with hk | hk
    · have hcard : (Fintype.piFinset fun _ : Fin 0 => S).card = 1 := by
        simp [Fintype.card_piFinset]
      have h1 : (((Fintype.piFinset fun _ : Fin 0 => S).filter
          fun ω => (Z ∪ Finset.image ω Finset.univ).card < N).card : ℝ) ≤ 1 := by
        have hle := Finset.card_filter_le (Fintype.piFinset fun _ : Fin 0 => S)
          fun ω => (Z ∪ Finset.image ω Finset.univ).card < N
        rw [hcard] at hle
        exact_mod_cast hle
      have h3 : (1 : ℝ) ≤ ((N - Z.card : ℕ) : ℝ) := by
        have : 1 ≤ N - Z.card := by omega
        exact_mod_cast this
      simpa using h1.trans h3
    · rw [filter_lt_distinct_eq_empty S N 0 Z hk, Nat.sub_eq_zero_of_le hk]
      simp
  | succ B ih =>
    intro Z hZS hZN
    rcases lt_or_ge Z.card N with hk | hk
    swap
    · rw [filter_lt_distinct_eq_empty S N (B + 1) Z hk, Nat.sub_eq_zero_of_le hk]
      simp
    -- Numeric facts, then notation.
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hk
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hZm : Z.card ≤ S.card := Finset.card_le_card hZS
    have hkm : (Z.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hZm
    have hk0 : (0 : ℝ) ≤ (Z.card : ℝ) := Nat.cast_nonneg _
    have hNm : (N : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hNS
    have hcast1 : ((N - Z.card : ℕ) : ℝ) = (N : ℝ) - (Z.card : ℝ) := by
      rw [Nat.cast_sub hk.le]
    set k : ℝ := (Z.card : ℝ) with hkdef
    set m : ℝ := (S.card : ℝ) with hmdef
    set c : ℝ := 1 - 1 / (N : ℝ) with hcdef
    -- Peel the first coordinate.
    rw [card_filter_piFinset_succ S B fun ω => (Z ∪ Finset.image ω Finset.univ).card < N,
      Nat.cast_sum]
    have hstep : ∀ y : α, ((Fintype.piFinset fun _ : Fin B => S).filter
        fun τ => (Z ∪ Finset.image (Fin.cons y τ) Finset.univ).card < N)
        = ((Fintype.piFinset fun _ : Fin B => S).filter
            fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N) := by
      intro y
      refine Finset.filter_congr fun τ _ => ?_
      rw [image_cons_univ, Finset.union_insert, Finset.insert_union]
    -- The induction hypothesis, applied to the enlarged seed.
    have hIH : ∀ y ∈ S, ((((Fintype.piFinset fun _ : Fin B => S).filter
        fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ))
        ≤ ((N - (insert y Z).card : ℕ) : ℝ) * c ^ B * m ^ B := by
      intro y hy
      refine ih (insert y Z) (Finset.insert_subset hy hZS) ?_
      have := Finset.card_insert_le y Z
      omega
    -- Split the sum over `S` into `Z` and `S \ Z`.
    have hsum : ∑ y ∈ S, (((Fintype.piFinset fun _ : Fin B => S).filter
          fun τ => (Z ∪ Finset.image (Fin.cons y τ) Finset.univ).card < N).card : ℝ)
        = (∑ y ∈ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
              fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ))
          + ∑ y ∈ S \ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
              fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ) := by
      have : ∀ y : α, (((Fintype.piFinset fun _ : Fin B => S).filter
          fun τ => (Z ∪ Finset.image (Fin.cons y τ) Finset.univ).card < N).card : ℝ)
          = (((Fintype.piFinset fun _ : Fin B => S).filter
              fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ) := by
        intro y; rw [hstep y]
      simp only [this]
      rw [← Finset.sum_sdiff hZS]
      ring
    rw [hsum]
    -- Bound the two pieces.
    have hpow0 : (0 : ℝ) ≤ c ^ B * m ^ B := mul_nonneg (pow_nonneg hc0 _) (pow_nonneg hm0 _)
    have hA : ∑ y ∈ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
          fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ)
        ≤ k * (((N : ℝ) - k) * (c ^ B * m ^ B)) := by
      calc ∑ y ∈ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
              fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ)
          ≤ ∑ _y ∈ Z, ((N : ℝ) - k) * (c ^ B * m ^ B) := by
            refine Finset.sum_le_sum fun y hy => ?_
            have hyZ : insert y Z = Z := Finset.insert_eq_self.mpr hy
            have hb := hIH y (hZS hy)
            rw [hyZ, hcast1] at hb
            rw [hyZ]
            linarith [hb]
        _ = k * (((N : ℝ) - k) * (c ^ B * m ^ B)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hkdef]
    have hB : ∑ y ∈ S \ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
          fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ)
        ≤ (m - k) * (((N : ℝ) - k - 1) * (c ^ B * m ^ B)) := by
      calc ∑ y ∈ S \ Z, (((Fintype.piFinset fun _ : Fin B => S).filter
              fun τ => (insert y Z ∪ Finset.image τ Finset.univ).card < N).card : ℝ)
          ≤ ∑ _y ∈ S \ Z, ((N : ℝ) - k - 1) * (c ^ B * m ^ B) := by
            refine Finset.sum_le_sum fun y hy => ?_
            have hyZ : y ∉ Z := (Finset.mem_sdiff.mp hy).2
            have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
            have hcard : (insert y Z).card = Z.card + 1 :=
              Finset.card_insert_of_notMem hyZ
            have hc2 : ((N - (insert y Z).card : ℕ) : ℝ) = (N : ℝ) - k - 1 := by
              rw [hcard, Nat.cast_sub (by omega), hkdef]
              push_cast
              ring
            have := hIH y hyS
            rw [hc2] at this
            linarith [this]
        _ = (m - k) * (((N : ℝ) - k - 1) * (c ^ B * m ^ B)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hZS,
              Nat.cast_sub hZm, hkdef, hmdef]
    -- The exact algebraic identity that makes the induction close.
    have key : k * ((N : ℝ) - k) + (m - k) * ((N : ℝ) - k - 1) ≤ ((N : ℝ) - k) * c * m := by
      have hid : ((N : ℝ) - k) * c * m - (k * ((N : ℝ) - k) + (m - k) * ((N : ℝ) - k - 1))
          = k * (m - (N : ℝ)) / (N : ℝ) := by
        rw [hcdef]
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ k * (m - (N : ℝ)) / (N : ℝ) :=
        div_nonneg (mul_nonneg hk0 (by linarith)) hNr.le
      rw [← sub_nonneg, hid]
      exact hnn
    have hfinal : k * (((N : ℝ) - k) * (c ^ B * m ^ B))
        + (m - k) * (((N : ℝ) - k - 1) * (c ^ B * m ^ B))
        ≤ ((N : ℝ) - k) * c ^ (B + 1) * m ^ (B + 1) := by
      have hmul : (k * ((N : ℝ) - k) + (m - k) * ((N : ℝ) - k - 1)) * (c ^ B * m ^ B)
          ≤ (((N : ℝ) - k) * c * m) * (c ^ B * m ^ B) :=
        mul_le_mul_of_nonneg_right key hpow0
      calc k * (((N : ℝ) - k) * (c ^ B * m ^ B))
            + (m - k) * (((N : ℝ) - k - 1) * (c ^ B * m ^ B))
          = (k * ((N : ℝ) - k) + (m - k) * ((N : ℝ) - k - 1)) * (c ^ B * m ^ B) := by ring
        _ ≤ (((N : ℝ) - k) * c * m) * (c ^ B * m ^ B) := hmul
        _ = ((N : ℝ) - k) * c ^ (B + 1) * m ^ (B + 1) := by ring
    rw [hcast1]
    linarith [hA, hB, hfinal]

/-! ## Probability forms -/

/-- **Probability form.**  With `B` uniform samples from `S` and `N ≤ |S|`, the
fraction of sample sequences containing fewer than `N` distinct values is at
most `N · (1 - 1/N)^B`. -/
theorem prob_lt_distinct_le (S : Finset α) (hS : S.Nonempty) (N B : ℕ) (hNS : N ≤ S.card) :
    ((((Fintype.piFinset fun _ : Fin B => S).filter
        fun ω => (Finset.image ω Finset.univ).card < N).card : ℝ) / (S.card : ℝ) ^ B)
      ≤ (N : ℝ) * (1 - 1 / (N : ℝ)) ^ B := by
  have hmpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    exact_mod_cast this
  have hpow : (0 : ℝ) < (S.card : ℝ) ^ B := pow_pos hmpos B
  have hmain := card_filter_lt_distinct_le S N hNS B ∅ (Finset.empty_subset _) (by simp)
  simp only [Finset.card_empty, Nat.sub_zero, Finset.empty_union] at hmain
  rw [div_le_iff₀ hpow]
  exact hmain

/-- **Exponential form.**  Using `1 - x ≤ exp (-x)`. -/
theorem prob_lt_distinct_le_exp (S : Finset α) (hS : S.Nonempty) (N B : ℕ) (hNS : N ≤ S.card) :
    ((((Fintype.piFinset fun _ : Fin B => S).filter
        fun ω => (Finset.image ω Finset.univ).card < N).card : ℝ) / (S.card : ℝ) ^ B)
      ≤ (N : ℝ) * Real.exp (-(B : ℝ) / N) := by
  refine (prob_lt_distinct_le S hS N B hNS).trans ?_
  have hc0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
  have hstep : (1 - 1 / (N : ℝ)) ≤ Real.exp (-(1 / (N : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (N : ℝ)))
    linarith
  have hpow : (1 - 1 / (N : ℝ)) ^ B ≤ Real.exp (-(1 / (N : ℝ))) ^ B :=
    pow_le_pow_left₀ hc0 hstep B
  have hexp : Real.exp (-(1 / (N : ℝ))) ^ B = Real.exp (-(B : ℝ) / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- **Budget form**, as used by streaming algorithms: a budget of
`B ≥ β · N · logb 2 N` samples brings the failure probability down to
`N ^ (1 - β)`.  The slack comes from `1 / Real.log 2 > 1`. -/
theorem prob_lt_distinct_le_rpow (S : Finset α) (hS : S.Nonempty) (N B : ℕ)
    (hNS : N ≤ S.card) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hB : β * N * Real.logb 2 N ≤ B) :
    ((((Fintype.piFinset fun _ : Fin B => S).filter
        fun ω => (Finset.image ω Finset.univ).card < N).card : ℝ) / (S.card : ℝ) ^ B)
      ≤ (N : ℝ) ^ (1 - β) := by
  refine (prob_lt_distinct_le_exp S hS N B hNS).trans ?_
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  -- Step 1: the exponent shrinks.
  have hexpo : -(B : ℝ) / N ≤ -(β * Real.logb 2 N) := by
    rw [div_le_iff₀ hNpos]
    have : β * N * Real.logb 2 N ≤ (B : ℝ) := hB
    nlinarith [this]
  have h1 : Real.exp (-(B : ℝ) / N) ≤ Real.exp (-(β * Real.logb 2 N)) :=
    Real.exp_le_exp.mpr hexpo
  -- Step 2: rewrite the exponential as an rpow of `N`.
  have h2 : Real.exp (-(β * Real.logb 2 N)) = (N : ℝ) ^ (-(β / Real.log 2)) := by
    have harg : -(β * Real.logb 2 (N : ℝ)) = Real.log (N : ℝ) * (-(β / Real.log 2)) := by
      rw [Real.logb]; ring
    rw [harg, ← Real.rpow_def_of_pos hNpos]
  -- Step 3: `-(β / log 2) ≤ -β` since `log 2 ≤ 1` and `β ≥ 0`.
  have h3 : (N : ℝ) ^ (-(β / Real.log 2)) ≤ (N : ℝ) ^ (-β) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hβl : β ≤ β / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      nlinarith
    linarith
  -- Step 4: `N * N ^ (-β) = N ^ (1 - β)`.
  have h4 : (N : ℝ) * (N : ℝ) ^ (-β) = (N : ℝ) ^ (1 - β) := by
    rw [sub_eq_add_neg, Real.rpow_add hNpos, Real.rpow_one]
  calc (N : ℝ) * Real.exp (-(B : ℝ) / N)
      ≤ (N : ℝ) * Real.exp (-(β * Real.logb 2 N)) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = (N : ℝ) * (N : ℝ) ^ (-(β / Real.log 2)) := by rw [h2]
    _ ≤ (N : ℝ) * (N : ℝ) ^ (-β) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = (N : ℝ) ^ (1 - β) := h4

end Arlib.Combinatorics
