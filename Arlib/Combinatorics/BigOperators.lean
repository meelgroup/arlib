/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Generic `Finset` sum / product helper lemmas

Reusable `BigOperators` facts that recur across combinatorial developments but
are not in Mathlib under an obvious name:

* the diagonal / off-diagonal split of a double sum (`sum_matrix_diag_offdiag`);
* products of an **idempotent** function over subsets / unions / `biUnion`s
  (`prod_mul_prod_subset`, `prod_union_idem`, `prod_biUnion_idem`);
* a surjection–product inequality (`prod_le_prod_comp_of_surj`);
* products of `{0,1}`-valued functions (`prod_zero_or_one`, `zo_prod_eq_one_iff`).

All are stated over generic types.  No `sorry`.
-/
import Arlib.Prelude
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Arlib.Combinatorics

open Finset

/-! ## Splitting a double sum into diagonal and off-diagonal parts -/

/-- Split a double sum over `I × I` into its diagonal `∑ i, c i i` and the
off-diagonal remainder `∑ i, ∑ j ∈ I.erase i, c i j`. -/
theorem sum_matrix_diag_offdiag {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (c : ι → ι → ℝ) :
    ∑ i ∈ I, ∑ j ∈ I, c i j
      = (∑ i ∈ I, c i i) + ∑ i ∈ I, ∑ j ∈ I.erase i, c i j := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.add_sum_erase I (c i) hi]

/-! ## Products of an idempotent function -/

/-- For `t ⊆ s` and `f` idempotent on `t` (`f x * f x = f x`), multiplying the
`s`-product by the `t`-product changes nothing. -/
theorem prod_mul_prod_subset {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {s t : Finset ι}
    (hst : t ⊆ s) (hidem : ∀ x ∈ t, f x * f x = f x) :
    (∏ x ∈ s, f x) * (∏ x ∈ t, f x) = ∏ x ∈ s, f x := by
  have hsp : ∏ x ∈ s, f x = (∏ x ∈ s \ t, f x) * ∏ x ∈ t, f x :=
    (Finset.prod_sdiff hst).symm
  rw [hsp, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl hidem

/-- For a globally idempotent `f`, the product over a union is the product of the
two products. -/
theorem prod_union_idem {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    (hidem : ∀ i, f i * f i = f i) (A B : Finset ι) :
    (∏ i ∈ A, f i) * (∏ i ∈ B, f i) = ∏ i ∈ A ∪ B, f i := by
  have hsub : A ∩ B ⊆ A ∪ B := Finset.inter_subset_left.trans Finset.subset_union_left
  have hkey : (∏ i ∈ A ∪ B, f i) * (∏ i ∈ A ∩ B, f i) = ∏ i ∈ A ∪ B, f i := by
    calc (∏ i ∈ A ∪ B, f i) * (∏ i ∈ A ∩ B, f i)
        = ((∏ i ∈ (A ∪ B) \ (A ∩ B), f i) * (∏ i ∈ A ∩ B, f i)) * (∏ i ∈ A ∩ B, f i) := by
          rw [Finset.prod_sdiff hsub]
      _ = (∏ i ∈ (A ∪ B) \ (A ∩ B), f i) * ((∏ i ∈ A ∩ B, f i) * (∏ i ∈ A ∩ B, f i)) := by ring
      _ = (∏ i ∈ (A ∪ B) \ (A ∩ B), f i) * (∏ i ∈ A ∩ B, f i) := by
          rw [← Finset.prod_mul_distrib]
          exact congrArg _ (Finset.prod_congr rfl (fun x _ => hidem x))
      _ = ∏ i ∈ A ∪ B, f i := Finset.prod_sdiff hsub
  rw [← Finset.prod_union_inter, hkey]

/-- For a globally idempotent `f`, a nested product over a `biUnion` collapses to
a single product over the `biUnion`. -/
theorem prod_biUnion_idem {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {f : ι' → ℝ}
    (hidem : ∀ i, f i * f i = f i) (g : ι → Finset ι') (W : Finset ι) :
    (∏ i ∈ W, ∏ c ∈ g i, f c) = ∏ c ∈ W.biUnion g, f c := by
  classical
  induction W using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.biUnion_insert, ← prod_union_idem hidem]

/-! ## A surjection–product inequality -/

/-- If `t ⊆ s.image f` and `g (f i) ≥ 1` on `s`, then `∏_{k ∈ t} g k ≤ ∏_{i ∈ s} g (f i)`. -/
theorem prod_le_prod_comp_of_surj {ι κ : Type*} [DecidableEq κ]
    {s : Finset ι} {t : Finset κ} {f : ι → κ} {g : κ → ℝ}
    (hsub : t ⊆ s.image f) (hge1 : ∀ i ∈ s, 1 ≤ g (f i)) :
    ∏ k ∈ t, g k ≤ ∏ i ∈ s, g (f i) := by
  have hg1img : ∀ k ∈ s.image f, 1 ≤ g k := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact hge1 i hi
  have hone : (1 : ℝ) ≤ ∏ k ∈ (s.image f) \ t, g k := by
    calc (1 : ℝ) = ∏ _k ∈ (s.image f) \ t, (1 : ℝ) := (Finset.prod_const_one).symm
      _ ≤ ∏ k ∈ (s.image f) \ t, g k :=
          Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun k hk => hg1img k (Finset.mem_sdiff.mp hk).1)
  have hprodt_nn : 0 ≤ ∏ k ∈ t, g k :=
    Finset.prod_nonneg (fun k hk => le_trans zero_le_one (hg1img k (hsub hk)))
  have hstep1 : ∏ k ∈ t, g k ≤ ∏ k ∈ s.image f, g k := by
    rw [← Finset.prod_sdiff hsub]
    exact le_mul_of_one_le_left hprodt_nn hone
  have hfib : ∏ k ∈ s.image f, ∏ i ∈ s.filter (fun i => f i = k), g (f i)
      = ∏ i ∈ s, g (f i) :=
    Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _
  have hstep2 : ∏ k ∈ s.image f, g k ≤ ∏ i ∈ s, g (f i) := by
    rw [← hfib]
    refine Finset.prod_le_prod (fun k hk => le_trans zero_le_one (hg1img k hk)) (fun k hk => ?_)
    have hconst : ∏ i ∈ s.filter (fun i => f i = k), g (f i)
        = (g k) ^ (s.filter (fun i => f i = k)).card := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
          Finset.prod_const]
    rw [hconst]
    have hne : (s.filter (fun i => f i = k)).card ≠ 0 := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨hi, rfl⟩)
    exact le_self_pow₀ (hg1img k hk) hne
  exact le_trans hstep1 hstep2

/-! ## Products of `{0,1}`-valued functions -/

/-- A finite product of `{0,1}`-valued reals is again `{0,1}`-valued. -/
theorem prod_zero_or_one {α : Type*} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, f x = 0 ∨ f x = 1) : (∏ x ∈ s, f x) = 0 ∨ (∏ x ∈ s, f x) = 1 := by
  refine Finset.prod_induction f (fun x => x = 0 ∨ x = 1) (fun a b ha hb => ?_) (Or.inr rfl) h
  rcases ha with rfl | rfl
  · exact Or.inl (by ring)
  · rcases hb with rfl | rfl
    · exact Or.inl (by ring)
    · exact Or.inr (by ring)

/-- A product of `{0,1}`-valued reals equals `1` iff every factor equals `1`. -/
theorem zo_prod_eq_one_iff {α : Type*} (A : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ A, f x = 0 ∨ f x = 1) :
    (∏ x ∈ A, f x) = 1 ↔ ∀ x ∈ A, f x = 1 := by
  constructor
  · intro hp x hx
    rcases h x hx with h0 | h1
    · exfalso
      have hz : (∏ x ∈ A, f x) = 0 := Finset.prod_eq_zero hx h0
      rw [hz] at hp; norm_num at hp
    · exact h1
  · exact fun hh => Finset.prod_eq_one hh

end Arlib.Combinatorics
