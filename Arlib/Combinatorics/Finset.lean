/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# General `Finset` helper lemmas

A small collection of generic `Finset` facts that are not in Mathlib under an
obvious name and that recur across combinatorial developments:

* membership in a list-accumulated union `List.foldr (· ∪ ·) ∅`
  (`mem_foldr_union`, and its mapped form `mem_foldr_union_map`);
* the powerset of a union as the `∪`-image of the product of powersets
  (`image_union_powerset`);
* recovering a summand of a disjoint union by intersecting with its support
  (`union_inter_left`, `union_inter_right`).

All are stated over an arbitrary `[DecidableEq α]`.  No `sorry`.
-/
import Arlib.Prelude
import Mathlib.Order.Interval.Finset.Nat

namespace Arlib.Combinatorics

open Finset

/-! ## Tiling an interval by consecutive blocks -/

/-- `nt` consecutive length-`ns` blocks, indexed by `Fin nt`, tile the single
interval `Ico (N·ns + 1) ((N+nt)·ns + 1)`. -/
theorem Ico_biUnion_blocks (N nt ns : ℕ) :
    (Finset.univ.biUnion (fun b : Fin nt =>
        Finset.Ico ((N + b.val) * ns + 1) ((N + b.val + 1) * ns + 1)))
      = Finset.Ico (N * ns + 1) ((N + nt) * ns + 1) := by
  have e3 : (N + nt) * ns = N * ns + ns * nt := by ring
  ext r
  constructor
  · intro hr
    obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp hr
    rw [Finset.mem_Ico] at hb ⊢
    obtain ⟨hlo, hhi⟩ := hb
    have hblt : b.val < nt := b.isLt
    have e1 : (N + b.val) * ns = N * ns + ns * b.val := by ring
    have e2 : (N + b.val + 1) * ns = N * ns + ns * b.val + ns := by ring
    have e4 : ns * b.val + ns ≤ ns * nt := by
      calc ns * b.val + ns = ns * (b.val + 1) := by ring
        _ ≤ ns * nt := Nat.mul_le_mul_left ns (by omega)
    omega
  · intro hr
    rw [Finset.mem_Ico] at hr
    obtain ⟨hlo, hhi⟩ := hr
    have hprod : 0 < ns * nt := by omega
    have hns : 0 < ns := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hprod)
    obtain ⟨q, s, hq, hs, hqs⟩ :
        ∃ q s : ℕ, q < nt ∧ s < ns ∧ r - 1 - N * ns = ns * q + s := by
      refine ⟨(r - 1 - N * ns) / ns, (r - 1 - N * ns) % ns, ?_, Nat.mod_lt _ hns,
        (Nat.div_add_mod _ ns).symm⟩
      refine (Nat.div_lt_iff_lt_mul hns).mpr ?_
      have : nt * ns = ns * nt := Nat.mul_comm _ _
      omega
    refine Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, Finset.mem_univ _, ?_⟩
    show r ∈ Finset.Ico ((N + q) * ns + 1) ((N + q + 1) * ns + 1)
    rw [Finset.mem_Ico]
    have e1 : (N + q) * ns = N * ns + ns * q := by ring
    have e2 : (N + q + 1) * ns = N * ns + ns * q + ns := by ring
    omega

/-! ## Counting a concatenation product -/

/-- The map `(a, b) ↦ a ++ b` is injective on `A ×ˢ B` when every word of `A`
shares a common length `la` (so the split point is determined). -/
theorem concat_injOn {α : Type*} [DecidableEq α] (A B : Finset (List α)) {la : ℕ}
    (hA : ∀ a ∈ A, a.length = la) :
    Set.InjOn (fun p : List α × List α => p.1 ++ p.2) (A ×ˢ B : Finset _) := by
  intro p hp q hq hpq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
  have hlen : p.1.length = q.1.length := by
    rw [hA p.1 hp.1, hA q.1 hq.1]
  obtain ⟨h1, h2⟩ := List.append_inj hpq hlen
  exact Prod.ext_iff.2 ⟨h1, h2⟩

/-- **Concatenation counting bound.**  If every equal-length word of `A`,
concatenated with every word of `B`, lands in `C`, then `|A|·|B| ≤ |C|`. -/
theorem card_mul_le_of_concat_subset {α : Type*} [DecidableEq α]
    (A B C : Finset (List α)) {la : ℕ}
    (hA : ∀ a ∈ A, a.length = la)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ++ b ∈ C) :
    A.card * B.card ≤ C.card := by
  have himg : (A ×ˢ B).image (fun p => p.1 ++ p.2) ⊆ C := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    rw [Finset.mem_product] at hp
    exact hAB p.1 hp.1 p.2 hp.2
  have hcard : ((A ×ˢ B).image (fun p => p.1 ++ p.2)).card = A.card * B.card := by
    rw [Finset.card_image_of_injOn (concat_injOn A B hA), Finset.card_product]
  calc A.card * B.card
      = ((A ×ˢ B).image (fun p => p.1 ++ p.2)).card := hcard.symm
    _ ≤ C.card := Finset.card_le_card himg

/-! ## Membership in a list-accumulated union -/

/-- Membership in a `foldr (· ∪ ·) ∅` of a list of finsets: an element lies in
the accumulated union iff it lies in one of the listed finsets. -/
theorem mem_foldr_union {α : Type*} [DecidableEq α] (L : List (Finset α)) (w : α) :
    w ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ L, w ∈ s := by
  induction L with
  | nil => simp
  | cons s t ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (hs | ⟨u, hu, hw⟩)
      · exact ⟨s, Or.inl rfl, hs⟩
      · exact ⟨u, Or.inr hu, hw⟩
    · rintro ⟨u, rfl | hu, hw⟩
      · exact Or.inl hw
      · exact Or.inr ⟨u, hu, hw⟩

/-- Membership in a `foldr (· ∪ ·) ∅` of a *mapped* list. -/
theorem mem_foldr_union_map {α β : Type*} [DecidableEq β] (L : List α) (f : α → Finset β)
    (w : β) : w ∈ (L.map f).foldr (· ∪ ·) ∅ ↔ ∃ x ∈ L, w ∈ f x := by
  rw [mem_foldr_union]
  simp only [List.mem_map]
  constructor
  · rintro ⟨s, ⟨x, hx, rfl⟩, hw⟩; exact ⟨x, hx, hw⟩
  · rintro ⟨x, hx, hw⟩; exact ⟨f x, ⟨x, hx, rfl⟩, hw⟩

/-! ## Powerset of a union -/

/-- The powerset of a union is the `∪`-image of the product of the powersets
(no disjointness needed for the set identity). -/
theorem image_union_powerset {α : Type*} [DecidableEq α] (S T : Finset α) :
    (S.powerset ×ˢ T.powerset).image (fun p => p.1 ∪ p.2) = (S ∪ T).powerset := by
  ext u
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact Finset.union_subset (ha.trans Finset.subset_union_left)
      (hb.trans Finset.subset_union_right)
  · intro hu
    refine ⟨(u ∩ S, u ∩ T), ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩, ?_⟩
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hu]

/-! ## Recovering a summand of a disjoint union -/

/-- `(a ∪ b) ∩ V = a` when `a ⊆ V`, `b ⊆ W`, and `V, W` are disjoint. -/
theorem union_inter_left {α : Type*} [DecidableEq α] {a b V W : Finset α}
    (ha : a ⊆ V) (hb : b ⊆ W) (hdis : Disjoint V W) : (a ∪ b) ∩ V = a := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 ha]
  have hbV : b ∩ V = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_of_subset_left hb hdis.symm)
  rw [hbV, Finset.union_empty]

/-- `(a ∪ b) ∩ W = b` when `a ⊆ V`, `b ⊆ W`, and `V, W` are disjoint. -/
theorem union_inter_right {α : Type*} [DecidableEq α] {a b V W : Finset α}
    (ha : a ⊆ V) (hb : b ⊆ W) (hdis : Disjoint V W) : (a ∪ b) ∩ W = b := by
  rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 hb]
  have haW : a ∩ W = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_of_subset_left ha hdis)
  rw [haW, Finset.empty_union]

end Arlib.Combinatorics
