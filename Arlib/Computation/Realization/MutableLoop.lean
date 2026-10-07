/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization
import Arlib.Computation.WordLoop
import Mathlib.Data.List.Range

/-!
# Relational refinement of mutable word-counter loops

An invariant relates different abstract/concrete accumulators in the current
machine state. Bodies may write or allocate: each executed body must reestablish
the invariant. On `none`, the old accumulator remains the result, so its
representation must survive the body's effects. Body costs are needed only for
represented states at guarded indices. Fuel describes the abstract range too;
complete traversal requires the caller to supply the full intended range.
-/
namespace Arlib.Computation.Realizes

variable {κ κₛ : Type} {α β : Type} {w : ℕ}

/-- Public value recurrence of the unchanged abstract early-exit fold. -/
theorem foldlWhile_cons (f : α → ℕ → Charged κ κₛ (Option α))
    (i : ℕ) (xs : List ℕ) (a : α) :
    (Charged.foldlWhile f (i :: xs) a).val =
      match (f a i).val with
      | none => a
      | some a' => (Charged.foldlWhile f xs a').val := by
  cases h : (f a i).val <;>
    simp [Charged.foldlWhile, Charged.val] at h ⊢ <;> simp [h]

/-- A mutable body's early-exit result relation. `none` must preserve the
representation of the prior accumulator in the updated memory state. -/
def LoopResult (R : α → β → RamState w → Prop) (a : α) (b : β)
    (a' : Option α) (b' : Option β) (σ : RamState w) : Prop :=
  match a', b' with
  | none, none => R a b σ
  | some x, some y => R x y σ
  | _, _ => False

/-- A word-loop invariant and bound. The abstract and concrete body results
need not have the same type or representation. -/
theorem mutableWordLoopGo
    (f : ℕ → α → Charged κ κₛ (Option α))
    (body : Word w → β → RAM w (Option β)) (limit one : Word w)
    (R : α → β → RamState w → Prop) (bodyBound : ℕ)
    (hone : one.toNat = 1)
    (hbody : ∀ index a b σ, index.toNat < limit.toNat → R a b σ →
      LoopResult R a b (f index.toNat a).val ((body index b).val σ)
        ((body index b).state σ))
    (hcost : ∀ index a b σ, index.toNat < limit.toNat → R a b σ →
      RAM.steps CostModel.unitCost (body index b) σ ≤ bodyBound) :
    ∀ fuel index a b σ, index.toNat + fuel ≤ limit.toNat → R a b σ →
      R (Charged.foldlWhile (fun a i => f i a) (List.range' index.toNat fuel) a).val
          ((wordLoopGo body limit one fuel index b).val σ)
          ((wordLoopGo body limit one fuel index b).state σ) ∧
        RAM.steps CostModel.unitCost (wordLoopGo body limit one fuel index b) σ
          ≤ 1 + fuel * (bodyBound + 2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro index a b σ _ hR
      simpa [wordLoopGo] using hR
  | succ fuel ih =>
      intro index a b σ hremaining hR
      have hi : index.toNat < limit.toNat := by omega
      have hc := hcost index a b σ hi hR
      have hr := hbody index a b σ hi hR
      simp only [List.range'_succ, foldlWhile_cons]
      simp only [wordLoopGo, RAM.val_bind, RAM.state_bind, RAM.steps_bind,
        state_lt, val_lt, steps_lt, CostModel.unitCost_cost]
      simp only [hi, decide_true, if_true, RAM.val_bind, RAM.state_bind, RAM.steps_bind]
      cases ha : (f index.toNat a).val with
      | none =>
          cases hb : (body index b).val σ with
          | none =>
              simp only [ha, hb, LoopResult] at hr
              simp only [RAM.val_pure, RAM.state_pure, RAM.steps_pure]
              exact ⟨hr, by nlinarith⟩
          | some b' => simp [ha, hb, LoopResult] at hr
      | some a' =>
          cases hb : (body index b).val σ with
          | none => simp [ha, hb, LoopResult] at hr
          | some b' =>
              simp only [ha, hb, LoopResult] at hr
              have hfit : index.toNat + 1 < 2 ^ w :=
                lt_of_le_of_lt (by omega) limit.toNat_lt
              have hindex : ((add index one).val ((body index b).state σ)).toNat =
                  index.toNat + 1 := by
                simp [toNat_add, hone, Nat.mod_eq_of_lt hfit]
              have htail := ih ((add index one).val ((body index b).state σ))
                a' b' ((body index b).state σ) (by rw [hindex]; omega) hr
              simp only [RAM.val_bind, RAM.state_bind, RAM.steps_bind,
                state_add, steps_add, CostModel.unitCost_cost]
              constructor
              · simpa only [hindex] using htail.1
              · have ht := htail.2
                nlinarith

/-- Package relational mutable iteration as an implementation of the existing
Charged range fold. Fuel coverage is explicit in the input precondition. -/
theorem mutableWordLoop
    (f : ℕ → α → Charged κ κₛ (Option α))
    (body : Word w → β → RAM w (Option β)) (fuel : ℕ) (limit : Word w)
    (a : α) (b : β) (R : α → β → RamState w → Prop) (bodyBound : ℕ)
    (hwidth : 1 < 2 ^ w)
    (hbody : ∀ index a b σ, index.toNat < limit.toNat → R a b σ →
      LoopResult R a b (f index.toNat a).val ((body index b).val σ)
        ((body index b).state σ))
    (hcost : ∀ index a b σ, index.toNat < limit.toNat → R a b σ →
      RAM.steps CostModel.unitCost (body index b) σ ≤ bodyBound) :
    Realizes (Charged.foldlWhile (fun a i => f i a) (List.range fuel) a)
      (wordRepeatWhile fuel limit body b)
      (fun σ => R a b σ ∧ fuel ≤ limit.toNat) R
      (3 + fuel * (bodyBound + 2)) where
  correct := by
    intro σ h
    have hz : ((lit 0 : RAM w (Word w)).val σ).toNat = 0 := by simp
    have ho : ((lit 1 : RAM w (Word w)).val σ).toNat = 1 := by
      simp [Nat.mod_eq_of_lt hwidth]
    have result := mutableWordLoopGo f body limit ((lit 1).val σ) R bodyBound
      ho hbody hcost fuel ((lit 0).val σ) a b σ (by simpa [hz] using h.2) h.1
    simpa only [wordRepeatWhile, RAM.val_bind, RAM.state_bind, state_lit, hz,
      ← List.range_eq_range'] using result.1
  steps_le := by
    intro σ h
    have hz : ((lit 0 : RAM w (Word w)).val σ).toNat = 0 := by simp
    have ho : ((lit 1 : RAM w (Word w)).val σ).toNat = 1 := by
      simp [Nat.mod_eq_of_lt hwidth]
    have result := mutableWordLoopGo f body limit ((lit 1).val σ) R bodyBound
      ho hbody hcost fuel ((lit 0).val σ) a b σ (by simpa [hz] using h.2) h.1
    simp only [wordRepeatWhile, RAM.steps_bind, state_lit, steps_lit,
      CostModel.unitCost_cost]
    have ht := result.2
    omega

end Arlib.Computation.Realizes
