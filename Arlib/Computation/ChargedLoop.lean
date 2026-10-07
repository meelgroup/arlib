/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.ExactRealization
import Arlib.Computation.WordLoop

/-! # Sealed-index charged loops

The source and RAM loops both pay initialization, every guard (including on fuel
exhaustion), and each continuing increment. `none` stops without replacing the
accumulator or incrementing. A full-traversal claim needs adequate fuel and a
nonwrapping counter; exact correspondence also covers intentional truncation.
-/
namespace Arlib.Computation
namespace ChargedLoop
attribute [local simp] val_add_empty val_lit_empty
variable {w : Nat} {κₛ : Type} {α β : Type}

def go (body : Word w → α → Charged Op κₛ (Option α))
    (limit one : Word w) : Nat → Word w → α → Charged Op κₛ α
  | 0, index, acc => do
      let _ ← ChargedWord.lt index limit
      pure acc
  | fuel+1, index, acc => do
      let more ← ChargedWord.lt index limit
      if more then
        let next ← body index acc
        match next with
        | none => pure acc
        | some acc' => do
            let index' ← ChargedWord.add index one
            go body limit one fuel index' acc'
      else pure acc

def repeatWhile (fuel : Nat) (limit : Word w)
    (body : Word w → α → Charged Op κₛ (Option α)) (acc : α) : Charged Op κₛ α := do
  let zero ← ChargedWord.literal 0
  let one ← ChargedWord.literal 1
  go body limit one fuel zero acc

/-- The early-exit result relation retains the old accumulators on `none`. -/
def OptionRel (R : α → β → RamState w → Prop) (a : α) (b : β)
    (x : Option α) (y : Option β) (σ : RamState w) : Prop :=
  match x,y with
  | none, none => R a b σ
  | some a', some b' => R a' b' σ
  | _, _ => False

theorem exact_go (body : Word w → α → Charged Op κₛ (Option α))
    (ram : Word w → β → RAM w (Option β)) (limit one : Word w)
    (R : α → β → RamState w → Prop)
    (hbody : ∀ i a b, ExactRealizes (body i a) (ram i b)
      (fun σ => R a b σ ∧ i.toNat < limit.toNat) (OptionRel R a b))
    (fuel : Nat) (index : Word w) (a : α) (b : β) :
    ExactRealizes (go body limit one fuel index a)
      (wordLoopGo ram limit one fuel index b) (R a b) R := by
  induction fuel generalizing index a b with
  | zero =>
    constructor
    · intro σ H; simpa [go, wordLoopGo] using H
    · intro σ _; simp [go, wordLoopGo]
  | succ fuel ih =>
    constructor
    · intro σ H
      by_cases hm : index.toNat < limit.toNat
      · have hc := (hbody index a b).correct σ ⟨H,hm⟩
        cases hs : (body index a).val with
        | none =>
          cases ht : (ram index b).val σ with
          | none => simpa [go, wordLoopGo, ChargedWord.val_lt_nat, hm, hs, ht, OptionRel] using hc
          | some b' => simp [OptionRel, hs, ht] at hc
        | some a' =>
          cases ht : (ram index b).val σ with
          | none => simp [OptionRel, hs, ht] at hc
          | some b' =>
            have hr := (ih ((Arlib.Computation.add index one).val σ) a' b').correct
              ((ram index b).state σ) (by simpa [OptionRel, hs, ht] using hc)
            simpa [go, wordLoopGo, ChargedWord.val_lt_nat, ChargedWord.val_add _ _ (RamState.empty w), ChargedWord.cost_add, hm, hs, ht] using hr
      · simpa [go, wordLoopGo, ChargedWord.val_lt_nat, hm] using H
    · intro σ H
      by_cases hm : index.toNat < limit.toNat
      · have hc := (hbody index a b).correct σ ⟨H,hm⟩
        have he := (hbody index a b).cost_eq σ ⟨H,hm⟩
        cases hs : (body index a).val with
        | none =>
          cases ht : (ram index b).val σ with
          | none => simp [go, wordLoopGo, ChargedWord.val_lt_nat, hm, hs, ht, he]
          | some b' => simp [OptionRel, hs, ht] at hc
        | some a' =>
          cases ht : (ram index b).val σ with
          | none => simp [OptionRel, hs, ht] at hc
          | some b' =>
            have hr := (ih ((Arlib.Computation.add index one).val σ) a' b').cost_eq
              ((ram index b).state σ) (by simpa [OptionRel, hs, ht] using hc)
            simpa [go, wordLoopGo, ChargedWord.val_lt_nat, ChargedWord.val_add _ _ (RamState.empty w), ChargedWord.cost_add, hm, hs, ht, he] using
              congrArg (fun c => CostVec.one Op.lt +
                ((ram index b).cost σ + (CostVec.one Op.add + c))) hr
      · simp [go, wordLoopGo, ChargedWord.val_lt_nat, hm]

theorem exact_repeatWhile (body : Word w → α → Charged Op κₛ (Option α))
    (ram : Word w → β → RAM w (Option β)) (limit : Word w)
    (R : α → β → RamState w → Prop)
    (hbody : ∀ i a b, ExactRealizes (body i a) (ram i b)
      (fun σ => R a b σ ∧ i.toNat < limit.toNat) (OptionRel R a b))
    (fuel : Nat) (a : α) (b : β) :
    ExactRealizes (repeatWhile fuel limit body a)
      (wordRepeatWhile fuel limit ram b) (R a b) R := by
  constructor
  · intro σ H
    simpa [repeatWhile, wordRepeatWhile, ChargedWord.val_literal _ (RamState.empty w), ChargedWord.cost_literal] using
      (exact_go body ram limit ((lit 1).val σ) R hbody fuel ((lit 0).val σ) a b).correct σ H
  · intro σ H
    have hc := (exact_go body ram limit ((lit 1).val σ) R hbody fuel ((lit 0).val σ) a b).cost_eq σ H
    simpa [repeatWhile, wordRepeatWhile, ChargedWord.val_literal _ (RamState.empty w), ChargedWord.cost_literal] using
      congrArg (fun c => CostVec.one Op.lit + (CostVec.one Op.lit + c)) hc


/-- A sharp bound depends on visited indices, not on a possibly huge structural
fuel allowance. Every continuing increment is nonwrapping under the guard. -/
theorem steps_go_le_visited (body : Word w → α → RAM w (Option α))
    (limit one : Word w) (hone : one.toNat=1) (bound : Nat)
    (hb : ∀ index acc σ, RAM.steps CostModel.unitCost (body index acc) σ≤bound)
    (fuel : Nat) (index : Word w) (acc : α) (σ : RamState w) :
    RAM.steps CostModel.unitCost (wordLoopGo body limit one fuel index acc) σ ≤
      1+min fuel (limit.toNat-index.toNat)*(bound+2) := by
  induction fuel generalizing index acc σ with
  | zero => simp [wordLoopGo]
  | succ fuel ih =>
    simp only [wordLoopGo, RAM.steps_bind, steps_lt, state_lt, val_lt, CostModel.unitCost_cost]
    by_cases hidx : index.toNat<limit.toNat
    · simp only [hidx, decide_true, if_true, RAM.steps_bind]
      have hbody := hb index acc σ
      have hmin : min (fuel+1) (limit.toNat-index.toNat) =
          min fuel (limit.toNat-(index.toNat+1))+1 := by omega
      cases hn : (body index acc).val σ with
      | none =>
        simp only [RAM.steps_pure]
        rw [hmin]
        have hm := Nat.le_mul_of_pos_left (bound+2) (Nat.succ_pos (min fuel (limit.toNat-(index.toNat+1))))
        simp only [Nat.succ_eq_add_one] at hm
        omega
      | some acc' =>
        simp only [RAM.steps_bind, steps_add, state_add, CostModel.unitCost_cost]
        have hfit : index.toNat+1<2^w := lt_of_le_of_lt (by omega) limit.toNat_lt
        have hnext : ((Arlib.Computation.add index one).val ((body index acc).state σ)).toNat = index.toNat+1 := by
          simp [toNat_add, hone, Nat.mod_eq_of_lt hfit]
        have hr := ih ((Arlib.Computation.add index one).val ((body index acc).state σ))
          acc' ((body index acc).state σ)
        rw [hnext] at hr
        rw [hmin]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
    · simp [hidx, show limit.toNat-index.toNat=0 from by omega]

theorem steps_repeatWhile_le_visited (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (acc : α) (σ : RamState w)
    (hw : 1<2^w) (bound : Nat)
    (hb : ∀ index acc σ, RAM.steps CostModel.unitCost (body index acc) σ≤bound) :
    RAM.steps CostModel.unitCost (wordRepeatWhile fuel limit body acc) σ ≤
      3+min fuel limit.toNat*(bound+2) := by
  simp only [wordRepeatWhile, RAM.steps_bind, steps_lit, state_lit, CostModel.unitCost_cost]
  have h := steps_go_le_visited body limit ((lit 1).val σ)
    (by simp [Nat.mod_eq_of_lt hw]) bound hb fuel ((lit 0).val σ) acc σ
  simp only [toNat_lit, Nat.zero_mod, Nat.sub_zero] at h
  omega

/-- Dynamic-length authoring without decoding the stored length into a natural.
The static word universe supplies structural fuel; the paid guard stops at the
actual length. This does not allocate or traverse a `List.range` of that universe. -/
def forWord (limit : Word w) (body : Word w → α → Charged Op κₛ (Option α))
    (acc : α) : Charged Op κₛ α := repeatWhile (2^w) limit body acc

def forWordRAM (limit : Word w) (body : Word w → β → RAM w (Option β))
    (acc : β) : RAM w β := wordRepeatWhile (2^w) limit body acc

theorem exact_forWord (body : Word w → α → Charged Op κₛ (Option α))
    (ram : Word w → β → RAM w (Option β)) (limit : Word w)
    (R : α → β → RamState w → Prop)
    (hbody : ∀ i a b, ExactRealizes (body i a) (ram i b)
      (fun σ => R a b σ ∧ i.toNat<limit.toNat) (OptionRel R a b))
    (a : α) (b : β) :
    ExactRealizes (forWord limit body a) (forWordRAM limit ram b) (R a b) R :=
  exact_repeatWhile body ram limit R hbody (2^w) a b

theorem steps_forWordRAM_le (limit : Word w) (body : Word w → α → RAM w (Option α))
    (acc : α) (σ : RamState w) (hw : 1<2^w) (bound : Nat)
    (hb : ∀ index acc σ, RAM.steps CostModel.unitCost (body index acc) σ≤bound) :
    RAM.steps CostModel.unitCost (forWordRAM limit body acc) σ ≤
      3+limit.toNat*(bound+2) := by
  have h := steps_repeatWhile_le_visited (2^w) limit body acc σ hw bound hb
  simpa [forWordRAM, Nat.min_eq_right (Nat.le_of_lt limit.toNat_lt)] using h
end ChargedLoop
end Arlib.Computation
