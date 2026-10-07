/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.CertifiedStd
import Arlib.Computation.RAMQueue
import Arlib.Computation.RAMDict

/-!
# Prices witnessed by concrete bounded integer-key implementations

Only the operations with certificates below establish an implementation. The
remaining table entries are uncertified prices for pricing algebra, without
an implementation-existence claim. Bounds describe unit RAM upper costs, not an
exact load trace. Dictionary/roster capacity initialization remains separate and
costs linear in the reserved key universe, independently of live cardinality.
-/
namespace Arlib.Computation.DirectAddressStd

private def operationBound : StdOp → ℕ
  | .roster .mem => 4
  | .roster .insert => 8
  | .roster .erase => 9
  | .dict .find => 6
  | .dict .insert => 10
  | .dict .erase => 9
  | .queue .enqueue => 5
  | .queue .dequeue => 7
  | .queue .isEmpty => 2
  | _ => 1

/-- Concrete-operation scalar ceilings. Unsupported operations acquire no code
or certificates merely from appearing in this table. -/
def pricing : StdImpl := StdImpl.ofBounds (fun o _ => operationBound o)
  (by intro o a b _; exact le_refl _)
  (by intro o n; cases o <;> rename_i op <;> cases op <;> decide)

theorem queue_isEmpty {w : ℕ} :
    CertifiedStdOperation pricing (.queue .isEmpty)
      (fun a : Queue ℕ => (Queue.isEmpty a : Charged StdOp Cell Bool))
      (fun c : RAMQueue w => RAMQueue.isEmpty c)
      (fun a c σ => RAMQueue.Rep σ c a) (fun a b _ => a = b) Queue.length where
  charge := by intro a; simp; rfl
  realization := by intro a c; exact RAMQueue.realizes_isEmpty a c

theorem queue_dequeue {w : ℕ} :
    CertifiedStdOperation pricing (.queue .dequeue)
      (fun a : Queue ℕ => (Queue.dequeue a : Charged StdOp Cell (Option ℕ × Queue ℕ)))
      (fun c : RAMQueue w => RAMQueue.dequeue c)
      (fun a c σ => RAMQueue.Rep σ c a)
      (fun a b σ => a.1 = b.1.map Word.toNat ∧ RAMQueue.Rep σ b.2 a.2) Queue.length where
  charge := by intro a; simp; rfl
  realization := by intro a c; exact RAMQueue.realizes_dequeue a c

theorem queue_enqueue {w : ℕ} :
    CertifiedStdOperation pricing (.queue .enqueue)
      (fun a : Queue ℕ × ℕ => (Queue.enqueue a.2 a.1 : Charged StdOp Cell (Queue ℕ)))
      (fun c : RAMQueue w × Word w => RAMQueue.enqueue c.1 c.2)
      (fun a c σ => RAMQueue.Rep σ c.1 a.1 ∧
        c.1.headNat + a.1.toList.length < c.1.capacityNat ∧ c.2.toNat = a.2)
      (fun a b σ => RAMQueue.Rep σ b a) (fun a => a.1.length) where
  charge := by intro a; simp; rfl
  realization := by intro a c; exact RAMQueue.realizes_enqueue a.1 c.1 a.2 c.2

theorem roster_mem {w : ℕ} :
    CertifiedStdOperation pricing (.roster .mem)
      (fun a : Roster ℕ × ℕ => (Roster.mem a.2 a.1 : Charged StdOp Cell Bool))
      (fun c : RAMRoster w × Word w => RAMRoster.mem c.1 c.2)
      (fun a c σ => RAMRoster.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat ∧
        c.2.toNat < c.1.capacityNat)
      (fun a b _ => a = b) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      rcases h.1 with ⟨xs, H⟩
      have hk : c.2.toNat < xs.length := by
        simpa only [RAMRoster.capacityNat, H.storage.length_eq] using h.2.2
      rw [Roster.val_mem, h.2.1, RAMRoster.mem_spec H c.2 hk]
    · intro σ _
      exact le_of_eq (RAMRoster.steps_mem c.1 c.2 σ)

theorem roster_size {w : ℕ} :
    CertifiedStdOperation pricing (.roster .size)
      (fun a : Roster ℕ => (Roster.size a : Charged StdOp Cell ℕ))
      (fun c : RAMRoster w => RAMRoster.size c)
      (fun a c σ => RAMRoster.Rep σ c a) (fun a b _ => a = b.toNat) Roster.card where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    exact (RAMRoster.realizes_size a c).consequence
      (fun _ h => h) (fun _ _ _ h => h) (Nat.zero_le _)

theorem dict_find {w : ℕ} :
    CertifiedStdOperation pricing (.dict .find)
      (fun a : Dict ℕ ℕ × ℕ => (Dict.find a.2 a.1 : Charged StdOp Cell (Option ℕ)))
      (fun c : RAMDict w × Word w => RAMDict.find c.1 c.2)
      (fun a c σ => RAMDict.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat ∧
        c.2.toNat < c.1.capacityNat)
      (fun a b _ => a = b.map Word.toNat) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      rcases h.1 with ⟨fs, vs, H⟩
      have hk : c.2.toNat < fs.length := by
        simpa only [RAMDict.capacityNat, RAMRoster.capacityNat, H.key_rep.storage.length_eq] using h.2.2
      rw [Dict.val_find, h.2.1, ← RAMDict.find_spec H c.2 hk]
    · intro σ _
      exact RAMDict.steps_find_le c.1 c.2 σ

theorem roster_insert {w : ℕ} :
    CertifiedStdOperation pricing (.roster .insert)
      (fun a : Roster ℕ × ℕ => (Roster.insert a.2 a.1 : Charged StdOp Cell (Roster ℕ)))
      (fun c : RAMRoster w × Word w => RAMRoster.insert c.1 c.2)
      (fun a c σ => RAMRoster.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat ∧
        c.2.toNat < c.1.capacityNat)
      (fun a b σ => RAMRoster.Rep σ b a) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      have hr := (RAMRoster.realizes_insert a.1 c.1 c.2).correct σ ⟨h.1, h.2.2⟩
      simpa only [h.2.1] using hr
    · intro σ _; exact RAMRoster.steps_insert_le c.1 c.2 σ

theorem roster_erase {w : ℕ} :
    CertifiedStdOperation pricing (.roster .erase)
      (fun a : Roster ℕ × ℕ => (Roster.erase a.2 a.1 : Charged StdOp Cell (Roster ℕ)))
      (fun c : RAMRoster w × Word w => RAMRoster.erase c.1 c.2)
      (fun a c σ => RAMRoster.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat ∧
        c.2.toNat < c.1.capacityNat)
      (fun a b σ => RAMRoster.Rep σ b a) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      have hr := (RAMRoster.realizes_erase a.1 c.1 c.2).correct σ ⟨h.1, h.2.2⟩
      simpa only [h.2.1] using hr
    · intro σ _; exact RAMRoster.steps_erase_le c.1 c.2 σ

theorem roster_cardEq {w : ℕ} :
    CertifiedStdOperation pricing (.roster .cardEq)
      (fun a : Roster ℕ × ℕ => (Roster.cardEq a.2 a.1 : Charged StdOp Cell Bool))
      (fun c : RAMRoster w × Word w => RAMRoster.cardEq c.1 c.2)
      (fun a c σ => RAMRoster.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat)
      (fun a b _ => a = b) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      rcases h.1 with ⟨xs, H⟩
      rw [Roster.val_cardEq, h.2, RAMRoster.cardEq_spec H c.2]
    · intro σ _; exact le_of_eq (RAMRoster.steps_cardEq c.1 c.2 σ)

theorem dict_insert {w : ℕ} :
    CertifiedStdOperation pricing (.dict .insert)
      (fun a : Dict ℕ ℕ × (ℕ × ℕ) =>
        (Dict.insert a.2.1 a.2.2 a.1 : Charged StdOp Cell (Dict ℕ ℕ)))
      (fun c : RAMDict w × (Word w × Word w) => RAMDict.insert c.1 c.2.1 c.2.2)
      (fun a c σ => RAMDict.Rep σ c.1 a.1 ∧ a.2.1 = c.2.1.toNat ∧
        a.2.2 = c.2.2.toNat ∧ c.2.1.toNat < c.1.capacityNat)
      (fun a b σ => RAMDict.Rep σ b a) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      have hr := (RAMDict.realizes_insert a.1 c.1 c.2.1 c.2.2).correct σ ⟨h.1, h.2.2.2⟩
      simpa only [h.2.1, h.2.2.1] using hr
    · intro σ _; exact RAMDict.steps_insert_le c.1 c.2.1 c.2.2 σ

theorem dict_erase {w : ℕ} :
    CertifiedStdOperation pricing (.dict .erase)
      (fun a : Dict ℕ ℕ × ℕ => (Dict.erase a.2 a.1 : Charged StdOp Cell (Dict ℕ ℕ)))
      (fun c : RAMDict w × Word w => RAMDict.erase c.1 c.2)
      (fun a c σ => RAMDict.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat ∧
        c.2.toNat < c.1.capacityNat)
      (fun a b σ => RAMDict.Rep σ b a) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      have hr := (RAMDict.realizes_erase a.1 c.1 c.2).correct σ ⟨h.1, h.2.2⟩
      simpa only [h.2.1] using hr
    · intro σ _; exact RAMDict.steps_erase_le c.1 c.2 σ

theorem dict_size {w : ℕ} :
    CertifiedStdOperation pricing (.dict .size)
      (fun a : Dict ℕ ℕ => (Dict.size a : Charged StdOp Cell ℕ))
      (fun c : RAMDict w => RAMDict.size c)
      (fun a c σ => RAMDict.Rep σ c a) (fun a b _ => a = b.toNat) Dict.card where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    exact (RAMDict.realizes_size a c).consequence
      (fun _ h => h) (fun _ _ _ h => h) (Nat.zero_le _)

theorem dict_cardEq {w : ℕ} :
    CertifiedStdOperation pricing (.dict .cardEq)
      (fun a : Dict ℕ ℕ × ℕ => (Dict.cardEq a.2 a.1 : Charged StdOp Cell Bool))
      (fun c : RAMDict w × Word w => RAMDict.cardEq c.1 c.2)
      (fun a c σ => RAMDict.Rep σ c.1 a.1 ∧ a.2 = c.2.toNat)
      (fun a b _ => a = b) (fun a => a.1.card) where
  charge := by intro a; simp; rfl
  realization := by
    intro a c
    constructor
    · intro σ h
      rcases h.1 with ⟨fs, vs, H⟩
      rw [Dict.val_cardEq, h.2, RAMDict.cardEq_spec H c.2]
    · intro σ _; exact le_of_eq (RAMDict.steps_cardEq c.1 c.2 σ)

end Arlib.Computation.DirectAddressStd
