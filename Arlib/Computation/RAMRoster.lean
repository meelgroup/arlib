/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Buffer
import Arlib.Computation.StdRealization

/-!
# Bounded integer-key direct-address rosters

A flag buffer has one slot per admissible integer key, with a stored live-count
word. Storage is proportional to the key universe capacity, not live cardinality.
Every certified key access requires a capacity bound; the physical reserved region
is retained after erasure. This is not a balanced-tree implementation.
-/
namespace Arlib.Computation

private structure RAMRosterRep (w : ℕ) where
  flags : Buffer w
  count : Word w

/-- A sealed flag-buffer handle and register-held live count. -/
def RAMRoster (w : ℕ) := RAMRosterRep w

namespace RAMRoster
variable {w : ℕ}

/-- Forward previously represented storage and a count word into a handle. -/
def ofBuffer (flags : Buffer w) (count : Word w) : RAMRoster w := ⟨flags, count⟩
private def flags (r : RAMRoster w) := RAMRosterRep.flags r
/-- Forward the sealed flag-buffer handle for framing and composition. -/
def storage (r : RAMRoster w) : Buffer w := flags r
private def count (r : RAMRoster w) := RAMRosterRep.count r
noncomputable def countNat (r : RAMRoster w) : ℕ := (count r).toNat
noncomputable def capacityNat (r : RAMRoster w) : ℕ := (flags r).lengthNat

/-- Concrete capacity-wide flags represent exactly the abstract finite set. -/
structure Holds (σ : RamState w) (r : RAMRoster w) (d : Roster ℕ) (xs : List ℕ) : Prop where
  storage : Buffer.Holds σ (flags r) xs
  bits : ∀ k (hk : k < xs.length), xs[k] = if k ∈ d.toFinset then 1 else 0
  keys_bounded : ∀ k ∈ d.toFinset, k < xs.length
  count_eq : r.countNat = d.card

/-- A roster representation with an existential mathematical backing list. -/
def Rep (σ : RamState w) (r : RAMRoster w) (d : Roster ℕ) : Prop := ∃ xs, Holds σ r d xs

/-- Membership executes a charged indexed load and flag comparison. -/
def mem (r : RAMRoster w) (key : Word w) : RAM w Bool := do
  let flag ← Buffer.read (flags r) key
  let zero ← lit 0
  lt zero flag

@[simp] theorem state_mem (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    (mem r key).state σ = σ := by simp [mem]
@[simp] theorem steps_mem (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (mem r key) σ = 4 := by simp [mem]

theorem mem_spec {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) (key : Word w) (hk : key.toNat < xs.length) :
    (mem r key).val σ = decide (key.toNat ∈ d.toFinset) := by
  simp only [mem, RAM.val_bind, Buffer.state_read, state_lit, val_lt, toNat_lit, Nat.zero_mod]
  rw [Buffer.read_spec H.storage hk, H.bits key.toNat hk]
  by_cases hm : key.toNat ∈ d.toFinset <;> simp [hm]

/-- Insertion preserves duplicate entries and increments the count only for a
new key. Certified callers supply the key-capacity condition. -/
def insert (r : RAMRoster w) (key : Word w) : RAM w (RAMRoster w) := do
  let present ← mem r key
  if present then pure r else do
    let one ← lit 1
    let _ ← Buffer.write (flags r) key one
    let next ← add (count r) one
    pure (ofBuffer (flags r) next)

/-- Erasure clears the flag and decrements the count only for a present key. -/
def erase (r : RAMRoster w) (key : Word w) : RAM w (RAMRoster w) := do
  let present ← mem r key
  if present then do
    let zero ← lit 0
    let _ ← Buffer.write (flags r) key zero
    let one ← lit 1
    let next ← sub (count r) one
    pure (ofBuffer (flags r) next)
  else pure r

-- Erasure pays for separate zero and one literals.
theorem steps_insert_le (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (insert r key) σ ≤ 8 := by
  simp only [insert, RAM.steps_bind, steps_mem, state_mem]
  split <;> simp

theorem steps_erase_le (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (erase r key) σ ≤ 9 := by
  simp only [erase, RAM.steps_bind, steps_mem, state_mem]
  split <;> simp

/-- Forward the stored count; this does not scan the reserved flag capacity. -/
def size (r : RAMRoster w) : RAM w (Word w) := pure (count r)

def cardEq (r : RAMRoster w) (n : Word w) : RAM w Bool := eq (count r) n

@[simp] theorem state_size (r : RAMRoster w) (σ : RamState w) : (size r).state σ = σ := rfl
@[simp] theorem steps_size (r : RAMRoster w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (size r) σ = 0 := by simp [size]
@[simp] theorem steps_cardEq (r : RAMRoster w) (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (cardEq r n) σ = 1 := by simp [cardEq]

/-- Insertion implements the existing abstract roster operation, including
idempotent insertion and exact live-cardinality metadata. -/
theorem insert_spec {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) (key : Word w) (hk : key.toNat < xs.length) :
    ∃ ys, Holds ((insert r key).state σ) ((insert r key).val σ)
      ((Roster.insert key.toNat d : Charged StdOp Cell (Roster ℕ)).val) ys := by
  let d' := (Roster.insert key.toNat d : Charged StdOp Cell (Roster ℕ)).val
  have hset : d'.toFinset = Insert.insert key.toNat d.toFinset := Roster.toFinset_insert _ _
  by_cases hm : key.toNat ∈ d.toFinset
  · have hv : (insert r key).val σ = r := by simp [insert, mem_spec H key hk, hm]
    have hs : (insert r key).state σ = σ := by simp [insert, mem_spec H key hk, hm]
    rw [hv, hs]
    refine ⟨xs, H.storage, ?_, ?_, ?_⟩
    · intro i hi; rw [hset, Finset.insert_eq_of_mem hm]; exact H.bits i hi
    · rw [hset, Finset.insert_eq_of_mem hm]; exact H.keys_bounded
    · rw [← Roster.card_toFinset d', hset, Finset.insert_eq_of_mem hm,
        Roster.card_toFinset]; exact H.count_eq
  · have hbnd : ∀ i ∈ d'.toFinset, i < xs.length := by
      intro i hi
      rw [hset] at hi
      rcases Finset.mem_insert.mp hi with heq | hi
      · simpa only [heq] using hk
      · exact H.keys_bounded i hi
    have hcard : d'.card = d.card + 1 := by
      rw [← Roster.card_toFinset d', hset, Finset.card_insert_of_notMem hm,
        Roster.card_toFinset]
    have hcardbound : d'.card ≤ xs.length := by
      rw [← Roster.card_toFinset d']
      calc
        d'.toFinset.card ≤ (Finset.range xs.length).card :=
          Finset.card_le_card (by intro i hi; exact Finset.mem_range.mpr (hbnd i hi))
        _ = xs.length := Finset.card_range _
    have hcap : xs.length < 2 ^ w := by
      rw [← H.storage.length_eq]
      exact Word.toNat_lt (Buffer.length (flags r))
    have hfit : r.countNat + 1 < 2 ^ w := by rw [H.count_eq]; omega
    have hwidth : 1 < 2 ^ w := by omega
    let one := (lit 1 : RAM w (Word w)).val σ
    let next := ofBuffer (flags r) ((add (count r) one).val σ)
    have hone : one.toNat = 1 := by simp [one, Nat.mod_eq_of_lt hwidth]
    have hv : (insert r key).val σ = next := by
      simp only [insert, RAM.val_bind, mem_spec H key hk, hm, decide_false, state_mem]
      rfl
    have hs : (insert r key).state σ = (Buffer.write (flags r) key one).state σ := by
      simp [insert, mem_spec H key hk, hm]
      rfl
    have hcount : next.countNat = d'.card := by
      change ((add (count r) one).val σ).toNat = _
      rw [toNat_add, hone]
      change (r.countNat + 1) % 2 ^ w = _
      rw [Nat.mod_eq_of_lt hfit, H.count_eq, ← hcard]
    rw [hv, hs]
    refine ⟨xs.set key.toNat 1, ?_, ?_, ?_, hcount⟩
    · simpa only [hone, next, ofBuffer, flags] using Buffer.write_spec H.storage hk one
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      rw [hset]
      by_cases heq : i = key.toNat
      · subst i; simp
      · rw [List.getElem_set_ne (Ne.symm heq)]
        simpa [heq] using H.bits i hi'
    · simpa only [List.length_set] using hbnd

/-- Erasure implements logical deletion while retaining the reserved buffer. -/
theorem erase_spec {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) (key : Word w) (hk : key.toNat < xs.length) :
    ∃ ys, Holds ((erase r key).state σ) ((erase r key).val σ)
      ((Roster.erase key.toNat d : Charged StdOp Cell (Roster ℕ)).val) ys := by
  let d' := (Roster.erase key.toNat d : Charged StdOp Cell (Roster ℕ)).val
  have hset : d'.toFinset = d.toFinset.erase key.toNat := Roster.toFinset_erase _ _
  by_cases hm : key.toNat ∈ d.toFinset
  · have hcard : d'.card = d.card - 1 := by
      rw [← Roster.card_toFinset d', hset, Finset.card_erase_of_mem hm,
        Roster.card_toFinset]
    have hcap : xs.length < 2 ^ w := by
      rw [← H.storage.length_eq]
      exact Word.toNat_lt (Buffer.length (flags r))
    have hwidth : 1 < 2 ^ w := by omega
    have hpositive : 1 ≤ r.countNat := by
      rw [H.count_eq, ← Roster.card_toFinset]
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨key.toNat, hm⟩)
    let zero := (lit 0 : RAM w (Word w)).val σ
    let one := (lit 1 : RAM w (Word w)).val σ
    let next := ofBuffer (flags r) ((sub (count r) one).val σ)
    have hzero : zero.toNat = 0 := by simp [zero]
    have hone : one.toNat = 1 := by simp [one, Nat.mod_eq_of_lt hwidth]
    have hv : (erase r key).val σ = next := by
      simp only [erase, RAM.val_bind, mem_spec H key hk, hm, decide_true,
        if_true, state_mem, state_lit]
      rfl
    have hs : (erase r key).state σ = (Buffer.write (flags r) key zero).state σ := by
      simp [erase, mem_spec H key hk, hm]
      rfl
    have hcount : next.countNat = d'.card := by
      change ((sub (count r) one).val σ).toNat = _
      rw [toNat_sub_of_le σ (count r) one (by rw [hone]; exact hpositive), hone]
      change r.countNat - 1 = _
      rw [H.count_eq, ← hcard]
    rw [hv, hs]
    refine ⟨xs.set key.toNat 0, ?_, ?_, ?_, hcount⟩
    · simpa only [hzero, next, ofBuffer, flags] using Buffer.write_spec H.storage hk zero
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      rw [hset]
      by_cases heq : i = key.toNat
      · subst i; simp
      · rw [List.getElem_set_ne (Ne.symm heq)]
        simpa [heq] using H.bits i hi'
    · intro i hi
      rw [hset] at hi
      exact (by simpa only [List.length_set] using
        H.keys_bounded i (Finset.mem_erase.mp hi).2)
  · have hv : (erase r key).val σ = r := by simp [erase, mem_spec H key hk, hm]
    have hs : (erase r key).state σ = σ := by simp [erase, mem_spec H key hk, hm]
    rw [hv, hs]
    refine ⟨xs, H.storage, ?_, ?_, ?_⟩
    · intro i hi; rw [hset, Finset.erase_eq_of_notMem hm]; exact H.bits i hi
    · rw [hset, Finset.erase_eq_of_notMem hm]; exact H.keys_bounded
    · rw [← Roster.card_toFinset d', hset, Finset.erase_eq_of_notMem hm,
        Roster.card_toFinset]; exact H.count_eq

/-- The stored count represents the existing cardinality view. -/
theorem size_spec {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) : ((size r).val σ).toNat = d.card := H.count_eq

theorem cardEq_spec {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) (n : Word w) :
    (cardEq r n).val σ = decide (d.card = n.toNat) := by
  simp only [cardEq, val_eq]
  change decide (r.countNat = n.toNat) = _
  rw [H.count_eq]

/-- Certified membership for any admissible integer key. -/
theorem realizes_mem (d : Roster ℕ) (r : RAMRoster w) (key : Word w) :
    Realizes (Roster.mem key.toNat d : Charged StdOp Cell Bool) (mem r key)
      (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat) (fun a b _ => a = b) 4 where
  correct := by
    intro σ h
    rcases h.1 with ⟨xs, H⟩
    have hk : key.toNat < xs.length := by
      simpa only [capacityNat, H.storage.length_eq] using h.2
    rw [Roster.val_mem, mem_spec H key hk]
  steps_le := by intro σ _; simp

theorem realizes_insert (d : Roster ℕ) (r : RAMRoster w) (key : Word w) :
    Realizes (Roster.insert key.toNat d : Charged StdOp Cell (Roster ℕ)) (insert r key)
      (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat) (fun a b σ => Rep σ b a) 8 where
  correct := by
    intro σ h
    rcases h.1 with ⟨xs, H⟩
    apply insert_spec H key
    simpa only [capacityNat, H.storage.length_eq] using h.2
  steps_le := by intro σ _; exact steps_insert_le r key σ

theorem realizes_erase (d : Roster ℕ) (r : RAMRoster w) (key : Word w) :
    Realizes (Roster.erase key.toNat d : Charged StdOp Cell (Roster ℕ)) (erase r key)
      (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat) (fun a b σ => Rep σ b a) 9 where
  correct := by
    intro σ h
    rcases h.1 with ⟨xs, H⟩
    apply erase_spec H key
    simpa only [capacityNat, H.storage.length_eq] using h.2
  steps_le := by intro σ _; exact steps_erase_le r key σ

theorem realizes_size (d : Roster ℕ) (r : RAMRoster w) :
    Realizes (Roster.size d : Charged StdOp Cell ℕ) (size r)
      (fun σ => Rep σ r d) (fun a b _ => a = b.toNat) 0 where
  correct := by intro σ h; rcases h with ⟨xs, H⟩; rw [Roster.val_size, ← size_spec H]
  steps_le := by intro σ _; simp

theorem realizes_cardEq (d : Roster ℕ) (r : RAMRoster w) (n : Word w) :
    Realizes (Roster.cardEq n.toNat d : Charged StdOp Cell Bool) (cardEq r n)
      (fun σ => Rep σ r d) (fun a b _ => a = b) 1 where
  correct := by
    intro σ h
    rcases h with ⟨xs, H⟩
    rw [Roster.val_cardEq, cardEq_spec H n]
  steps_le := by intro σ _; simp

/-- Physical flags remain separate from another buffer's storage. -/
theorem frame_write {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs ys : List ℕ}
    (H : Holds σ r d xs) {b : Buffer w} (HB : Buffer.Holds σ b ys)
    (index value : Word w) (hi : index.toNat < ys.length)
    (hd : Disjoint (block (storage r).baseNat xs.length) (block b.baseNat ys.length)) :
    Holds ((Buffer.write b index value).state σ) r d xs := by
  refine ⟨?_, H.bits, H.keys_bounded, H.count_eq⟩
  exact Buffer.write_frame HB H.storage hi value hd

/-- Insertion writes only the flag slot and preserves a disjoint buffer. -/
theorem insert_frame {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs ys : List ℕ}
    (H : Holds σ r d xs) {b : Buffer w} (HB : Buffer.Holds σ b ys)
    (key : Word w) (hk : key.toNat < xs.length)
    (hd : Disjoint (block b.baseNat ys.length) (block (storage r).baseNat xs.length)) :
    Buffer.Holds ((insert r key).state σ) b ys := by
  by_cases hm : key.toNat ∈ d.toFinset
  · simpa [insert, mem_spec H key hk, hm] using HB
  · let one := (lit 1 : RAM w (Word w)).val σ
    have hs : (insert r key).state σ = (Buffer.write (storage r) key one).state σ := by
      simp [insert, mem_spec H key hk, hm]
      rfl
    rw [hs]
    exact Buffer.write_frame H.storage HB hk one hd

/-- Erasure preserves a disjoint buffer and does not reclaim reserved storage. -/
theorem erase_frame {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ} {xs ys : List ℕ}
    (H : Holds σ r d xs) {b : Buffer w} (HB : Buffer.Holds σ b ys)
    (key : Word w) (hk : key.toNat < xs.length)
    (hd : Disjoint (block b.baseNat ys.length) (block (storage r).baseNat xs.length)) :
    Buffer.Holds ((erase r key).state σ) b ys := by
  by_cases hm : key.toNat ∈ d.toFinset
  · let zero := (lit 0 : RAM w (Word w)).val σ
    have hs : (erase r key).state σ = (Buffer.write (storage r) key zero).state σ := by
      simp [erase, mem_spec H key hk, hm]
      rfl
    rw [hs]
    exact Buffer.write_frame H.storage HB hk zero hd
  · simpa [erase, mem_spec H key hk, hm] using HB

/-- Allocate and zero all flag slots, charging the key universe capacity. -/
def allocate (n : Word w) : RAM w (RAMRoster w) := do
  let b ← Buffer.allocate n
  let zero ← lit 0
  pure (ofBuffer b zero)

@[simp] theorem steps_allocate (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate n) σ = n.toNat + 1 := by
  simp [allocate, Buffer.allocate]

theorem allocate_spec (σ : RamState w) (n : Word w)
    (hfrontier : σ.size < 2 ^ w) (hspace : σ.size + n.toNat ≤ 2 ^ w) :
    Rep ((allocate n).state σ) ((allocate n).val σ) (Roster.empty : Roster ℕ) := by
  refine ⟨List.replicate n.toNat 0, ?_, ?_, ?_, ?_⟩
  · exact Buffer.allocate_spec σ n hfrontier hspace
  · intro i hi
    simp
  · intro i hi
    simp at hi
  · change ((lit 0 : RAM w (Word w)).val ((Buffer.allocate n).state σ)).toNat = 0
    simp

/-- Equal abstract finite sets have the same concrete representation. -/
theorem holds_congr {σ : RamState w} {r : RAMRoster w} {d e : Roster ℕ} {xs : List ℕ}
    (H : Holds σ r d xs) (heq : d.toFinset = e.toFinset) : Holds σ r e xs := by
  refine ⟨H.storage, ?_, ?_, ?_⟩
  · intro i hi; rw [← heq]; exact H.bits i hi
  · rw [← heq]; exact H.keys_bounded
  · rw [← Roster.card_toFinset e, ← heq, Roster.card_toFinset]; exact H.count_eq

@[simp] theorem storage_insert (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    storage ((insert r key).val σ) = storage r := by
  simp only [insert, RAM.val_bind]
  split <;> rfl

@[simp] theorem storage_erase (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    storage ((erase r key).val σ) = storage r := by
  simp only [erase, RAM.val_bind]
  split <;> rfl

/-- Allocating a new disjoint buffer preserves every existing roster. -/
theorem allocate_buffer_frame {σ : RamState w} {r : RAMRoster w} {d : Roster ℕ}
    {xs : List ℕ} (H : Holds σ r d xs) (n : Word w)
    (hspace : σ.size + n.toNat ≤ 2 ^ w) :
    Holds ((Buffer.allocate n).state σ) r d xs :=
  ⟨Buffer.allocate_frame H.storage n hspace, H.bits, H.keys_bounded, H.count_eq⟩

/-- Physical reserved capacity is unchanged by logical insertion. -/
@[simp] theorem size_state_insert (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    ((insert r key).state σ).size = σ.size := by
  simp only [insert, RAM.state_bind, state_mem]
  split <;> simp

/-- Logical deletion does not reclaim the reserved flag array. -/
@[simp] theorem size_state_erase (r : RAMRoster w) (key : Word w) (σ : RamState w) :
    ((erase r key).state σ).size = σ.size := by
  simp only [erase, RAM.state_bind, state_mem]
  split <;> simp

@[simp] theorem size_state_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).state σ).size = σ.size + n.toNat := by
  simp [allocate, Buffer.allocate]

end RAMRoster
end Arlib.Computation
