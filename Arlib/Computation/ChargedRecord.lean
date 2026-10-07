/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ChargedStorage
import Arlib.Computation.RecordBuffer
import Arlib.Computation.SignedBuffer

/-! # Charged record and signed storage

Records use two disjoint fields. Source writes return the new contents; physical
writes retain the handle. The representation relation checks both fields in the
updated memory and is suitable for the mutable loop rule.
-/
namespace Arlib.Computation
structure ChargedRecord (w : Nat) where
  first : ChargedVector w
  second : ChargedVector w
namespace ChargedRecord
variable {w : Nat} {κₛ : Type}
def length (v : ChargedRecord w) : Word w := v.first.length

def read (v : ChargedRecord w) (i : Word w) : Charged Op κₛ (Word w × Word w) := do
  let a ← ChargedVector.read v.first i
  let b ← ChargedVector.read v.second i
  pure (a,b)

def write (v : ChargedRecord w) (i : Word w) (x : Word w × Word w) : Charged Op κₛ (ChargedRecord w) := do
  let a ← ChargedVector.write v.first i x.1
  let b ← ChargedVector.write v.second i x.2
  pure ⟨a,b⟩

def allocate (n : Word w) : Charged Op κₛ (ChargedRecord w) := do
  let a ← ChargedVector.allocate n
  let b ← ChargedVector.allocate n
  pure ⟨a,b⟩

structure Represents (v : ChargedRecord w) (b : RecordBuffer w) (σ : RamState w) : Prop where
  first : ChargedVector.Represents v.first b.first σ
  second : ChargedVector.Represents v.second b.second σ
  disjoint : Disjoint (block b.first.baseNat v.first.contents.length)
    (block b.second.baseNat v.second.contents.length)

theorem exact_read (v : ChargedRecord w) (b : RecordBuffer w) (i : Word w)
    (h1 : i.toNat<v.first.contents.length) (h2 : i.toNat<v.second.contents.length) :
    ExactRealizes (read v i : Charged Op κₛ (Word w × Word w)) (RecordBuffer.read b i)
      (Represents v b) (fun x y σ => x=y ∧ Represents v b σ) := by
  constructor
  · intro σ H
    have ha := (ChargedVector.exact_read (κₛ := κₛ) v.first b.first i h1).correct σ H.first
    have hb := (ChargedVector.exact_read (κₛ := κₛ) v.second b.second i h2).correct σ H.second
    refine ⟨?_,H⟩
    change ((ChargedVector.read v.first i : Charged Op κₛ (Word w)).val,
      (ChargedVector.read v.second i : Charged Op κₛ (Word w)).val) =
      ((Buffer.read b.first i).val σ, (Buffer.read b.second i).val σ)
    rw [ha.1,hb.1]
  · intros; simp [read, RecordBuffer.read]

theorem exact_write (v : ChargedRecord w) (b : RecordBuffer w) (i : Word w) (x : Word w × Word w)
    (h1 : i.toNat<v.first.contents.length) (h2 : i.toNat<v.second.contents.length) :
    ExactRealizes (write v i x : Charged Op κₛ (ChargedRecord w)) (RecordBuffer.write b i x)
      (Represents v b) (fun v' _ σ => Represents v' b σ) := by
  constructor
  · intro σ H
    have ha := Buffer.write_spec H.first.storage h1 x.1
    have hb := Buffer.write_frame H.first.storage H.second.storage h1 x.1 H.disjoint.symm
    have ha' := Buffer.write_frame hb ha h2 x.2 (by simpa using H.disjoint)
    have hb' := Buffer.write_spec hb h2 x.2
    change Represents
      ⟨(ChargedVector.write v.first i x.1 : Charged Op κₛ (ChargedVector w)).val,
       (ChargedVector.write v.second i x.2 : Charged Op κₛ (ChargedVector w)).val⟩ b _
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [RecordBuffer.write] using ha'
    · simpa using H.first.length_eq
    · simpa [RecordBuffer.write] using hb'
    · simpa using H.second.length_eq
    · simpa using H.disjoint
  · intros; simp [write, RecordBuffer.write]

theorem exact_allocate (n : Word w) :
    ExactRealizes (allocate n : Charged Op κₛ (ChargedRecord w)) (RecordBuffer.allocate n)
      (fun σ => σ.size+n.toNat < 2^w ∧ σ.size+2*n.toNat ≤ 2^w) Represents := by
  constructor
  · intro σ H
    have hfront : σ.size<2^w := by omega
    have hspace : σ.size+n.toNat≤2^w := by omega
    have ha := Buffer.allocate_spec σ n hfront hspace
    have hb := Buffer.allocate_spec ((Buffer.allocate n).state σ) n
      (by simpa using H.1) (by simp only [Buffer.state_allocate, size_state_alloc]; omega)
    have ha' := Buffer.allocate_frame ha n (by simp only [Buffer.state_allocate, size_state_alloc]; omega)
    change Represents
      ⟨(ChargedVector.allocate n : Charged Op κₛ (ChargedVector w)).val,
       (ChargedVector.allocate n : Charged Op κₛ (ChargedVector w)).val⟩
      (RecordBuffer.ofBuffers ((Buffer.allocate n).val σ)
        ((Buffer.allocate n).val ((Buffer.allocate n).state σ)))
      ((Buffer.allocate n).state ((Buffer.allocate n).state σ))
    refine ⟨⟨?_, by simp⟩, ⟨?_, by simp⟩, ?_⟩
    · simpa [RecordBuffer.allocate, RecordBuffer.first, RecordBuffer.ofBuffers] using ha'
    · simpa [RecordBuffer.allocate, RecordBuffer.second, RecordBuffer.ofBuffers] using hb
    · simp only [ChargedVector.contents_allocate, List.length_replicate]
      apply Set.disjoint_left.mpr
      intro j hj hk
      have hbase1 : ((Buffer.allocate n).val σ).baseNat = σ.size := toNat_val_alloc σ n hfront
      have hbase2 : ((Buffer.allocate n).val ((Buffer.allocate n).state σ)).baseNat = σ.size+n.toNat := by
        change ((alloc n).val ((alloc n).state σ)).toNat = _
        simpa using toNat_val_alloc ((Buffer.allocate n).state σ) n (by simpa using H.1)
      simpa only [RecordBuffer.first, RecordBuffer.second, RecordBuffer.ofBuffers, hbase1, hbase2, block,
        Set.mem_ofPred_eq] using (show False from by
          simp only [RecordBuffer.first, RecordBuffer.second, RecordBuffer.ofBuffers, hbase1, hbase2, block,
            Set.mem_ofPred_eq] at hj hk
          omega)
  · intros; simp [allocate, RecordBuffer.allocate]

end ChargedRecord

namespace ChargedSignedStorage
variable {w : Nat} {κₛ : Type}
def read (v : ChargedRecord w) (i : Word w) : Charged Op κₛ (SignedWord w) := do
  let x ← ChargedRecord.read v i
  let one ← ChargedWord.literal 1
  let negative ← ChargedWord.eq x.1 one
  pure (SignedWord.ofParts negative x.2)
def write (v : ChargedRecord w) (i : Word w) (x : SignedWord w) : Charged Op κₛ (ChargedRecord w) := do
  let flag ← ChargedWord.literal (if x.sign then 1 else 0)
  ChargedRecord.write v i (flag,x.magnitudeWord)

theorem exact_read (v : ChargedRecord w) (b : SignedBuffer w) (i : Word w)
    (h1 : i.toNat<v.first.contents.length) (h2 : i.toNat<v.second.contents.length) :
    ExactRealizes (read v i : Charged Op κₛ (SignedWord w)) (SignedBuffer.read b i)
      (ChargedRecord.Represents v b.records)
      (fun x y σ => x=y ∧ ChargedRecord.Represents v b.records σ) := by
  constructor
  · intro σ H
    have hr := (ChargedRecord.exact_read (κₛ := κₛ) v b.records i h1 h2).correct σ H
    change SignedWord.ofParts
      (ChargedWord.eq (ChargedRecord.read v i : Charged Op κₛ (Word w × Word w)).val.1
        (ChargedWord.literal 1 : Charged Op κₛ (Word w)).val : Charged Op κₛ Bool).val
      (ChargedRecord.read v i : Charged Op κₛ (Word w × Word w)).val.2 = _ ∧ _
    refine ⟨?_, H⟩
    rw [hr.1, ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ]
    simp [SignedBuffer.read]
  · intros; simp [read, SignedBuffer.read, ChargedRecord.read, RecordBuffer.read, add_assoc]
theorem exact_write (v : ChargedRecord w) (b : SignedBuffer w) (i : Word w) (x : SignedWord w)
    (h1 : i.toNat<v.first.contents.length) (h2 : i.toNat<v.second.contents.length) :
    ExactRealizes (write v i x : Charged Op κₛ (ChargedRecord w)) (SignedBuffer.write b i x)
      (ChargedRecord.Represents v b.records)
      (fun v' _ σ => ChargedRecord.Represents v' b.records σ) := by
  constructor
  · intro σ H
    have hw := (ChargedRecord.exact_write (κₛ := κₛ) v b.records i
      ((lit (if x.sign then 1 else 0)).val σ, x.magnitudeWord) h1 h2).correct σ H
    simpa only [write, SignedBuffer.write, Charged.val_bind, RAM.state_bind,
      state_lit, ChargedWord.val_literal _ σ] using hw
  · intros; simp [write, SignedBuffer.write, ChargedRecord.write, RecordBuffer.write, add_assoc]

end ChargedSignedStorage
end Arlib.Computation
