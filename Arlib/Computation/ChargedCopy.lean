/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ChargedView

/-! # Charged copying between disjoint represented blocks

The read-only source stays represented while the destination changes. Overlap
is excluded explicitly; these certificates do not promise `memmove` semantics.
-/
namespace Arlib.Computation.ChargedVector
variable {w : Nat} {κₛ : Type}

def copy (fuel : Nat) (limit : Word w) (src dst : ChargedVector w) : Charged Op κₛ (ChargedVector w) :=
  ChargedLoop.repeatWhile fuel limit (fun i a => do
    let x ← read src i
    let a' ← write a i x
    pure (some a')) dst

def copyRAM (fuel : Nat) (limit : Word w) (src dst : Buffer w) : RAM w (Buffer w) :=
  wordRepeatWhile fuel limit (fun i a => do
    let x ← Buffer.read src i
    Buffer.write a i x
    pure (some a)) dst

structure CopyRep (limit : Word w) (src : ChargedVector w) (srcRAM : Buffer w)
    (dst : ChargedVector w) (dstRAM : Buffer w) (σ : RamState w) : Prop where
  source : Represents src srcRAM σ
  destination : Represents dst dstRAM σ
  length_eq : dst.length = limit
  disjoint : Disjoint (block srcRAM.baseNat src.contents.length)
    (block dstRAM.baseNat dst.contents.length)

theorem exact_copy (fuel : Nat) (limit : Word w) (src dst : ChargedVector w)
    (srcRAM dstRAM : Buffer w) (hlen : limit.toNat≤src.contents.length) :
    ExactRealizes (copy fuel limit src dst : Charged Op κₛ (ChargedVector w))
      (copyRAM fuel limit srcRAM dstRAM) (CopyRep limit src srcRAM dst dstRAM)
      (CopyRep limit src srcRAM) := by
  apply ChargedLoop.exact_repeatWhile
  intro i a b
  constructor
  · intro σ H
    have hi : i.toNat<a.contents.length := by
      rw [←H.1.destination.length_eq,H.1.length_eq]; exact H.2
    have hisrc : i.toNat<src.contents.length := by omega
    have hr := (exact_read (κₛ := κₛ) src srcRAM i hisrc).correct σ H.1.source
    have hw := (exact_write (κₛ := κₛ) a b i ((Buffer.read srcRAM i).val σ) hi).correct σ H.1.destination
    have hs := Buffer.write_frame H.1.destination.storage H.1.source.storage hi
      ((Buffer.read srcRAM i).val σ) H.1.disjoint
    change CopyRep limit src srcRAM
      (write a i (read src i : Charged Op κₛ (Word w)).val : Charged Op κₛ (ChargedVector w)).val
      b ((Buffer.write b i ((Buffer.read srcRAM i).val σ)).state σ)
    rw [hr.1]
    refine ⟨⟨hs,H.1.source.length_eq⟩,hw,?_,?_⟩
    · simpa using H.1.length_eq
    · simpa using H.1.disjoint
  · intro σ _; simp [add_assoc]

theorem steps_copyRAM_le (fuel : Nat) (limit : Word w) (src dst : Buffer w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (copyRAM fuel limit src dst) σ ≤ 3+6*fuel := by
  simpa [copyRAM, Nat.mul_comm, Nat.add_comm] using
    steps_wordRepeatWhile_le fuel limit
      (fun i a => do
        let x ← Buffer.read src i
        Buffer.write a i x
        pure (some a)) dst σ 4 (by intros; simp)

def copyForWord (limit : Word w) (src dst : ChargedVector w) : Charged Op κₛ (ChargedVector w) :=
  copy (2^w) limit src dst

def copyForWordRAM (limit : Word w) (src dst : Buffer w) : RAM w (Buffer w) :=
  copyRAM (2^w) limit src dst

theorem exact_copyForWord (limit : Word w) (src dst : ChargedVector w) (a b : Buffer w)
    (hlen : limit.toNat≤src.contents.length) :
    ExactRealizes (copyForWord limit src dst : Charged Op κₛ (ChargedVector w))
      (copyForWordRAM limit a b) (CopyRep limit src a dst b) (CopyRep limit src a) :=
  exact_copy (2^w) limit src dst a b hlen

theorem steps_copyForWordRAM_le (limit : Word w) (src dst : Buffer w) (σ : RamState w)
    (hw : 1<2^w) : RAM.steps CostModel.unitCost (copyForWordRAM limit src dst) σ ≤ 3+6*limit.toNat := by
  have h := ChargedLoop.steps_repeatWhile_le_visited (2^w) limit
    (fun i a => do
      let x ← Buffer.read src i
      Buffer.write a i x
      pure (some a)) dst σ hw 4 (by intros; simp)
  simpa [copyForWordRAM, copyRAM, Nat.min_eq_right (Nat.le_of_lt limit.toNat_lt), Nat.mul_comm] using h
end Arlib.Computation.ChargedVector
