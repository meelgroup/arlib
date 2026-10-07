/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ChargedStorage
import Arlib.Computation.ChargedLoop

/-! # Shared indexed views and charged bulk filling

Views forward sealed metadata and share the backing storage. Each indexed read
pays for multiplication, offset addition, buffer-address addition and load.
These are read-only views; mutation needs a current backing representation.
-/
namespace Arlib.Computation

structure ChargedView (w : Nat) where
  storage : ChargedVector w
  offset : Word w
  stride : Word w
  length : Word w

structure RAMView (w : Nat) where
  storage : Buffer w
  offset : Word w
  stride : Word w
  length : Word w

namespace ChargedView
variable {w : Nat} {κₛ : Type}

def read (v : ChargedView w) (i : Word w) : Charged Op κₛ (Word w) := do
  let delta ← ChargedWord.mul i v.stride
  let index ← ChargedWord.add v.offset delta
  ChargedVector.read v.storage index

def readRAM (v : RAMView w) (i : Word w) : RAM w (Word w) := do
  let delta ← mul i v.stride
  let index ← add v.offset delta
  Buffer.read v.storage index

/-- Each selected physical index fits without wrapping either intermediate. -/
structure Represents (v : ChargedView w) (b : RAMView w) (σ : RamState w) : Prop where
  storage : ChargedVector.Represents v.storage b.storage σ
  offset_eq : v.offset = b.offset
  stride_eq : v.stride = b.stride
  length_eq : v.length = b.length
  bounds : ∀ i, i < v.length.toNat →
    v.offset.toNat+i*v.stride.toNat < v.storage.contents.length

theorem exact_read (v : ChargedView w) (b : RAMView w) (i : Word w)
    (hi : i.toNat < v.length.toNat) :
    ExactRealizes (read v i : Charged Op κₛ (Word w)) (readRAM b i)
      (Represents v b) (fun x y σ => x = y ∧ Represents v b σ) := by
  constructor
  · intro σ H
    have hbound := H.bounds i.toNat hi
    have hvlen : v.storage.contents.length < 2^w := by
      rw [←H.storage.length_eq]; exact Word.toNat_lt _
    have hsum : v.offset.toNat+i.toNat*v.stride.toNat < 2^w := lt_trans hbound hvlen
    have hprod : i.toNat*v.stride.toNat < 2^w := by omega
    let index := (add v.offset ((mul i v.stride).val σ)).val σ
    have hindex : index.toNat = v.offset.toNat+i.toNat*v.stride.toNat := by
      simp [index, toNat_add, toNat_mul, Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]
    have hc := (ChargedVector.exact_read (κₛ := κₛ) v.storage b.storage index
      (by omega)).correct σ H.storage
    refine ⟨?_, H⟩
    simpa only [read, readRAM, Charged.val_bind, RAM.val_bind, state_mul, state_add,
      ChargedWord.val_mul _ _ σ, ChargedWord.val_add _ _ σ, ←H.offset_eq,
      ←H.stride_eq] using hc.1
  · intro σ _; simp [read, readRAM, ChargedVector.cost_read]

@[simp] theorem steps_readRAM (v : RAMView w) (i : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (readRAM v i) σ = 4 := by simp [readRAM]

def write (v : ChargedView w) (i x : Word w) : Charged Op κₛ (ChargedView w) := do
  let delta ← ChargedWord.mul i v.stride
  let index ← ChargedWord.add v.offset delta
  let storage ← ChargedVector.write v.storage index x
  pure {v with storage := storage}

def writeRAM (v : RAMView w) (i x : Word w) : RAM w (RAMView w) := do
  let delta ← mul i v.stride
  let index ← add v.offset delta
  Buffer.write v.storage index x
  pure v

theorem exact_write (v : ChargedView w) (b : RAMView w) (i x : Word w)
    (hi : i.toNat<v.length.toNat) :
    ExactRealizes (write v i x : Charged Op κₛ (ChargedView w)) (writeRAM b i x)
      (Represents v b) Represents := by
  constructor
  · intro σ H
    have hbound := H.bounds i.toNat hi
    have hfit : v.storage.contents.length<2^w := by
      rw [←H.storage.length_eq]; exact Word.toNat_lt _
    have hsum : v.offset.toNat+i.toNat*v.stride.toNat < 2^w := lt_trans hbound hfit
    have hprod : i.toNat*v.stride.toNat<2^w := by omega
    let index := (add v.offset ((mul i v.stride).val σ)).val σ
    have hindex : index.toNat = v.offset.toNat+i.toNat*v.stride.toNat := by
      simp [index, toNat_add, toNat_mul, Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]
    have hw := (ChargedVector.exact_write (κₛ := κₛ) v.storage b.storage index x (by omega)).correct σ H.storage
    simp only [write, writeRAM, Charged.val_bind, Charged.val_pure, RAM.val_bind, RAM.state_bind,
      RAM.val_pure, RAM.state_pure, state_mul, state_add,
      ChargedWord.val_mul _ _ σ, ChargedWord.val_add _ _ σ, ←H.offset_eq, ←H.stride_eq]
    change Represents {v with storage :=
      (ChargedVector.write v.storage index x : Charged Op κₛ (ChargedVector w)).val}
      b ((Buffer.write b.storage index x).state σ)
    refine ⟨hw,H.offset_eq,H.stride_eq,H.length_eq,?_⟩
    intro j hj
    simpa using H.bounds j hj
  · intros; simp [write, writeRAM]

@[simp] theorem steps_writeRAM (v : RAMView w) (i x : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (writeRAM v i x) σ = 4 := by simp [writeRAM]
end ChargedView

namespace ChargedVector
variable {w : Nat} {κₛ : Type}

def fill (fuel : Nat) (limit : Word w) (v : ChargedVector w) (x : Word w) :
    Charged Op κₛ (ChargedVector w) :=
  ChargedLoop.repeatWhile fuel limit (fun i a => do
    let a' ← write a i x
    pure (some a')) v

def fillRAM (fuel : Nat) (limit : Word w) (b : Buffer w) (x : Word w) : RAM w (Buffer w) :=
  wordRepeatWhile fuel limit (fun i a => do
    Buffer.write a i x
    pure (some a)) b

/-- The relation carries the immutable length and the current memory version. -/
def FillRep (limit : Word w) (v : ChargedVector w) (b : Buffer w) (σ : RamState w) : Prop :=
  Represents v b σ ∧ v.length = limit

theorem exact_fill (fuel : Nat) (limit : Word w) (v : ChargedVector w)
    (b : Buffer w) (x : Word w) :
    ExactRealizes (fill fuel limit v x : Charged Op κₛ (ChargedVector w))
      (fillRAM fuel limit b x) (FillRep limit v b) (FillRep limit) := by
  apply ChargedLoop.exact_repeatWhile
  intro i a c
  constructor
  · intro σ H
    have hi : i.toNat < a.contents.length := by
      rw [←H.1.1.length_eq, H.1.2]; exact H.2
    have hw := (exact_write (κₛ := κₛ) a c i x hi).correct σ H.1.1
    simpa [ChargedLoop.OptionRel, Charged.val_bind, RAM.val_bind,
      RAM.state_bind, FillRep] using And.intro hw (by simpa using H.1.2)
  · intro σ _; simp

/-- A continuing fill body costs add+store; each iteration adds guard+increment.
An exhausted or completed traversal still pays the final guard. -/
theorem steps_fillRAM_le (fuel : Nat) (limit : Word w) (b : Buffer w)
    (x : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (fillRAM fuel limit b x) σ ≤ 3+4*fuel := by
  simpa [fillRAM, Nat.mul_comm, Nat.add_comm] using
    steps_wordRepeatWhile_le fuel limit
      (fun i a => do Buffer.write a i x; pure (some a)) b σ 2 (by intros; simp)


def fillForWord (limit : Word w) (v : ChargedVector w) (x : Word w) : Charged Op κₛ (ChargedVector w) :=
  fill (2^w) limit v x

def fillForWordRAM (limit : Word w) (b : Buffer w) (x : Word w) : RAM w (Buffer w) :=
  fillRAM (2^w) limit b x

theorem exact_fillForWord (limit : Word w) (v : ChargedVector w) (b : Buffer w) (x : Word w) :
    ExactRealizes (fillForWord limit v x : Charged Op κₛ (ChargedVector w))
      (fillForWordRAM limit b x) (FillRep limit v b) (FillRep limit) := exact_fill (2^w) limit v b x

theorem steps_fillForWordRAM_le (limit : Word w) (b : Buffer w) (x : Word w) (σ : RamState w)
    (hw : 1<2^w) : RAM.steps CostModel.unitCost (fillForWordRAM limit b x) σ ≤ 3+4*limit.toNat := by
  have h := ChargedLoop.steps_repeatWhile_le_visited (2^w) limit
    (fun i a => do Buffer.write a i x; pure (some a)) b σ hw 2 (by intros; simp)
  simpa [fillForWordRAM, fillRAM, Nat.min_eq_right (Nat.le_of_lt limit.toNat_lt), Nat.mul_comm] using h
end ChargedVector
end Arlib.Computation
