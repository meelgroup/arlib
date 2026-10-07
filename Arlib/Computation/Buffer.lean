/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Footprint

/-!
# Sealed indexed RAM buffers

A buffer handle consists of a base address and a stored length in registers.
Forwarding these words is free; it does not claim a memory read occurred.
Indexed accesses execute an address addition and a memory operation. Mathematical
observations are specification-only. `Holds` supplies the allocation and width
conditions that exclude wrapped addresses and discarded stores.
-/

namespace Arlib.Computation

private structure BufferRep (w : ℕ) where
  base : Word w
  length : Word w

/-- An opaque pair of register-held words describing an indexed memory block. -/
def Buffer (w : ℕ) := BufferRep w

namespace Buffer

variable {w : ℕ}

/-- Forward existing machine words into a handle. Validity is expressed by `Holds`;
this constructor neither allocates nor certifies a block. -/
def ofWords (base length : Word w) : Buffer w := ⟨base, length⟩

/-- Forward the stored length register, without traversing the buffer. -/
def length (b : Buffer w) : Word w := BufferRep.length b

private def base (b : Buffer w) : Word w := BufferRep.base b

/-- Specification-only observation of the base address. -/
noncomputable def baseNat (b : Buffer w) : ℕ := (base b).toNat

/-- Specification-only observation of the stored length. -/
noncomputable def lengthNat (b : Buffer w) : ℕ := (length b).toNat

@[simp] theorem baseNat_ofWords (a n : Word w) :
    (ofWords a n).baseNat = a.toNat := rfl
@[simp] theorem length_ofWords (a n : Word w) : (ofWords a n).length = n := rfl
@[simp] theorem lengthNat_ofWords (a n : Word w) :
    (ofWords a n).lengthNat = n.toNat := rfl

/-- The stored length is exact and the block contains the specified list. -/
structure Holds (σ : RamState w) (b : Buffer w) (xs : List ℕ) : Prop where
  length_eq : b.lengthNat = xs.length
  contents : HoldsList σ b.baseNat xs

/-- Read using a machine index. Out-of-range accesses have the underlying RAM
semantics; `read_spec` requires an in-range index. -/
def read (b : Buffer w) (index : Word w) : RAM w (Word w) := do
  let address ← add (base b) index
  load address

/-- Write using a machine index. Bounds are proved at each certified call. -/
def write (b : Buffer w) (index value : Word w) : RAM w Unit := do
  let address ← add (base b) index
  store address value

@[simp] theorem state_read (b : Buffer w) (index : Word w) (σ : RamState w) :
    (read b index).state σ = σ := rfl

@[simp] theorem cost_read (b : Buffer w) (index : Word w) (σ : RamState w) :
    (read b index).cost σ = CostVec.one .add + CostVec.one .load := rfl

@[simp] theorem steps_read (C : CostModel) (b : Buffer w) (index : Word w)
    (σ : RamState w) : RAM.steps C (read b index) σ = C.cost .add + C.cost .load := by
  simp [read, RAM.steps]

/-- An in-bounds read returns the represented element, without address overflow. -/
theorem read_spec {σ : RamState w} {b : Buffer w} {xs : List ℕ}
    (H : Holds σ b xs) {index : Word w} (hi : index.toNat < xs.length) :
    ((read b index).val σ).toNat = xs[index.toNat] := by
  have haddr := H.contents.index_lt hi
  simp only [read, RAM.val_bind, state_add, toNat_load, toNat_add]
  change (σ.get ((b.baseNat + index.toNat) % 2 ^ w)).toNat = _
  rw [Nat.mod_eq_of_lt haddr]
  exact H.contents.get index.toNat hi

@[simp] theorem cost_write (b : Buffer w) (index value : Word w) (σ : RamState w) :
    (write b index value).cost σ = CostVec.one .add + CostVec.one .store := rfl

@[simp] theorem steps_write (C : CostModel) (b : Buffer w) (index value : Word w)
    (σ : RamState w) : RAM.steps C (write b index value) σ =
      C.cost .add + C.cost .store := by
  simp [write, RAM.steps]

@[simp] theorem size_state_write (b : Buffer w) (index value : Word w)
    (σ : RamState w) : ((write b index value).state σ).size = σ.size := by
  simp [write, RamState.size]

/-- The indexed store's exact footprint, including the machine's wrap convention. -/
theorem footprint_write (b : Buffer w) (index value : Word w) :
    Footprint {(b.baseNat + index.toNat) % 2 ^ w} (write b index value) := by
  intro σ j hj
  simp only [write, RAM.state_bind, state_add]
  exact get_state_store_of_ne _ _ σ (by simpa [baseNat] using hj)

/-- Indexed stores never allocate. -/
theorem noAlloc_write (b : Buffer w) (index value : Word w) :
    NoAlloc (write b index value) := size_state_write b index value

private theorem state_write_eq_storeAt (b : Buffer w) (index value : Word w)
    (σ : RamState w) : (write b index value).state σ =
      (storeAt (base b) index.toNat value).state σ := by
  have hindex : (lit index.toNat : RAM w (Word w)).val σ = index := by
    apply Word.toNat_injective
    simp [Nat.mod_eq_of_lt (Word.toNat_lt index)]
  simp only [write, storeAt, RAM.state_bind, state_add, state_lit]
  rw [hindex]

/-- An in-bounds update changes exactly one represented element and preserves
both the stored length and the allocated size. -/
theorem write_spec {σ : RamState w} {b : Buffer w} {xs : List ℕ}
    (H : Holds σ b xs) {index : Word w} (hi : index.toNat < xs.length)
    (value : Word w) : Holds ((write b index value).state σ) b
      (xs.set index.toNat value.toNat) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.length_set] using H.length_eq
  · rw [state_write_eq_storeAt]
    exact H.contents.state_storeAt rfl hi value

/-- A write into one block preserves the representation of a disjoint block. -/
theorem write_frame {σ : RamState w} {b other : Buffer w} {xs ys : List ℕ}
    (H : Holds σ b xs) (Hother : Holds σ other ys) {index : Word w}
    (hi : index.toNat < xs.length) (value : Word w)
    (hd : Disjoint (block other.baseNat ys.length) (block b.baseNat xs.length)) :
    Holds ((write b index value).state σ) other ys := by
  refine ⟨Hother.length_eq, Hother.contents.of_footprint
    (footprint_write b index value) (noAlloc_write b index value) ?_⟩
  have haddr := H.contents.index_lt hi
  rw [Nat.mod_eq_of_lt haddr]
  apply Set.disjoint_left.mpr
  intro j hj hj'
  have heq : j = b.baseNat + index.toNat := by simpa using hj'
  subst j
  exact Set.disjoint_left.mp hd hj ⟨Nat.le_add_right _ _, by omega⟩

/-- Allocate zeroed storage, charged once per cell by the RAM allocator. -/
def allocate (n : Word w) : RAM w (Buffer w) := do
  let a ← alloc n
  pure (ofWords a n)

@[simp] theorem state_allocate (n : Word w) (σ : RamState w) :
    (allocate n).state σ = (alloc n).state σ := rfl

@[simp] theorem cost_allocate (n : Word w) (σ : RamState w) :
    (allocate n).cost σ = CostVec.many .alloc n.toNat := by
  simp [allocate]

@[simp] theorem length_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).val σ).length = n := rfl

/-- The allocation frontier must itself fit in a word, including for an empty
allocation. The full newly allocated region must fit too. -/
theorem allocate_spec (σ : RamState w) (n : Word w)
    (hfrontier : σ.size < 2 ^ w) (hspace : σ.size + n.toNat ≤ 2 ^ w) :
    Holds ((allocate n).state σ) ((allocate n).val σ) (List.replicate n.toNat 0) := by
  refine ⟨by simp [lengthNat], ?_⟩
  have hbase : ((allocate n).val σ).baseNat = σ.size :=
    toNat_val_alloc σ n hfrontier
  refine ⟨?_, ?_, ?_⟩
  · simp [hbase]
  · simpa using hspace
  · intro i hi
    simp only [List.length_replicate] at hi
    rw [hbase]
    simp only [List.getElem_replicate]
    simp [allocate, alloc, RAM.state, RamState.get, RamState.size,
      Array.getD]

/-- Allocation preserves the contents of every already represented buffer. -/
theorem allocate_frame {σ : RamState w} {b : Buffer w} {xs : List ℕ}
    (H : Holds σ b xs) (n : Word w) (hspace : σ.size + n.toNat ≤ 2 ^ w) :
    Holds ((allocate n).state σ) b xs := by
  refine ⟨H.length_eq, ?_, ?_, ?_⟩
  · have := H.contents.fits
    simp only [state_allocate, size_state_alloc]
    omega
  · simpa using hspace
  · intro i hi
    have hlt : b.baseNat + i < σ.size := by have := H.contents.fits; omega
    rw [state_allocate, get_state_alloc σ n hlt]
    exact H.contents.get i hi

/-- A specification-only input encoding. This describes preexisting input
memory; it is not an executable operation that constructs storage for free. -/
noncomputable def encodedState (xs : List ℕ) : RamState w :=
  { mem := (xs.map (BitVec.ofNat w)).toArray }

/-- A specification-only handle for input encoded at address zero. The words
are obtained by observing charged literals, not by exposing word constructors. -/
noncomputable def encodedHandle (xs : List ℕ) : Buffer w :=
  ofWords ((lit 0 : RAM w (Word w)).val (RamState.empty w))
    ((lit xs.length : RAM w (Word w)).val (RamState.empty w))

/-- Every word-bounded list whose length fits has an admissible input encoding.
The strict length bound is required because length is itself stored in a word. -/
theorem encoded_holds (xs : List ℕ) (hlen : xs.length < 2 ^ w)
    (hentries : ∀ i (hi : i < xs.length), xs[i] < 2 ^ w) :
    Holds (encodedState (w := w) xs) (encodedHandle (w := w) xs) xs := by
  have hbase : (encodedHandle (w := w) xs).baseNat = 0 := by
    simp [encodedHandle]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [encodedHandle, Nat.mod_eq_of_lt hlen]
  · simp [hbase, encodedState, RamState.size]
  · simpa [encodedState, RamState.size] using Nat.le_of_lt hlen
  · intro i hi
    rw [hbase]
    simp [encodedState, RamState.get, Array.getD, hi,
      Nat.mod_eq_of_lt (hentries i hi)]

end Buffer
end Arlib.Computation
