/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.RecordBuffer
import Arlib.Computation.SignedWord
import Arlib.Computation.Realization

/-! # Signed storage
Each entry occupies two cells: a sign code (0 or 1) and an unsigned magnitude.
Both signs of zero are admissible. Reads reconstruct a control bit using a charged
comparison; writes materialize the sign with a charged literal. -/
namespace Arlib.Computation
private structure SignedBufferRep (w : Nat) where
  records : RecordBuffer w

def SignedBuffer (w : Nat) := SignedBufferRep w
namespace SignedBuffer
variable {w : Nat}
def ofRecords (b : RecordBuffer w) : SignedBuffer w := ⟨b⟩
def records (b : SignedBuffer w) : RecordBuffer w := SignedBufferRep.records b
def length (b : SignedBuffer w) : Word w := b.records.capacity

def decode (v : Nat × Nat) : Int := if v.1 = 1 then -(v.2 : Int) else v.2
structure Encoding (σ : RamState w) (b : SignedBuffer w) (xs : List Int) (cells : List (Nat × Nat)) : Prop where
  storage : RecordBuffer.Holds σ b.records cells
  values : cells.map decode = xs
  signs : ∀ v ∈ cells, v.1 = 0 ∨ v.1 = 1

def Holds (σ : RamState w) (b : SignedBuffer w) (xs : List Int) : Prop :=
  ∃ cells, Encoding σ b xs cells

def read (b : SignedBuffer w) (i : Word w) : RAM w (SignedWord w) := do
  let v ← RecordBuffer.read b.records i
  let one ← lit 1
  let negative ← eq v.1 one
  pure (SignedWord.ofParts negative v.2)
def write (b : SignedBuffer w) (i : Word w) (x : SignedWord w) : RAM w Unit := do
  let flag ← lit (if x.sign then 1 else 0)
  RecordBuffer.write b.records i (flag,x.magnitudeWord)

@[simp] theorem state_read (b : SignedBuffer w) (i : Word w) (σ : RamState w) :
    (read b i).state σ = σ := rfl
@[simp] theorem steps_read (b : SignedBuffer w) (i : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (read b i) σ = 6 := by simp [read]
@[simp] theorem steps_write (b : SignedBuffer w) (i : Word w) (x : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (write b i x) σ = 5 := by simp [write]
@[simp] theorem size_state_write (b : SignedBuffer w) (i : Word w) (x : SignedWord w) (σ : RamState w) :
    ((write b i x).state σ).size = σ.size := by simp [write]

theorem length_eq {σ : RamState w} {b : SignedBuffer w} {xs : List Int}
    (H : Holds σ b xs) : b.length.toNat = xs.length := by
  rcases H with ⟨cells, H⟩
  have := RecordBuffer.capacity_eq H.storage
  simpa [length, RecordBuffer.capacityNat, ← H.values] using this

theorem read_spec {σ : RamState w} {b : SignedBuffer w} {xs : List Int}
    (H : Holds σ b xs) {i : Word w} (hi : i.toNat < xs.length) (hw : 1 < 2^w) :
    ((read b i).val σ).value = xs[i.toNat] := by
  rcases H with ⟨cells, H⟩
  have hlen : cells.length = xs.length := by rw [← H.values, List.length_map]
  have hpair := RecordBuffer.read_spec H.storage (by omega : i.toNat < cells.length)
  simp only [← H.values, List.getElem_map]
  simp only [read, RAM.val_bind, RecordBuffer.state_read, state_lit, state_eq,
    RAM.val_pure, SignedWord.value_ofParts, val_eq, toNat_lit, Nat.mod_eq_of_lt hw,
    hpair.1, hpair.2, decode, decide_eq_true_eq]

theorem write_spec {σ : RamState w} {b : SignedBuffer w} {xs : List Int}
    (H : Holds σ b xs) {i : Word w} (hi : i.toNat < xs.length) (x : SignedWord w)
    (hw : 1 < 2^w) : Holds ((write b i x).state σ) b (xs.set i.toNat x.value) := by
  rcases H with ⟨cells, H⟩
  let f := (lit (if x.sign then 1 else 0) : RAM w (Word w)).val σ
  have hf : f.toNat = if x.sign then 1 else 0 := by
    cases h : x.sign <;> simp [f, h, Nat.mod_eq_of_lt hw]
  have hd : decode (f.toNat, x.magnitudeWord.toNat) = x.value := by
    rw [hf, SignedWord.value_eq_sign]; cases x.sign <;> simp [decode]
  have hlen : cells.length = xs.length := by rw [← H.values, List.length_map]
  refine ⟨cells.set i.toNat (f.toNat,x.magnitudeWord.toNat), ?_, ?_, ?_⟩
  · simpa [write, f] using RecordBuffer.write_spec H.storage (by omega) (f,x.magnitudeWord)
  · rw [List.map_set, H.values, hd]
  · intro v hv
    rcases List.mem_or_eq_of_mem_set hv with hv | hv
    · exact H.signs v hv
    · subst v; rw [hf]; cases x.sign <;> simp

/-- Writes preserve any disjoint unsigned buffer. -/
theorem write_frame {σ : RamState w} {b : SignedBuffer w} {xs : List Int}
    (H : Holds σ b xs) {other : Buffer w} {ys : List Nat} (Ho : Buffer.Holds σ other ys)
    {i : Word w} (hi : i.toNat < xs.length) (x : SignedWord w)
    (h1 : Disjoint (block other.baseNat ys.length) (block b.records.first.baseNat xs.length))
    (h2 : Disjoint (block other.baseNat ys.length) (block b.records.second.baseNat xs.length)) :
    Buffer.Holds ((write b i x).state σ) other ys := by
  rcases H with ⟨cells, H⟩
  have hlen : cells.length = xs.length := by rw [← H.values, List.length_map]
  simpa [write] using RecordBuffer.write_frame H.storage Ho (by omega)
    ((lit (if x.sign then 1 else 0)).val σ,x.magnitudeWord) (by simpa [hlen] using h1)
    (by simpa [hlen] using h2)

def allocate (n : Word w) : RAM w (SignedBuffer w) := do
  let b ← RecordBuffer.allocate n
  pure (ofRecords b)
@[simp] theorem steps_allocate (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate n) σ = 2*n.toNat := by
  simp only [allocate, RAM.steps_bind, RecordBuffer.steps_allocate, RAM.steps_pure, Nat.add_zero]
@[simp] theorem size_state_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).state σ).size = σ.size + 2*n.toNat := by
  change ((RecordBuffer.allocate n).state σ).size = _
  exact RecordBuffer.size_state_allocate n σ

theorem allocate_spec (σ : RamState w) (n : Word w)
    (hf : σ.size < 2^w) (hs : σ.size+2*n.toNat ≤ 2^w) :
    Holds ((allocate n).state σ) ((allocate n).val σ) (List.replicate n.toNat 0) := by
  refine ⟨List.replicate n.toNat (0,0), ?_, ?_, ?_⟩
  · exact RecordBuffer.allocate_spec σ n hf hs
  · simp [decode]
  · intro v hv; have := List.eq_of_mem_replicate hv; subst v; simp

/-- External disjoint writes preserve a signed representation, including its sign codes. -/
theorem frame_write {σ : RamState w} {b : SignedBuffer w} {xs : List Int}
    (H : Holds σ b xs) {other : Buffer w} {ys : List Nat} (Ho : Buffer.Holds σ other ys)
    {i : Word w} (hi : i.toNat < ys.length) (v : Word w)
    (h1 : Disjoint (block b.records.first.baseNat xs.length) (block other.baseNat ys.length))
    (h2 : Disjoint (block b.records.second.baseNat xs.length) (block other.baseNat ys.length)) :
    Holds ((Buffer.write other i v).state σ) b xs := by
  rcases H with ⟨cells,H⟩
  have hl : cells.length = xs.length := by rw [← H.values, List.length_map]
  exact ⟨cells, RecordBuffer.frame_write H.storage Ho hi v (by simpa [hl] using h1)
    (by simpa [hl] using h2), H.values, H.signs⟩

/-- A concrete write realizes the logical update, including its resulting storage. -/
theorem realizes_write (xs : List Int) (b : SignedBuffer w) (i : Word w) (index : Nat)
    (x : SignedWord w) (z : Int) (hw : 1 < 2^w) :
    Realizes (Charged.op .store (xs.set index z) : Charged Op Unit (List Int)) (write b i x)
      (fun σ => Holds σ b xs ∧ i.toNat=index ∧ index<xs.length ∧ x.value=z)
      (fun values _ σ => Holds σ b values) 5 where
  correct := by
    intro σ ⟨H,hi,hlen,hv⟩
    simpa [hi,hv] using write_spec H (i := i) (by omega) x hw
  steps_le := by intro σ _; simp

/-- A source-level load has an actual two-cell RAM implementation. -/
theorem realizes_read (xs : List Int) (b : SignedBuffer w) (i : Word w) (index : Nat)
    (hw : 1 < 2^w) :
    Realizes (Charged.op .load (xs[index]?.getD 0) : Charged Op Unit Int) (read b i)
      (fun σ => Holds σ b xs ∧ i.toNat = index ∧ index < xs.length)
      (fun a r σ => a = r.value ∧ Holds σ b xs) 6 where
  correct := by
    intro σ ⟨H, he, hi⟩
    refine ⟨?_, by simpa using H⟩
    simp only [Charged.val_op]
    have hr := read_spec H (i := i) (by omega) hw
    simpa [he, hi] using hr.symm
  steps_le := by intro σ _; simp
end SignedBuffer
end Arlib.Computation
