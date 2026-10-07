/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.Buffer

/-! # Two-word record buffers
Two disjoint buffers store record fields. Reads/writes charge two address additions
and two memory operations. Allocation reserves two cells per record, including
unused capacity; fields and lengths remain word registers. -/
namespace Arlib.Computation
private structure RecordBufferRep (w : Nat) where
  first : Buffer w
  second : Buffer w

def RecordBuffer (w : Nat) := RecordBufferRep w
namespace RecordBuffer
variable {w : Nat}
def ofBuffers (first second : Buffer w) : RecordBuffer w := ⟨first, second⟩
def first (b : RecordBuffer w) : Buffer w := RecordBufferRep.first b
def second (b : RecordBuffer w) : Buffer w := RecordBufferRep.second b
def capacity (b : RecordBuffer w) : Word w := b.first.length
noncomputable def capacityNat (b : RecordBuffer w) : Nat := b.capacity.toNat

structure Holds (σ : RamState w) (b : RecordBuffer w) (xs : List (Nat × Nat)) : Prop where
  first : Buffer.Holds σ b.first (xs.map Prod.fst)
  second : Buffer.Holds σ b.second (xs.map Prod.snd)
  disjoint : Disjoint (block b.first.baseNat xs.length) (block b.second.baseNat xs.length)

def read (b : RecordBuffer w) (i : Word w) : RAM w (Word w × Word w) := do
  let x ← Buffer.read b.first i
  let y ← Buffer.read b.second i
  pure (x,y)
def write (b : RecordBuffer w) (i : Word w) (v : Word w × Word w) : RAM w Unit := do
  Buffer.write b.first i v.1
  Buffer.write b.second i v.2

@[simp] theorem state_read (b : RecordBuffer w) (i : Word w) (σ : RamState w) :
    (read b i).state σ = σ := by simp [read]
@[simp] theorem steps_read (b : RecordBuffer w) (i : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (read b i) σ = 4 := by simp [read]
@[simp] theorem steps_write (b : RecordBuffer w) (i : Word w) (v : Word w × Word w)
    (σ : RamState w) : RAM.steps CostModel.unitCost (write b i v) σ = 4 := by simp [write]
@[simp] theorem size_state_write (b : RecordBuffer w) (i : Word w) (v : Word w × Word w)
    (σ : RamState w) : ((write b i v).state σ).size = σ.size := by simp [write]

theorem capacity_eq {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) : b.capacityNat = xs.length := by
  simpa [capacityNat, capacity, Buffer.lengthNat] using H.first.length_eq

theorem read_spec {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) {i : Word w} (hi : i.toNat < xs.length) :
    ((read b i).val σ).1.toNat = xs[i.toNat].1 ∧
    ((read b i).val σ).2.toNat = xs[i.toNat].2 := by
  have h1 := Buffer.read_spec H.first (by simpa using hi)
  have h2 := Buffer.read_spec H.second (by simpa using hi)
  simpa [read] using And.intro h1 h2

theorem write_spec {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) {i : Word w} (hi : i.toNat < xs.length) (v : Word w × Word w) :
    Holds ((write b i v).state σ) b (xs.set i.toNat (v.1.toNat,v.2.toNat)) := by
  have hi1 : i.toNat < (xs.map Prod.fst).length := by simpa using hi
  have hi2 : i.toNat < (xs.map Prod.snd).length := by simpa using hi
  have hs2 := Buffer.write_frame H.first H.second hi1 v.1 (by simpa using H.disjoint.symm)
  have hs1 := Buffer.write_spec H.first hi1 v.1
  have hs1' := Buffer.write_frame hs2 hs1 hi2 v.2 (by simpa using H.disjoint)
  have hs2' := Buffer.write_spec hs2 hi2 v.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [write, List.map_set] using hs1'
  · simpa [write, List.map_set] using hs2'
  · simpa using H.disjoint

theorem write_frame {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) {other : Buffer w} {ys : List Nat} (Ho : Buffer.Holds σ other ys)
    {i : Word w} (hi : i.toNat < xs.length) (v : Word w × Word w)
    (h1 : Disjoint (block other.baseNat ys.length) (block b.first.baseNat xs.length))
    (h2 : Disjoint (block other.baseNat ys.length) (block b.second.baseNat xs.length)) :
    Buffer.Holds ((write b i v).state σ) other ys := by
  have hs := Buffer.write_frame H.first H.second (by simpa using hi) v.1
    (by simpa using H.disjoint.symm)
  have ho := Buffer.write_frame H.first Ho (by simpa using hi) v.1 (by simpa using h1)
  simpa [write] using Buffer.write_frame hs ho (by simpa using hi) v.2 (by simpa using h2)

theorem frame_write {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) {other : Buffer w} {ys : List Nat} (Ho : Buffer.Holds σ other ys)
    {i : Word w} (hi : i.toNat < ys.length) (v : Word w)
    (h1 : Disjoint (block b.first.baseNat xs.length) (block other.baseNat ys.length))
    (h2 : Disjoint (block b.second.baseNat xs.length) (block other.baseNat ys.length)) :
    Holds ((Buffer.write other i v).state σ) b xs :=
  ⟨Buffer.write_frame Ho H.first hi v (by simpa using h1),
   Buffer.write_frame Ho H.second hi v (by simpa using h2), H.disjoint⟩

def allocate (n : Word w) : RAM w (RecordBuffer w) := do
  let a ← Buffer.allocate n
  let b ← Buffer.allocate n
  pure (ofBuffers a b)
@[simp] theorem steps_allocate (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate n) σ = 2*n.toNat := by simp [allocate, Buffer.allocate]; omega
@[simp] theorem size_state_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).state σ).size = σ.size + 2*n.toNat := by simp [allocate, Buffer.allocate]; omega

theorem allocate_spec (σ : RamState w) (n : Word w)
    (hf : σ.size < 2^w) (hs : σ.size + 2*n.toNat ≤ 2^w) :
    Holds ((allocate n).state σ) ((allocate n).val σ) (List.replicate n.toNat (0,0)) := by
  let σ₁ := (Buffer.allocate n).state σ
  have he : σ₁.size = σ.size + n.toNat := by simp [σ₁]
  have hs₁ : σ.size + n.toNat ≤ 2^w := by omega
  have hf₁ : σ₁.size < 2^w := by rw [he]; omega
  have hs₂ : σ₁.size + n.toNat ≤ 2^w := by rw [he]; omega
  have ha := Buffer.allocate_frame (Buffer.allocate_spec σ n hf hs₁) n hs₂
  have hb := Buffer.allocate_spec σ₁ n hf₁ hs₂
  refine ⟨?_, ?_, ?_⟩
  · change Buffer.Holds ((Buffer.allocate n).state σ₁) ((Buffer.allocate n).val σ) _
    simpa [σ₁] using ha
  · change Buffer.Holds ((Buffer.allocate n).state σ₁) ((Buffer.allocate n).val σ₁) _
    simpa using hb
  · change Disjoint (block ((Buffer.allocate n).val σ).baseNat _)
      (block ((Buffer.allocate n).val σ₁).baseNat _)
    have hbase₁ : ((Buffer.allocate n).val σ).baseNat = σ.size := toNat_val_alloc σ n hf
    have hbase₂ : ((Buffer.allocate n).val σ₁).baseNat = σ₁.size := toNat_val_alloc σ₁ n hf₁
    rw [hbase₁, hbase₂, he, List.length_replicate]
    exact disjoint_block (le_refl _)
/-- Subsequent allocation preserves both fields of an existing record buffer. -/
theorem allocate_frame {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : Holds σ b xs) (n : Word w) (hs : σ.size+n.toNat ≤ 2^w) :
    Holds ((Buffer.allocate n).state σ) b xs :=
  ⟨Buffer.allocate_frame H.first n hs, Buffer.allocate_frame H.second n hs, H.disjoint⟩

/-- Allocating record storage preserves any already represented buffer. -/
theorem frame_allocate {σ : RamState w} {b : Buffer w} {xs : List Nat}
    (H : Buffer.Holds σ b xs) (n : Word w) (hs : σ.size+2*n.toNat ≤ 2^w) :
    Buffer.Holds ((allocate n).state σ) b xs := by
  have ha := Buffer.allocate_frame H n (by omega)
  have hb := Buffer.allocate_frame ha n (by simp only [Buffer.state_allocate, size_state_alloc]; omega)
  exact hb

end RecordBuffer
end Arlib.Computation
