/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.RecordBuffer
import Arlib.Computation.WordLoop

/-! # Pooled record buckets
A shared pool reserves two record fields and one link cell per record, plus one
head cell per bucket: `3*M + p` cells. Links are one-based; zero denotes the empty
chain. Insertion prepends, so traversal is in reverse insertion order. It never
allocates `M` cells independently for every bucket. Exhaustion is reported.
-/
namespace Arlib.Computation
private structure BucketBufferRep (w : Nat) where
  records : RecordBuffer w
  links : Buffer w
  heads : Buffer w
  used : Word w

def BucketBuffer (w : Nat) := BucketBufferRep w
namespace BucketBuffer
variable {w : Nat}
def ofParts (r : RecordBuffer w) (n h : Buffer w) (u : Word w) : BucketBuffer w := ⟨r,n,h,u⟩
def records (b : BucketBuffer w) : RecordBuffer w := BucketBufferRep.records b
def links (b : BucketBuffer w) : Buffer w := BucketBufferRep.links b
def heads (b : BucketBuffer w) : Buffer w := BucketBufferRep.heads b
def used (b : BucketBuffer w) : Word w := BucketBufferRep.used b
def capacity (b : BucketBuffer w) : Word w := b.records.capacity
def bucketCount (b : BucketBuffer w) : Word w := b.heads.length

/-- Physical pool invariant, with all four blocks disjoint. -/
structure Holds (σ : RamState w) (b : BucketBuffer w)
    (rs : List (Nat × Nat)) (ns hs : List Nat) : Prop where
  records : RecordBuffer.Holds σ b.records rs
  links : Buffer.Holds σ b.links ns
  heads : Buffer.Holds σ b.heads hs
  lengths : ns.length = rs.length
  room : b.used.toNat ≤ rs.length
  linkBounds : ∀ i (hi : i < ns.length), i < b.used.toNat → ns[i] ≤ b.used.toNat
  headBounds : ∀ i (hi : i < hs.length), hs[i] ≤ b.used.toNat
  nextFirst : Disjoint (block b.links.baseNat ns.length) (block b.records.first.baseNat rs.length)
  nextSecond : Disjoint (block b.links.baseNat ns.length) (block b.records.second.baseNat rs.length)
  headFirst : Disjoint (block b.heads.baseNat hs.length) (block b.records.first.baseNat rs.length)
  headSecond : Disjoint (block b.heads.baseNat hs.length) (block b.records.second.baseNat rs.length)
  nextHead : Disjoint (block b.heads.baseNat hs.length) (block b.links.baseNat ns.length)

/-- Logical chains are finite and bounded by the number of occupied slots. -/
inductive Chain (rs : List (Nat × Nat)) (ns : List Nat) (used : Nat) : Nat → List (Nat × Nat) → Prop
  | nil : Chain rs ns used 0 []
  | cons {h : Nat} {tail : List (Nat × Nat)} (positive : 0 < h) (occupied : h ≤ used)
      (record : h-1 < rs.length) (link : h-1 < ns.length)
      (rest : Chain rs ns used ns[h-1] tail) : Chain rs ns used h (rs[h-1] :: tail)

/-- Insert a record into a valid bucket if the shared pool has space. -/
def push (b : BucketBuffer w) (key : Word w) (v : Word w × Word w) : RAM w (Option (BucketBuffer w)) := do
  let valid ← lt key b.bucketCount
  if valid then do
    let room ← lt b.used b.capacity
    if room then do
      let old ← Buffer.read b.heads key
      let one ← lit 1
      let newHead ← add b.used one
      RecordBuffer.write b.records b.used v
      Buffer.write b.links b.used old
      Buffer.write b.heads key newHead
      pure (some (ofParts b.records b.links b.heads newHead))
    else pure none
  else pure none

@[simp] theorem size_state_push (b : BucketBuffer w) (k : Word w) (v : Word w × Word w) (σ : RamState w) :
    ((push b k v).state σ).size = σ.size := by
  simp only [push, RAM.state_bind, state_lt]
  split <;> simp only [RAM.state_bind, state_lt, RAM.state_pure]
  split <;> simp [RecordBuffer.size_state_write]

theorem steps_push_le (b : BucketBuffer w) (k : Word w) (v : Word w × Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (push b k v) σ ≤ 14 := by
  simp only [push, RAM.steps_bind, steps_lt, state_lt, CostModel.unitCost_cost]
  split <;> simp only [RAM.steps_bind, steps_lt, state_lt, RAM.steps_pure, CostModel.unitCost_cost]
  · split <;> simp [RecordBuffer.steps_write]
  · omega

/-- Read the stored head pointer (zero denotes the empty bucket). -/
def head (b : BucketBuffer w) (key : Word w) : RAM w (Word w) := Buffer.read b.heads key
@[simp] theorem state_head (b : BucketBuffer w) (k : Word w) (σ : RamState w) : (head b k).state σ = σ := rfl
@[simp] theorem steps_head (b : BucketBuffer w) (k : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (head b k) σ = 2 := by simp [head]

/-- Follow one link. Empty pointers return none; an occupied pointer returns
its record and successor. Only charged subtraction produces the zero-based index. -/
def next (b : BucketBuffer w) (pointer : Word w) : RAM w (Option ((Word w × Word w) × Word w)) := do
  let zero ← lit 0
  let empty ← eq pointer zero
  if empty then pure none else do
    let one ← lit 1
    let i ← sub pointer one
    let v ← RecordBuffer.read b.records i
    let n ← Buffer.read b.links i
    pure (some (v,n))
@[simp] theorem state_next (b : BucketBuffer w) (h : Word w) (σ : RamState w) : (next b h).state σ = σ := by
  simp only [next, RAM.state_bind, state_lit, state_eq]
  split <;> simp

theorem steps_next_le (b : BucketBuffer w) (h : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (next b h) σ ≤ 10 := by
  simp only [next, RAM.steps_bind, steps_lit, steps_eq, state_lit, state_eq, CostModel.unitCost_cost]
  split <;> simp

theorem head_spec {σ : RamState w} {b : BucketBuffer w} {rs : List (Nat × Nat)} {ns hs : List Nat}
    (H : Holds σ b rs ns hs) {k : Word w} (hk : k.toNat < hs.length) :
    ((head b k).val σ).toNat = hs[k.toNat] := Buffer.read_spec H.heads hk

/-- The next call returns exactly the represented record and successor. -/
theorem next_spec {σ : RamState w} {b : BucketBuffer w} {rs : List (Nat × Nat)} {ns hs : List Nat}
    (H : Holds σ b rs ns hs) {h : Word w} (hh : 0 < h.toNat) (hu : h.toNat ≤ b.used.toNat)
    (hw : 1 < 2^w) :
    ∃ v n, (next b h).val σ = some (v,n) ∧
      v.1.toNat = (rs[h.toNat-1]' (by have := H.room; omega)).1 ∧ v.2.toNat = (rs[h.toNat-1]' (by have := H.room; omega)).2 ∧ n.toNat = ns[h.toNat-1]' (by have := H.room; have := H.lengths; omega) := by
  let i := (sub h ((lit 1 : RAM w (Word w)).val σ)).val σ
  have hi : i.toNat = h.toNat-1 := by
    exact (toNat_sub_of_le σ h _ (by simp [Nat.mod_eq_of_lt hw]; omega)).trans (by simp [Nat.mod_eq_of_lt hw])
  have hr : i.toNat < rs.length := by have := H.room; omega
  have hn : i.toNat < ns.length := by rw [H.lengths]; exact hr
  refine ⟨(RecordBuffer.read b.records i).val σ, (Buffer.read b.links i).val σ, ?_, ?_⟩
  · simp [next, hh.ne', i]
  · have hp := RecordBuffer.read_spec H.records hr
    have hl := Buffer.read_spec H.links hn
    simpa [hi] using And.intro hp.1 (And.intro hp.2 hl)

/-- The concrete stores performed by successful insertion, exposed for proofs. -/
def insertAt (b : BucketBuffer w) (k : Word w) (v : Word w × Word w)
    (old newHead : Word w) : RAM w Unit := do
  RecordBuffer.write b.records b.used v
  Buffer.write b.links b.used old
  Buffer.write b.heads k newHead

/-- Each store preserves every other pool field. This theorem supplies exact
updated contents independently of the logical chain interpretation. -/
theorem insertAt_spec {σ : RamState w} {b : BucketBuffer w} {rs : List (Nat × Nat)} {ns hs : List Nat}
    (H : Holds σ b rs ns hs) {k : Word w} (hk : k.toNat < hs.length)
    (hu : b.used.toNat < rs.length) (v : Word w × Word w) (old newHead : Word w) :
    RecordBuffer.Holds ((insertAt b k v old newHead).state σ) b.records
      (rs.set b.used.toNat (v.1.toNat,v.2.toNat)) ∧
    Buffer.Holds ((insertAt b k v old newHead).state σ) b.links (ns.set b.used.toNat old.toNat) ∧
    Buffer.Holds ((insertAt b k v old newHead).state σ) b.heads (hs.set k.toNat newHead.toNat) := by
  have hr := RecordBuffer.write_spec H.records hu v
  have hn := RecordBuffer.write_frame H.records H.links hu v H.nextFirst H.nextSecond
  have hh := RecordBuffer.write_frame H.records H.heads hu v H.headFirst H.headSecond
  have hu' : b.used.toNat < ns.length := by rw [H.lengths]; exact hu
  have hr' := RecordBuffer.frame_write hr hn hu' old (by simpa using H.nextFirst.symm)
    (by simpa using H.nextSecond.symm)
  have hh' := Buffer.write_frame hn hh hu' old H.nextHead
  have hn' := Buffer.write_spec hn hu' old
  have hr'' := RecordBuffer.frame_write hr' hh' hk newHead (by simpa using H.headFirst.symm)
    (by simpa using H.headSecond.symm)
  have hn'' := Buffer.write_frame hh' hn' hk newHead (by simpa using H.nextHead.symm)
  have hh'' := Buffer.write_spec hh' hk newHead
  simpa [insertAt] using And.intro hr'' (And.intro hn'' hh'')

/-- Allocation includes all reserved cells and initializes all heads to zero. -/
def allocate (recordCapacity bucketCount : Word w) : RAM w (BucketBuffer w) := do
  let r ← RecordBuffer.allocate recordCapacity
  let n ← Buffer.allocate recordCapacity
  let h ← Buffer.allocate bucketCount
  let zero ← lit 0
  pure (ofParts r n h zero)
@[simp] theorem steps_allocate (m p : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate m p) σ = 3*m.toNat+p.toNat+1 := by
  simp [allocate, Buffer.allocate]; omega
@[simp] theorem size_state_allocate (m p : Word w) (σ : RamState w) :
    ((allocate m p).state σ).size = σ.size+3*m.toNat+p.toNat := by
  simp only [allocate, RAM.state_bind, state_lit, RAM.state_pure,
    RecordBuffer.size_state_allocate, Buffer.state_allocate, size_state_alloc]
  omega
/-- A fresh pool slot cannot modify any occupied logical chain. -/
theorem Chain.setFresh {rs : List (Nat × Nat)} {ns : List Nat} {u h : Nat}
    {xs : List (Nat × Nat)} (H : Chain rs ns u h xs) (v : Nat × Nat) (n : Nat) :
    Chain (rs.set u v) (ns.set u n) (u+1) h xs := by
  induction H with
  | nil => exact Chain.nil
  | @cons h tail hp hu hr hn rest ih =>
    have he : u ≠ h-1 := by omega
    have hn' : h-1 < (ns.set u n).length := by simpa using hn
    have hr' : h-1 < (rs.set u v).length := by simpa using hr
    have hs : (ns.set u n)[h-1] = ns[h-1] := List.getElem_set_ne he hn'
    have hv : (rs.set u v)[h-1] = rs[h-1] := List.getElem_set_ne he hr'
    simpa only [hs, hv] using Chain.cons hp (by omega) hr' hn' (by simpa only [hs] using ih)

/-- Prepending creates exactly one new node with the old chain as its suffix. -/
theorem Chain.prepend {rs : List (Nat × Nat)} {ns : List Nat} {u h : Nat}
    {xs : List (Nat × Nat)} (H : Chain rs ns u h xs) (hu : u < rs.length)
    (hn : u < ns.length) (v : Nat × Nat) :
    Chain (rs.set u v) (ns.set u h) (u+1) (u+1) (v::xs) := by
  have ht := H.setFresh v h
  have hr' : (u+1)-1 < (rs.set u v).length := by simpa using hu
  have hn' : (u+1)-1 < (ns.set u h).length := by simpa using hn
  simpa using Chain.cons (by omega : 0 < u+1) (le_refl (u+1)) hr' hn' (by simpa using ht)

/-- Success returns the updated handle and preserves the physical pool invariant. -/
theorem push_spec {σ : RamState w} {b : BucketBuffer w} {rs : List (Nat × Nat)} {ns hs : List Nat}
    (H : Holds σ b rs ns hs) {k : Word w} (hk : k.toNat < hs.length)
    (hu : b.used.toNat < rs.length) (v : Word w × Word w) (hw : 1 < 2^w) :
    ∃ b', (push b k v).val σ = some b' ∧ b'.used.toNat = b.used.toNat+1 ∧
      Holds ((push b k v).state σ) b'
        (rs.set b.used.toNat (v.1.toNat,v.2.toNat))
        (ns.set b.used.toNat hs[k.toNat]) (hs.set k.toNat (b.used.toNat+1)) := by
  let old := (Buffer.read b.heads k).val σ
  let newHead := (add b.used ((lit 1 : RAM w (Word w)).val σ)).val σ
  have ho : old.toNat = hs[k.toNat] := Buffer.read_spec H.heads hk
  have hc : b.capacity.toNat = rs.length := RecordBuffer.capacity_eq H.records
  have hb : b.bucketCount.toNat = hs.length := H.heads.length_eq
  have hn : newHead.toNat = b.used.toNat+1 := by
    have hf : b.used.toNat+1 < 2^w := by have := b.capacity.toNat_lt; omega
    simp [newHead, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hf]
  let b' := ofParts b.records b.links b.heads newHead
  have hval : (push b k v).val σ = some b' := by
    simp [push, hk, hu, hc, hb, newHead, b']
  have hstate : (push b k v).state σ = (insertAt b k v old newHead).state σ := by
    simp [push, insertAt, hk, hu, hc, hb, old, newHead]
  refine ⟨b', hval, hn, ?_⟩
  rw [hstate]
  have hs' := insertAt_spec H hk hu v old newHead
  refine ⟨hs'.1, ?_, ?_, by simpa using H.lengths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ho, b', ofParts, links] using hs'.2.1
  · simpa only [hn, b', ofParts, heads] using hs'.2.2
  · change newHead.toNat ≤ (rs.set _ _).length; simp only [hn, List.length_set]; omega
  · intro i hi hiu
    change (ns.set b.used.toNat hs[k.toNat])[i] ≤ newHead.toNat
    rw [hn]
    by_cases he : b.used.toNat = i
    · subst i; simp only [List.getElem_set_self]; have := H.headBounds k.toNat hk; omega
    · rw [List.getElem_set_ne he hi]
      have := H.linkBounds i (by simpa using hi) (by change i < newHead.toNat at hiu; rw [hn] at hiu; omega)
      omega
  · intro i hi
    change (hs.set k.toNat (b.used.toNat+1))[i] ≤ newHead.toNat
    rw [hn]
    by_cases he : k.toNat = i
    · subst i; simp
    · rw [List.getElem_set_ne he hi]; have := H.headBounds i (by simpa using hi); omega
  · simpa [b', ofParts, links, records, used] using H.nextFirst
  · simpa [b', ofParts, links, records, used] using H.nextSecond
  · simpa [b', ofParts, heads, records, used] using H.headFirst
  · simpa [b', ofParts, heads, records, used] using H.headSecond
  · simpa [b', ofParts, heads, links, used] using H.nextHead

/-- Invalid keys and exhausted pools leave both memory and the handle untouched. -/
theorem push_reject (b : BucketBuffer w) (k : Word w) (v : Word w × Word w) (σ : RamState w)
    (h : b.bucketCount.toNat ≤ k.toNat ∨ b.capacity.toNat ≤ b.used.toNat) :
    (push b k v).val σ = none ∧ (push b k v).state σ = σ := by
  rcases h with h | h
  · simp [push, show ¬ k.toNat < b.bucketCount.toNat by omega]
  · by_cases hk : k.toNat < b.bucketCount.toNat <;>
      simp [push, hk, show ¬ b.used.toNat < b.capacity.toNat by omega]

/-- The initial pool represents empty chains in every bucket. The intermediate
frontiers fit even when a following allocation has zero length. -/
theorem allocate_spec (σ : RamState w) (m p : Word w)
    (hf : σ.size < 2^w) (hi : σ.size+3*m.toNat < 2^w)
    (hs : σ.size+3*m.toNat+p.toNat ≤ 2^w) :
    Holds ((allocate m p).state σ) ((allocate m p).val σ)
      (List.replicate m.toNat (0,0)) (List.replicate m.toNat 0) (List.replicate p.toNat 0) := by
  let σ₁ := (RecordBuffer.allocate m).state σ
  let σ₂ := (Buffer.allocate m).state σ₁
  have he₁ : σ₁.size = σ.size+2*m.toNat := RecordBuffer.size_state_allocate m σ
  have he₂ : σ₂.size = σ.size+3*m.toNat := by simp [σ₂, he₁]; omega
  have hf₁ : σ₁.size < 2^w := by omega
  have hs₁ : σ.size+2*m.toNat ≤ 2^w := by omega
  have hs₂ : σ₁.size+m.toNat ≤ 2^w := by omega
  have hf₂ : σ₂.size < 2^w := by omega
  have hs₃ : σ₂.size+p.toNat ≤ 2^w := by omega
  have hr₀ := RecordBuffer.allocate_spec σ m hf hs₁
  have hr₁ := RecordBuffer.allocate_frame hr₀ m hs₂
  have hr := RecordBuffer.allocate_frame hr₁ p hs₃
  have hn := Buffer.allocate_frame (Buffer.allocate_spec σ₁ m hf₁ hs₂) p hs₃
  have hh := Buffer.allocate_spec σ₂ p hf₂ hs₃
  have hu : ((allocate m p).val σ).used.toNat = 0 := by
    change ((lit 0 : RAM w (Word w)).val ((Buffer.allocate p).state σ₂)).toNat = 0
    simp
  have ha : ((RecordBuffer.allocate m).val σ).first.baseNat = σ.size := toNat_val_alloc σ m hf
  have hb : ((RecordBuffer.allocate m).val σ).second.baseNat = σ.size+m.toNat := by
    change ((Buffer.allocate m).val ((Buffer.allocate m).state σ)).baseNat = _
    have hfhalf : σ.size+m.toNat < 2^w := by omega
    have hbase : ((Buffer.allocate m).val ((Buffer.allocate m).state σ)).baseNat =
        ((Buffer.allocate m).state σ).size :=
      toNat_val_alloc ((Buffer.allocate m).state σ) m (by simpa only [Buffer.state_allocate, size_state_alloc] using hfhalf)
    simpa only [Buffer.state_allocate, size_state_alloc] using hbase
  have hc : ((Buffer.allocate m).val σ₁).baseNat = σ.size+2*m.toNat := by
    rw [← he₁]; exact toNat_val_alloc σ₁ m hf₁
  have hd : ((Buffer.allocate p).val σ₂).baseNat = σ.size+3*m.toNat := by
    rw [← he₂]; exact toNat_val_alloc σ₂ p hf₂
  refine ⟨hr, hn, hh, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu]; simp
  · intro i _ hi; rw [hu] at hi; omega
  · intro i hi; simp only [List.getElem_replicate, hu]; exact le_refl 0
  · change Disjoint (block ((Buffer.allocate m).val σ₁).baseNat _)
      (block ((RecordBuffer.allocate m).val σ).first.baseNat _)
    rw [hc, ha, List.length_replicate, List.length_replicate]
    exact (disjoint_block (by omega)).symm
  · change Disjoint (block ((Buffer.allocate m).val σ₁).baseNat _)
      (block ((RecordBuffer.allocate m).val σ).second.baseNat _)
    rw [hc, hb, List.length_replicate, List.length_replicate]
    exact (disjoint_block (by omega)).symm
  · change Disjoint (block ((Buffer.allocate p).val σ₂).baseNat _)
      (block ((RecordBuffer.allocate m).val σ).first.baseNat _)
    rw [hd, ha, List.length_replicate, List.length_replicate]
    exact (disjoint_block (by omega)).symm
  · change Disjoint (block ((Buffer.allocate p).val σ₂).baseNat _)
      (block ((RecordBuffer.allocate m).val σ).second.baseNat _)
    rw [hd, hb, List.length_replicate, List.length_replicate]
    exact (disjoint_block (by omega)).symm
  · change Disjoint (block ((Buffer.allocate p).val σ₂).baseNat _)
      (block ((Buffer.allocate m).val σ₁).baseNat _)
    rw [hd, hc, List.length_replicate, List.length_replicate]
    exact (disjoint_block (by omega)).symm

/-- Allocating a pool preserves an already represented record buffer. -/
theorem allocate_frame {σ : RamState w} {b : RecordBuffer w} {xs : List (Nat × Nat)}
    (H : RecordBuffer.Holds σ b xs) (m p : Word w) (hs : σ.size+3*m.toNat+p.toNat ≤ 2^w) :
    RecordBuffer.Holds ((allocate m p).state σ) b xs := by
  have h1 : σ.size+2*m.toNat ≤ 2^w := by omega
  have ha : RecordBuffer.Holds ((RecordBuffer.allocate m).state σ) b xs :=
    ⟨RecordBuffer.frame_allocate H.first m h1, RecordBuffer.frame_allocate H.second m h1, H.disjoint⟩
  have hb := RecordBuffer.allocate_frame ha m (by rw [RecordBuffer.size_state_allocate]; omega)
  have hc := RecordBuffer.allocate_frame hb p (by simp only [Buffer.state_allocate,
    size_state_alloc, RecordBuffer.size_state_allocate]; omega)
  exact hc

/-- Read-only traversal with early exit. Fuel bounds the number of nodes visited;
completeness additionally requires the represented chain length to fit in fuel. -/
def any (b : BucketBuffer w) (test : Word w × Word w → RAM w Bool) :
    Nat → Word w → RAM w Bool
  | 0, h => do
    let zero ← lit 0
    let _ ← eq h zero
    pure false
  | fuel+1, h => do
    let node ← next b h
    match node with
    | none => pure false
    | some (v,n) => do
      let hit ← test v
      if hit then pure true else any b test fuel n

theorem state_any (b : BucketBuffer w) (test : Word w × Word w → RAM w Bool)
    (ht : ∀ v σ, (test v).state σ = σ) (fuel : Nat) (h : Word w) (σ : RamState w) :
    (any b test fuel h).state σ = σ := by
  induction fuel generalizing h with
  | zero => simp [any]
  | succ fuel ih =>
    simp only [any, RAM.state_bind, state_next]
    split <;> simp only [RAM.state_pure, RAM.state_bind, ht]
    split <;> simp [ih]

theorem steps_any_le (b : BucketBuffer w) (test : Word w × Word w → RAM w Bool)
    (bound : Nat) (ht : ∀ v σ, RAM.steps CostModel.unitCost (test v) σ ≤ bound)
    (fuel : Nat) (h : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (any b test fuel h) σ ≤ 2+fuel*(10+bound) := by
  induction fuel generalizing h σ with
  | zero => simp [any]
  | succ fuel ih =>
    simp only [any, RAM.steps_bind, Nat.succ_mul, Nat.mul_add]
    have hn := steps_next_le b h σ
    split
    · simp only [RAM.steps_pure]; omega
    · rename_i node v n heq
      simp only [RAM.steps_bind]
      have hc := ht v ((next b h).state σ)
      split
      · simp only [RAM.steps_pure]; omega
      · have hc' := ih n ((test v).state ((next b h).state σ))
        simp only [Nat.mul_add] at hc'
        omega

/-- Every finite represented chain is traversed faithfully when fuel covers it. -/
theorem any_spec {σ : RamState w} {b : BucketBuffer w} {rs : List (Nat × Nat)} {ns hs : List Nat}
    (H : Holds σ b rs ns hs) (test : Word w × Word w → RAM w Bool) (pred : Nat × Nat → Bool)
    (ht : ∀ v i (hi : i < rs.length), i < b.used.toNat →
      (v.1.toNat,v.2.toNat) = rs[i] → (test v).val σ = pred rs[i])
    (hstate : ∀ v σ, (test v).state σ = σ) (hw : 1 < 2^w)
    {h : Nat} {xs : List (Nat × Nat)} (HC : Chain rs ns b.used.toNat h xs)
    {pointer : Word w} (hp : pointer.toNat = h) (fuel : Nat) (hf : xs.length ≤ fuel) :
    (any b test fuel pointer).val σ = xs.any pred := by
  induction HC generalizing pointer fuel with
  | nil =>
    cases fuel with
    | zero => simp [any]
    | succ f => simp [any, next, hp]
  | @cons h tail positive occupied hr hn rest ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      obtain ⟨v,n,hv,ha,hb,hc⟩ := next_spec H (by omega : 0 < pointer.toNat) (by omega) hw
      have hc' : n.toNat = ns[h-1] := by simpa [hp] using hc
      have ht' : (test v).val σ = pred rs[h-1] := by
        apply ht v (h-1) hr (by omega)
        simp only [hp] at ha hb
        exact Prod.ext ha hb
      simp only [any, RAM.val_bind, hv, state_next, hstate, ht', List.any_cons]
      by_cases hit : pred rs[h-1] = true
      · simp [hit]
      · simp [hit, ih hc' f (by simpa using (show tail.length ≤ f by simpa using hf))]

/-- A logical list of buckets, backed by finite chains in the physical pool.
`Holds` alone allows arbitrary bounded links; `Models` also rules out cycles. -/
def Models (σ : RamState w) (b : BucketBuffer w) (buckets : List (List (Nat × Nat))) : Prop :=
  ∃ rs ns hs, Holds σ b rs ns hs ∧ buckets.length = hs.length ∧
    ∀ i (hi : i < hs.length) (hib : i < buckets.length), Chain rs ns b.used.toNat hs[i] buckets[i]

theorem allocate_models (σ : RamState w) (m p : Word w)
    (hf : σ.size < 2^w) (hi : σ.size+3*m.toNat < 2^w)
    (hs : σ.size+3*m.toNat+p.toNat ≤ 2^w) :
    Models ((allocate m p).state σ) ((allocate m p).val σ) (List.replicate p.toNat []) := by
  refine ⟨List.replicate m.toNat (0,0), List.replicate m.toNat 0, List.replicate p.toNat 0,
    allocate_spec σ m p hf hi hs, by simp, ?_⟩
  intro i hi hib; simp only [List.getElem_replicate]; exact Chain.nil

/-- Successful insertion prepends exactly one record to its selected logical
bucket and preserves every other bucket's sequence, without changing capacity. -/
theorem push_models {σ : RamState w} {b : BucketBuffer w} {buckets : List (List (Nat × Nat))}
    (HM : Models σ b buckets) {key : Word w} (hk : key.toNat < buckets.length)
    (hu : b.used.toNat < b.capacity.toNat) (v : Word w × Word w) (hw : 1 < 2^w) :
    ∃ b', (push b key v).val σ = some b' ∧
      Models ((push b key v).state σ) b' (buckets.set key.toNat ((v.1.toNat,v.2.toNat)::buckets[key.toNat])) := by
  rcases HM with ⟨rs,ns,hs,H,hlen,HC⟩
  have hk' : key.toNat < hs.length := by omega
  have hu' : b.used.toNat < rs.length := by rw [← RecordBuffer.capacity_eq H.records]; exact hu
  obtain ⟨b',hb',hbused,H'⟩ := push_spec H hk' hu' v hw
  refine ⟨b',hb', rs.set b.used.toNat (v.1.toNat,v.2.toNat),
    ns.set b.used.toNat hs[key.toNat], hs.set key.toNat (b.used.toNat+1), H', by simpa using hlen, ?_⟩
  intro i hi hib
  have hi' : i < hs.length := by simpa using hi
  have chain := HC i hi' (by simp only [List.length_set] at hib; exact hib)
  rw [hbused]
  by_cases he : key.toNat = i
  · subst i
    simp only [List.getElem_set_self]
    exact chain.prepend hu' (by rw [H.lengths]; exact hu') (v.1.toNat,v.2.toNat)
  · simp only [List.getElem_set_ne he hi, List.getElem_set_ne he hib]
    exact chain.setFresh (v.1.toNat,v.2.toNat) hs[key.toNat]

end BucketBuffer
end Arlib.Computation
