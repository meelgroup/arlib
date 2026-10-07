/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.RAMRoster

/-!
# Bounded integer-key direct-address dictionaries

Separate, disjoint buffers store occupancy flags and values. The key universe
capacity determines reserved space; it is independent of the live dictionary
cardinality. Every access is certified only for a key below that capacity.
Initialization allocates/zeros both buffers and is charged per cell.
-/
namespace Arlib.Computation
private structure RAMDictRep (w : ℕ) where
  keys : RAMRoster w
  values : Buffer w

def RAMDict (w : ℕ) := RAMDictRep w
namespace RAMDict
variable {w : ℕ}

def ofBuffers (keys : RAMRoster w) (values : Buffer w) : RAMDict w := ⟨keys, values⟩
private def keys (d : RAMDict w) := RAMDictRep.keys d
private def values (d : RAMDict w) := RAMDictRep.values d
noncomputable def capacityNat (d : RAMDict w) := RAMRoster.capacityNat (keys d)

/-- Exact occupancy/count metadata, represented values at every present key,
and separation of the mutable occupancy and value regions. -/
structure Holds (σ : RamState w) (r : RAMDict w) (d : Dict ℕ ℕ)
    (flags vals : List ℕ) : Prop where
  key_rep : RAMRoster.Holds σ (keys r) (Roster.ofFinset d.keys) flags
  value_rep : Buffer.Holds σ (values r) vals
  lengths : flags.length = vals.length
  lookup : ∀ k (hk : k < vals.length) v, d.lookup k = some v → vals[k] = v
  disjoint : Disjoint (block (RAMRoster.storage (keys r)).baseNat flags.length)
    (block (values r).baseNat vals.length)

def Rep (σ : RamState w) (r : RAMDict w) (d : Dict ℕ ℕ) : Prop :=
  ∃ flags vals, Holds σ r d flags vals

/-- Lookup first tests the charged flag, then reads the separate value slot. -/
def find (r : RAMDict w) (key : Word w) : RAM w (Option (Word w)) := do
  let present ← RAMRoster.mem (keys r) key
  if present then do
    let value ← Buffer.read (values r) key
    pure (some value)
  else pure none

@[simp] theorem state_find (r : RAMDict w) (key : Word w) (σ : RamState w) :
    (find r key).state σ = σ := by
  simp only [find, RAM.state_bind, RAMRoster.state_mem]
  split <;> simp

theorem steps_find_le (r : RAMDict w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (find r key) σ ≤ 6 := by
  simp only [find, RAM.steps_bind, RAMRoster.steps_mem, RAMRoster.state_mem]
  split <;> simp

def insert (r : RAMDict w) (key value : Word w) : RAM w (RAMDict w) := do
  let next ← RAMRoster.insert (keys r) key
  let _ ← Buffer.write (values r) key value
  pure (ofBuffers next (values r))

def erase (r : RAMDict w) (key : Word w) : RAM w (RAMDict w) := do
  let next ← RAMRoster.erase (keys r) key
  pure (ofBuffers next (values r))

def size (r : RAMDict w) : RAM w (Word w) := RAMRoster.size (keys r)
def cardEq (r : RAMDict w) (n : Word w) : RAM w Bool := RAMRoster.cardEq (keys r) n

theorem steps_insert_le (r : RAMDict w) (key value : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (insert r key value) σ ≤ 10 := by
  simp only [insert, RAM.steps_bind, Buffer.steps_write, CostModel.unitCost_cost,
    RAM.steps_pure]
  have h := RAMRoster.steps_insert_le (keys r) key σ
  omega

theorem steps_erase_le (r : RAMDict w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (erase r key) σ ≤ 9 := by
  simp only [erase, RAM.steps_bind, RAM.steps_pure, Nat.add_zero]
  exact RAMRoster.steps_erase_le (keys r) key σ

@[simp] theorem steps_size (r : RAMDict w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (size r) σ = 0 := by simp [size]
@[simp] theorem steps_cardEq (r : RAMDict w) (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (cardEq r n) σ = 1 := by simp [cardEq]

theorem find_spec {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {flags vals : List ℕ}
    (H : Holds σ r d flags vals) (key : Word w) (hk : key.toNat < flags.length) :
    ((find r key).val σ).map Word.toNat = d.lookup key.toNat := by
  have hmem := RAMRoster.mem_spec H.key_rep key hk
  simp only [Roster.toFinset_ofFinset] at hmem
  have hkvals : key.toNat < vals.length := by rw [← H.lengths]; exact hk
  by_cases hm : key.toNat ∈ d.keys
  · have hex : (d.lookup key.toNat).isSome = true := by
      rw [Dict.lookup_isSome]; simpa using hm
    cases hlookup : d.lookup key.toNat with
    | none => simp [hlookup] at hex
    | some value =>
      have hv := H.lookup key.toNat hkvals value hlookup
      simp only [find, RAM.val_bind, hmem, hm, decide_true, if_true,
        RAMRoster.state_mem, Buffer.state_read, RAM.val_pure, Option.map_some]
      rw [Buffer.read_spec H.value_rep hkvals, hv]
  · have hn := (Dict.lookup_eq_none_iff_not_mem_keys d key.toNat).mpr hm
    simp [find, hmem, hm, hn]

/-- Insert replaces an existing value or adds a new key, maintaining separate
occupancy/value representations and exact live-size metadata. -/
theorem insert_spec {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {flags vals : List ℕ}
    (H : Holds σ r d flags vals) (key value : Word w) (hk : key.toNat < flags.length) :
    Rep ((insert r key value).state σ) ((insert r key value).val σ)
      ((Dict.insert key.toNat value.toNat d : Charged StdOp Cell (Dict ℕ ℕ)).val) := by
  let d' := (Dict.insert key.toNat value.toNat d : Charged StdOp Cell (Dict ℕ ℕ)).val
  let σ₁ := (RAMRoster.insert (keys r) key).state σ
  let k₁ := (RAMRoster.insert (keys r) key).val σ
  have hkvals : key.toNat < vals.length := by rw [← H.lengths]; exact hk
  rcases RAMRoster.insert_spec H.key_rep key hk with ⟨newflags, HK⟩
  have HK' : RAMRoster.Holds σ₁ k₁ (Roster.ofFinset d'.keys) newflags := by
    apply RAMRoster.holds_congr HK
    simp [d', Dict.keys_insert]
  have HV : Buffer.Holds σ₁ (values r) vals :=
    RAMRoster.insert_frame H.key_rep H.value_rep key hk H.disjoint.symm
  have hflaglen : newflags.length = flags.length := by
    have heq := HK'.storage.length_eq
    change (RAMRoster.storage k₁).lengthNat = newflags.length at heq
    rw [RAMRoster.storage_insert] at heq
    exact heq.symm.trans H.key_rep.storage.length_eq
  have hd : Disjoint (block (RAMRoster.storage k₁).baseNat newflags.length)
      (block (values r).baseNat vals.length) := by
    rw [RAMRoster.storage_insert, hflaglen]
    exact H.disjoint
  have HK'' := RAMRoster.frame_write HK' HV key value hkvals hd
  have HV' := Buffer.write_spec HV hkvals value
  have hstate : (insert r key value).state σ = (Buffer.write (values r) key value).state σ₁ := by
    simp only [insert, RAM.state_bind, RAM.state_pure]
    rfl
  have hval : (insert r key value).val σ = ofBuffers k₁ (values r) := by
    simp only [insert, RAM.val_bind, RAM.val_pure]
    rfl
  rw [hstate, hval]
  refine ⟨newflags, vals.set key.toNat value.toNat, HK'', HV', ?_, ?_, ?_⟩
  · simpa only [List.length_set] using hflaglen.trans H.lengths
  · intro i hi v hlookup
    have hi' : i < vals.length := by simpa using hi
    change d'.lookup i = some v at hlookup
    simp only [d', Dict.lookup_insert] at hlookup
    by_cases heq : i = key.toNat
    · subst i
      simp at hlookup
      simp [hlookup]
    · simp only [if_neg heq] at hlookup
      rw [List.getElem_set_ne (Ne.symm heq)]
      exact H.lookup i hi' v hlookup
  · simpa only [List.length_set, ofBuffers, keys, values] using hd

/-- Erasure updates occupancy and live count while leaving stale value slots
unobservable through dictionary lookup. -/
theorem erase_spec {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {flags vals : List ℕ}
    (H : Holds σ r d flags vals) (key : Word w) (hk : key.toNat < flags.length) :
    Rep ((erase r key).state σ) ((erase r key).val σ)
      ((Dict.erase key.toNat d : Charged StdOp Cell (Dict ℕ ℕ)).val) := by
  let d' := (Dict.erase key.toNat d : Charged StdOp Cell (Dict ℕ ℕ)).val
  let σ₁ := (RAMRoster.erase (keys r) key).state σ
  let k₁ := (RAMRoster.erase (keys r) key).val σ
  rcases RAMRoster.erase_spec H.key_rep key hk with ⟨newflags, HK⟩
  have HK' : RAMRoster.Holds σ₁ k₁ (Roster.ofFinset d'.keys) newflags := by
    apply RAMRoster.holds_congr HK
    simp [d', Dict.keys_erase]
  have HV : Buffer.Holds σ₁ (values r) vals :=
    RAMRoster.erase_frame H.key_rep H.value_rep key hk H.disjoint.symm
  have hflaglen : newflags.length = flags.length := by
    have heq := HK'.storage.length_eq
    change (RAMRoster.storage k₁).lengthNat = newflags.length at heq
    rw [RAMRoster.storage_erase] at heq
    exact heq.symm.trans H.key_rep.storage.length_eq
  have hd : Disjoint (block (RAMRoster.storage k₁).baseNat newflags.length)
      (block (values r).baseNat vals.length) := by
    rw [RAMRoster.storage_erase, hflaglen]
    exact H.disjoint
  have hstate : (erase r key).state σ = σ₁ := by
    simp only [erase, RAM.state_bind, RAM.state_pure]
    rfl
  have hval : (erase r key).val σ = ofBuffers k₁ (values r) := by
    simp only [erase, RAM.val_bind, RAM.val_pure]
    rfl
  rw [hstate, hval]
  refine ⟨newflags, vals, HK', HV, hflaglen.trans H.lengths, ?_, hd⟩
  intro i hi v hlookup
  change d'.lookup i = some v at hlookup
  simp only [d', Dict.lookup_erase] at hlookup
  by_cases heq : i = key.toNat
  · simp [heq] at hlookup
  · simp only [if_neg heq] at hlookup
    exact H.lookup i hi v hlookup

/-- Stored live size agrees with the existing abstract dictionary cardinality. -/
theorem size_spec {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {flags vals : List ℕ}
    (H : Holds σ r d flags vals) : ((size r).val σ).toNat = d.card := by
  rw [size, RAMRoster.size_spec H.key_rep, ← Roster.card_toFinset,
    Roster.toFinset_ofFinset, Dict.card_keys]

theorem cardEq_spec {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {flags vals : List ℕ}
    (H : Holds σ r d flags vals) (n : Word w) :
    (cardEq r n).val σ = decide (d.card = n.toNat) := by
  rw [cardEq, RAMRoster.cardEq_spec H.key_rep, ← Roster.card_toFinset,
    Roster.toFinset_ofFinset, Dict.card_keys]

theorem realizes_find (d : Dict ℕ ℕ) (r : RAMDict w) (key : Word w) :
    Realizes (Dict.find key.toNat d : Charged StdOp Cell (Option ℕ)) (find r key)
      (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat)
      (fun a b _ => a = b.map Word.toNat) 6 where
  correct := by
    intro σ h
    rcases h.1 with ⟨fs, vs, H⟩
    have hk : key.toNat < fs.length := by
      simpa only [capacityNat, RAMRoster.capacityNat, H.key_rep.storage.length_eq] using h.2
    rw [Dict.val_find, ← find_spec H key hk]
  steps_le := by intro σ _; exact steps_find_le r key σ

theorem realizes_insert (d : Dict ℕ ℕ) (r : RAMDict w) (key value : Word w) :
    Realizes (Dict.insert key.toNat value.toNat d : Charged StdOp Cell (Dict ℕ ℕ))
      (insert r key value) (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat)
      (fun a b σ => Rep σ b a) 10 where
  correct := by
    intro σ h
    rcases h.1 with ⟨fs, vs, H⟩
    apply insert_spec H key value
    simpa only [capacityNat, RAMRoster.capacityNat, H.key_rep.storage.length_eq] using h.2
  steps_le := by intro σ _; exact steps_insert_le r key value σ

theorem realizes_erase (d : Dict ℕ ℕ) (r : RAMDict w) (key : Word w) :
    Realizes (Dict.erase key.toNat d : Charged StdOp Cell (Dict ℕ ℕ)) (erase r key)
      (fun σ => Rep σ r d ∧ key.toNat < r.capacityNat) (fun a b σ => Rep σ b a) 9 where
  correct := by
    intro σ h
    rcases h.1 with ⟨fs, vs, H⟩
    apply erase_spec H key
    simpa only [capacityNat, RAMRoster.capacityNat, H.key_rep.storage.length_eq] using h.2
  steps_le := by intro σ _; exact steps_erase_le r key σ

theorem realizes_size (d : Dict ℕ ℕ) (r : RAMDict w) :
    Realizes (Dict.size d : Charged StdOp Cell ℕ) (size r)
      (fun σ => Rep σ r d) (fun a b _ => a = b.toNat) 0 where
  correct := by intro σ h; rcases h with ⟨fs, vs, H⟩; rw [Dict.val_size, ← size_spec H]
  steps_le := by intro σ _; simp

theorem realizes_cardEq (d : Dict ℕ ℕ) (r : RAMDict w) (n : Word w) :
    Realizes (Dict.cardEq n.toNat d : Charged StdOp Cell Bool) (cardEq r n)
      (fun σ => Rep σ r d) (fun a b _ => a = b) 1 where
  correct := by intro σ h; rcases h with ⟨fs, vs, H⟩; rw [Dict.val_cardEq, cardEq_spec H n]
  steps_le := by intro σ _; simp

/-- Updates preserve a third buffer when it is disjoint from both dictionary
regions. This states ownership requirements explicitly. -/
theorem insert_frame {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {fs vs zs : List ℕ}
    (H : Holds σ r d fs vs) {b : Buffer w} (HB : Buffer.Holds σ b zs)
    (key value : Word w) (hk : key.toNat < fs.length)
    (hflags : Disjoint (block b.baseNat zs.length)
      (block (RAMRoster.storage (keys r)).baseNat fs.length))
    (hvalues : Disjoint (block b.baseNat zs.length) (block (values r).baseNat vs.length)) :
    Buffer.Holds ((insert r key value).state σ) b zs := by
  have HB' := RAMRoster.insert_frame H.key_rep HB key hk hflags
  have HV' := RAMRoster.insert_frame H.key_rep H.value_rep key hk H.disjoint.symm
  have hkvs : key.toNat < vs.length := by rw [← H.lengths]; exact hk
  have h := Buffer.write_frame HV' HB' hkvs value hvalues
  simpa only [insert, RAM.state_bind, RAM.state_pure] using h

theorem erase_frame {σ : RamState w} {r : RAMDict w} {d : Dict ℕ ℕ} {fs vs zs : List ℕ}
    (H : Holds σ r d fs vs) {b : Buffer w} (HB : Buffer.Holds σ b zs)
    (key : Word w) (hk : key.toNat < fs.length)
    (hflags : Disjoint (block b.baseNat zs.length)
      (block (RAMRoster.storage (keys r)).baseNat fs.length)) :
    Buffer.Holds ((erase r key).state σ) b zs := by
  have h := RAMRoster.erase_frame H.key_rep HB key hk hflags
  simpa only [erase, RAM.state_bind, RAM.state_pure] using h

/-- Allocate separate zeroed occupancy and value buffers. -/
def allocate (n : Word w) : RAM w (RAMDict w) := do
  let k ← RAMRoster.allocate n
  let v ← Buffer.allocate n
  pure (ofBuffers k v)

@[simp] theorem steps_allocate (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate n) σ = 2 * n.toNat + 1 := by
  simp [allocate, Buffer.allocate]
  omega

/-- Nonvacuous construction of an empty dictionary, with actual charged
capacity-wide initialization and separated storage regions. -/
theorem allocate_spec (σ : RamState w) (n : Word w)
    (hfrontier : σ.size < 2 ^ w) (hspace : σ.size + 2 * n.toNat ≤ 2 ^ w) :
    Rep ((allocate n).state σ) ((allocate n).val σ) (Dict.empty : Dict ℕ ℕ) := by
  let σ₁ := (RAMRoster.allocate n).state σ
  let k₁ := (RAMRoster.allocate n).val σ
  let v₁ := (Buffer.allocate n).val σ₁
  have hsize : σ₁.size = σ.size + n.toNat := by
    simp [σ₁, RAMRoster.allocate, Buffer.allocate]
  have hspace₁ : σ.size + n.toNat ≤ 2 ^ w := by omega
  have hfrontier₁ : σ₁.size < 2 ^ w := by rw [hsize]; omega
  have hspace₂ : σ₁.size + n.toNat ≤ 2 ^ w := by rw [hsize]; omega
  rcases RAMRoster.allocate_spec σ n hfrontier hspace₁ with ⟨fs, HK⟩
  have HK' := RAMRoster.allocate_buffer_frame HK n hspace₂
  have HK'' : RAMRoster.Holds ((Buffer.allocate n).state σ₁) k₁
      (Roster.ofFinset (Dict.empty : Dict ℕ ℕ).keys) fs := by
    apply RAMRoster.holds_congr HK'
    simp
  have HV := Buffer.allocate_spec σ₁ n hfrontier₁ hspace₂
  have hflen : fs.length = n.toNat := by
    have heq := HK.storage.length_eq
    have hn : (RAMRoster.storage k₁).lengthNat = n.toNat := rfl
    change (RAMRoster.storage k₁).lengthNat = fs.length at heq
    exact heq.symm.trans hn
  have hbflags : (RAMRoster.storage k₁).baseNat = σ.size := by
    change ((Buffer.allocate n).val σ).baseNat = σ.size
    exact toNat_val_alloc σ n hfrontier
  have hbvalues : v₁.baseNat = σ₁.size := toNat_val_alloc σ₁ n hfrontier₁
  have hs : (allocate n).state σ = (Buffer.allocate n).state σ₁ := by
    simp only [allocate, RAM.state_bind, RAM.state_pure]
    rfl
  have hv : (allocate n).val σ = ofBuffers k₁ v₁ := by
    simp only [allocate, RAM.val_bind, RAM.val_pure]
    rfl
  rw [hs, hv]
  refine ⟨fs, List.replicate n.toNat 0, HK'', HV, ?_, ?_, ?_⟩
  · simpa using hflen
  · intro i hi v hlookup
    simp at hlookup
  · change Disjoint (block (RAMRoster.storage k₁).baseNat fs.length)
      (block v₁.baseNat (List.replicate n.toNat 0).length)
    rw [hbflags, hbvalues, hflen, hsize, List.length_replicate]
    exact disjoint_block (le_refl _)

/-- Both dictionary regions remain reserved across updates. -/
@[simp] theorem size_state_insert (r : RAMDict w) (key value : Word w) (σ : RamState w) :
    ((insert r key value).state σ).size = σ.size := by simp [insert]

@[simp] theorem size_state_erase (r : RAMDict w) (key : Word w) (σ : RamState w) :
    ((erase r key).state σ).size = σ.size := by simp [erase]

@[simp] theorem size_state_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).state σ).size = σ.size + 2 * n.toNat := by
  simp [allocate, Buffer.allocate]
  omega

end RAMDict
end Arlib.Computation
