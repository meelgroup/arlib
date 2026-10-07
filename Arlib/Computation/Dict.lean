/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

/-!
# A sealed finite map, whose operations charge

A `Dict ι α` is a finite map from `ι` to `α` that a program can touch only
through a charged operation.  It holds a private list of entries with
duplicate-free keys; the lookup function, the key set and the cardinality are
`noncomputable`, so `d.lookup k` is specification vocabulary and `Dict.find k d`
is the program.

`find`, `insert`, `erase`, `size` and `cardEq` each charge one operation, under
the opcode the development's `DictOps` instance names.  A caller computes the
value it inserts and pays for that computation in the monad on the way; `insert`
charges for the store.

There is no `modify`: a program that changes the value at a key does `find` then
`insert`, and pays for both.  There is no membership test either — `find` returns
the value, and testing an `Option` costs nothing once the lookup is paid for.

An entry occupies one cell of the kind `DictCells` names, whatever the value is.
A development whose values are themselves large names a kind whose cell means
"one entry of this table" and prices it in its space model.

Keys without values belong in `Arlib.Computation.Roster ι`.

## Main definitions

* `Dict ι α` — a sealed finite map.
* `Dict.lookup`, `Dict.keys`, `Dict.card` — the specification view; noncomputable.
* `Dict.ofFinset` — the map with a given domain; noncomputable.
* `DictOp`, `DictOps` — the standard operations, and what a development's
  currency calls each of them.
* `DictCells` — the kind of cell one entry occupies.
* `Dict.empty`, `Dict.find`, `Dict.insert`, `Dict.erase`, `Dict.size`,
  `Dict.cardEq` — the operations, one charge each.
* `Dict.occupancy` — the measure an `ExactNet` obligation is stated against.
-/

namespace Arlib.Computation

universe u

/-- A finite map from `ι` to `α` that a program can touch only through a charged
operation.

The entries are a list rather than a `Finsupp` so that they can be iterated.  The
constructor, the list and the invariant are `private`, so outside this module the
only way to obtain a `Dict` is `empty` together with the operations below. -/
structure Dict (ι : Type u) (α : Type u) where
  private mk ::
  private entries : List (ι × α)
  private nodupKeys : (entries.map Prod.fst).Nodup

/-- The standard dictionary operations.  Each of the operations below charges
exactly one of these, and takes no opcode parameter. -/
inductive DictOp
  /-- Retrieve the value stored at a key, if any. -/
  | find
  /-- Store a value at a key, replacing whatever was there. -/
  | insert
  /-- Remove a key and its value. -/
  | erase
  /-- Ask how many entries are held. -/
  | size
  /-- Compare the number of entries held against a number. -/
  | cardEq
  deriving DecidableEq, Repr, Inhabited

instance : Fintype DictOp where
  elems := {.find, .insert, .erase, .size, .cardEq}
  complete := fun x => by cases x <;> decide

/-- Which opcode of a development's currency `κ` names each standard dictionary
operation.  A name, not an amount: the amount is one charge per call, fixed by
the operations below.  `charge_injective` keeps distinct operations under
distinct names, and is discharged by `decide`. -/
class DictOps (κ : Type) where
  /-- The development's opcode for a standard dictionary operation. -/
  charge : DictOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The kind of storage cell one entry of a `Dict ι α` occupies.

One instance per key/value pair of types per development.  The kind comes from
the data rather than from a parameter at each operation. -/
class DictCells (ι : Type u) (α : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one entry of a `Dict ι α` occupies. -/
  cell : κₛ

namespace Dict

variable {κ κₛ ι α : Type} [DecidableEq κ] [DecidableEq κₛ] [DecidableEq ι]

/-- The kind of cell an entry of a `Dict ι α` occupies. -/
abbrev cell (ι α : Type) [DictCells ι α κₛ] : κₛ := DictCells.cell ι α

/-- The opcode a standard dictionary operation charges in the currency `κ`. -/
abbrev opcode (κ : Type) [DictOps κ] (o : DictOp) : κ := DictOps.charge o

/-! ## The list underneath

The two functions the operations are built from, and their laws.  Both are
`private`: they are the representation. -/

/-- INTERNAL: the value stored at a key, in an entry list. -/
private def findEntry (k : ι) : List (ι × α) → Option α
  | [] => none
  | p :: l => if p.1 = k then some p.2 else findEntry k l

/-- INTERNAL: drop every entry at a key. -/
private def eraseKey (k : ι) : List (ι × α) → List (ι × α)
  | [] => []
  | p :: l => if p.1 = k then eraseKey k l else p :: eraseKey k l

private theorem mem_keys_eraseKey (k x : ι) :
    ∀ l : List (ι × α), x ∈ (eraseKey k l).map Prod.fst ↔ x ≠ k ∧ x ∈ l.map Prod.fst := by
  intro l
  induction l with
  | nil => simp [eraseKey]
  | cons p l ih =>
      by_cases hp : p.1 = k
      · rw [eraseKey, if_pos hp]
        simp only [ih, List.map_cons, List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact absurd (h2.trans hp) h1
          · exact ⟨h1, h2⟩
      · rw [eraseKey, if_neg hp]
        simp only [List.map_cons, List.mem_cons, ih]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact ⟨by rintro rfl; exact hp h.symm, Or.inl h⟩
          · exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h2⟩

private theorem nodup_eraseKey (k : ι) :
    ∀ {l : List (ι × α)}, (l.map Prod.fst).Nodup → ((eraseKey k l).map Prod.fst).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp [eraseKey]
  | cons p l ih =>
      intro h
      rw [List.map_cons, List.nodup_cons] at h
      by_cases hp : p.1 = k
      · rw [eraseKey, if_pos hp]; exact ih h.2
      · rw [eraseKey, if_neg hp, List.map_cons, List.nodup_cons]
        exact ⟨fun hmem => h.1 ((mem_keys_eraseKey k p.1 l).1 hmem).2, ih h.2⟩

private theorem findEntry_eraseKey (k k' : ι) :
    ∀ l : List (ι × α), findEntry k' (eraseKey k l) = if k' = k then none else findEntry k' l := by
  intro l
  induction l with
  | nil => simp [eraseKey, findEntry]
  | cons p l ih =>
      by_cases hk : k' = k
      · subst hk
        simp only at ih ⊢
        by_cases hp : p.1 = k'
        · rw [eraseKey, if_pos hp]; exact ih
        · rw [eraseKey, if_neg hp]
          simp only [findEntry, if_neg hp]
          exact ih
      · simp only [if_neg hk] at ih ⊢
        by_cases hp : p.1 = k
        · rw [eraseKey, if_pos hp, ih]
          simp only [findEntry, if_neg (show ¬ p.1 = k' from by rintro rfl; exact hk hp)]
        · rw [eraseKey, if_neg hp]
          simp only [findEntry, ih]

private theorem length_eraseKey_le (k : ι) :
    ∀ l : List (ι × α), (eraseKey k l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [eraseKey]
  | cons p l ih =>
      by_cases hp : p.1 = k
      · rw [eraseKey, if_pos hp]; simpa using Nat.le_succ_of_le ih
      · rw [eraseKey, if_neg hp]; simpa using ih

/-! ## The specification view

Every declaration in this section is `noncomputable`, and so cannot appear in a
program. -/

/-- The value a dictionary stores at a key.  **Specification-only**; the program
form is `find`. -/
noncomputable def lookup (d : Dict ι α) (k : ι) : Option α := findEntry k d.entries

/-- The keys a dictionary holds.  **Specification-only.** -/
noncomputable def keys (d : Dict ι α) : Finset ι := (d.entries.map Prod.fst).toFinset

/-- How many entries a dictionary holds.  **Specification-only**; the program
forms are `size` and `cardEq`. -/
noncomputable def card (d : Dict ι α) : ℕ := d.entries.length

/-- The dictionary with a given domain, storing `f` at each key.
**Specification-only.** -/
noncomputable def ofFinset (s : Finset ι) (f : ι → α) : Dict ι α :=
  ⟨s.toList.map (fun k => (k, f k)), by
    simpa [List.map_map, Function.comp_def] using s.nodup_toList⟩

omit [DecidableEq κ] [DecidableEq κₛ] in
@[simp] theorem keys_ofFinset (s : Finset ι) (f : ι → α) : (ofFinset s f).keys = s := by
  ext y
  simp [keys, ofFinset, List.map_map, Function.comp_def]

omit [DecidableEq κ] [DecidableEq κₛ] in
/-- The cardinality view agrees with the key set. -/
@[simp] theorem card_keys (d : Dict ι α) : d.keys.card = d.card := by
  simpa [keys, card] using List.toFinset_card_of_nodup d.nodupKeys

private theorem findEntry_isSome (k : ι) :
    ∀ l : List (ι × α), (findEntry k l).isSome = decide (k ∈ l.map Prod.fst) := by
  intro l
  induction l with
  | nil => simp [findEntry]
  | cons p l ih =>
      by_cases hk : p.1 = k
      · simp [findEntry, hk]
      · have hne : k ≠ p.1 := Ne.symm hk
        simp [findEntry, hk, hne, ih]

omit [DecidableEq κ] [DecidableEq κₛ] in
/-- Membership in the dictionary's key set is exactly successful lookup. -/
theorem lookup_isSome (d : Dict ι α) (k : ι) :
    (d.lookup k).isSome = decide (k ∈ d.keys) := by
  change (findEntry k d.entries).isSome = decide (k ∈ (d.entries.map Prod.fst).toFinset)
  rw [findEntry_isSome]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.decide_iff, List.mem_toFinset]

omit [DecidableEq κ] [DecidableEq κₛ] in
/-- A missing lookup is precisely a key outside the dictionary domain. -/
theorem lookup_eq_none_iff_not_mem_keys (d : Dict ι α) (k : ι) :
    d.lookup k = none ↔ k ∉ d.keys := by
  have h := lookup_isSome d k
  cases hl : d.lookup k <;> simp [hl] at h ⊢ <;> simp_all

/-! ## What a dictionary occupies

**A dictionary occupies one cell of the storage kind it is given, per entry, and
nothing of any other kind.**  The `space_*` theorems below follow from this and
from what each operation does to the entry list. -/

private def slots (k : κₛ) (d : Dict ι α) : Residency κₛ :=
  Residency.ofFun fun k' => if k' = k then d.entries.length else 0

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem at'_slots_self (k : κₛ) (d : Dict ι α) : (slots k d).at' k = d.card := by
  simp [slots, card]

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem at'_slots_of_ne {k k' : κₛ} (h : k' ≠ k) (d : Dict ι α) :
    (slots k d).at' k' = 0 := by simp [slots, h]

/-- The measure a `Charged.ExactNet` obligation about a dictionary is stated
against. -/
def occupancy (k : κₛ) : Dict ι α → Residency κₛ := slots k

omit [DecidableEq κ] [DecidableEq ι] in
@[simp] theorem occupancy_eq (k : κₛ) (d : Dict ι α) : occupancy k d = slots k d := rfl

omit [DecidableEq ι] in
/-- An update's net is the change in the number of entries. -/
theorem space_net_update (o : κ) (k : κₛ) (f : Dict ι α → Dict ι α) (d : Dict ι α) :
    (Charged.opUpdate o (slots k) f d).space.net k = ((f d).card : ℤ) - (d.card : ℤ) := by
  simp

omit [DecidableEq ι] in
/-- An update's peak is its growth, or nothing if it shrank. -/
theorem space_peak_update (o : κ) (k : κₛ) (f : Dict ι α → Dict ι α) (d : Dict ι α) :
    (Charged.opUpdate o (slots k) f d).space.peak k
      = max 0 (((f d).card : ℤ) - (d.card : ℤ)) := by
  simp

omit [DecidableEq ι] in
@[simp] theorem space_net_update_of_ne (o : κ) {k k' : κₛ} (h : k' ≠ k)
    (f : Dict ι α → Dict ι α) (d : Dict ι α) :
    (Charged.opUpdate o (slots k) f d).space.net k' = 0 := by
  simp [at'_slots_of_ne h]

omit [DecidableEq ι] in
@[simp] theorem space_peak_update_of_ne (o : κ) {k k' : κₛ} (h : k' ≠ k)
    (f : Dict ι α → Dict ι α) (d : Dict ι α) :
    (Charged.opUpdate o (slots k) f d).space.peak k' = 0 := by
  simp [at'_slots_of_ne h]

/-! ## The operations -/

/-- The empty dictionary.  It holds nothing and charges nothing. -/
def empty : Dict ι α := ⟨[], by simp⟩

omit [DecidableEq κ] [DecidableEq κₛ] in
@[simp] theorem keys_empty : (empty : Dict ι α).keys = ∅ := rfl

omit [DecidableEq κ] [DecidableEq κₛ] [DecidableEq ι] in
@[simp] theorem card_empty : (empty : Dict ι α).card = 0 := rfl

omit [DecidableEq κ] [DecidableEq κₛ] in
@[simp] theorem lookup_empty (k : ι) : (empty : Dict ι α).lookup k = none := rfl

variable [DictOps κ]

/-- Retrieve the value stored at a key, at the price of one `DictOp.find`. -/
def find (k : ι) (d : Dict ι α) : Charged κ κₛ (Option α) :=
  Charged.op (opcode κ .find) (findEntry k d.entries)

omit [DecidableEq κₛ] in
@[simp] theorem val_find (k : ι) (d : Dict ι α) :
    (find k d : Charged κ κₛ (Option α)).val = d.lookup k := rfl

omit [DecidableEq κₛ] in
@[simp] theorem cost_find (k : ι) (d : Dict ι α) :
    (find k d : Charged κ κₛ (Option α)).cost = CostVec.one (opcode κ .find) := rfl

omit [DecidableEq κₛ] in
/-- A lookup holds nothing. -/
@[simp] theorem space_find (k : ι) (d : Dict ι α) :
    (find k d : Charged κ κₛ (Option α)).space = 1 := rfl

/-- Store a value at a key, replacing whatever was there, at the price of one
`DictOp.insert`, and of one cell if the key was not already present. -/
def insert [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) : Charged κ κₛ (Dict ι α) :=
  Charged.opUpdate (opcode κ .insert) (slots (DictCells.cell ι α))
    (fun x => ⟨(k, v) :: eraseKey k x.entries, by
      rw [List.map_cons, List.nodup_cons]
      exact ⟨fun h => ((mem_keys_eraseKey k k x.entries).1 h).1 rfl,
        nodup_eraseKey k x.nodupKeys⟩⟩) d

/-- What an insertion stores: the new value at `k`, and nothing else moved. -/
@[simp] theorem lookup_insert [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) (k' : ι) :
    ((insert (κ := κ) k v d).val).lookup k' = if k' = k then some v else d.lookup k' := by
  by_cases h : k' = k
  · subst h
    simp only [insert, Charged.val_opUpdate, lookup, findEntry]
    simp
  · simp only [insert, Charged.val_opUpdate, lookup, findEntry,
      if_neg (show ¬ k = k' from fun hh => h hh.symm), findEntry_eraseKey, if_neg h]

@[simp] theorem keys_insert [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) :
    ((insert (κ := κ) k v d).val).keys = Insert.insert k d.keys := by
  ext y
  simp only [insert, Charged.val_opUpdate, keys, List.map_cons, List.toFinset_cons,
    Finset.mem_insert, List.mem_toFinset, mem_keys_eraseKey]
  constructor
  · rintro (h | ⟨_, h⟩) <;> simp [h]
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hy : y = k
      · exact Or.inl hy
      · exact Or.inr ⟨hy, h⟩

@[simp] theorem cost_insert [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) :
    (insert (κ := κ) (κₛ := κₛ) k v d).cost = CostVec.one (opcode κ .insert) := rfl

/-- What an insertion takes, stated against the key set: one cell for a fresh
key, none for a key already present. -/
@[simp] theorem space_net_insert [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) (k' : κₛ) :
    (insert (κ := κ) k v d).space.net k'
      = if k' = cell ι α then ((Insert.insert k d.keys).card : ℤ) - (d.keys.card : ℤ)
        else 0 := by
  by_cases hk : k' = cell ι α
  · subst hk
    have h := keys_insert (κ := κ) (κₛ := κₛ) k v d
    rw [if_pos rfl, insert, space_net_update, ← card_keys, ← card_keys]
    rw [show ((fun x : Dict ι α => (⟨(k, v) :: eraseKey k x.entries, by
        rw [List.map_cons, List.nodup_cons]
        exact ⟨fun hh => ((mem_keys_eraseKey k k x.entries).1 hh).1 rfl,
          nodup_eraseKey k x.nodupKeys⟩⟩ : Dict ι α)) d).keys = Insert.insert k d.keys from h]
  · rw [if_neg hk, insert, space_net_update_of_ne _ hk]

/-- An insertion adds at most one cell. -/
theorem space_peak_insert_le [DictCells ι α κₛ] (k : ι) (v : α) (d : Dict ι α) (k' : κₛ) :
    (insert (κ := κ) k v d).space.peak k' ≤ 1 := by
  by_cases hk : k' = cell ι α
  case neg => rw [insert, space_peak_update_of_ne _ hk]; omega
  subst hk
  rw [insert, space_peak_update]
  have h : ((k, v) :: eraseKey k d.entries).length ≤ d.entries.length + 1 := by
    simpa using length_eraseKey_le k d.entries
  simp only [card]
  omega

/-- Remove a key and its value, at the price of one `DictOp.erase`, giving back
the cell the entry occupied. -/
def erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) : Charged κ κₛ (Dict ι α) :=
  Charged.opUpdate (opcode κ .erase) (slots (DictCells.cell ι α))
    (fun x => ⟨eraseKey k x.entries, nodup_eraseKey k x.nodupKeys⟩) d

@[simp] theorem lookup_erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) (k' : ι) :
    ((erase (κ := κ) k d).val).lookup k' = if k' = k then none else d.lookup k' := by
  simp only [erase, Charged.val_opUpdate, lookup, findEntry_eraseKey]

@[simp] theorem keys_erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) :
    ((erase (κ := κ) k d).val).keys = d.keys.erase k := by
  ext y
  simp only [erase, Charged.val_opUpdate, keys, List.mem_toFinset, mem_keys_eraseKey,
    Finset.mem_erase, List.mem_toFinset]

@[simp] theorem cost_erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) :
    (erase (κ := κ) (κₛ := κₛ) k d).cost = CostVec.one (opcode κ .erase) := rfl

/-- What an erase gives back, stated against the key set. -/
@[simp] theorem space_net_erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) (k' : κₛ) :
    (erase (κ := κ) k d).space.net k'
      = if k' = cell ι α then ((d.keys.erase k).card : ℤ) - (d.keys.card : ℤ) else 0 := by
  by_cases hk : k' = cell ι α
  · subst hk
    have h := keys_erase (κ := κ) (κₛ := κₛ) k d
    rw [if_pos rfl, erase, space_net_update, ← card_keys, ← card_keys]
    rw [show ((fun x : Dict ι α => (⟨eraseKey k x.entries, nodup_eraseKey k x.nodupKeys⟩ :
      Dict ι α)) d).keys = d.keys.erase k from h]
  · rw [if_neg hk, erase, space_net_update_of_ne _ hk]

/-- An erase never rises above where it started. -/
@[simp] theorem space_peak_erase [DictCells ι α κₛ] (k : ι) (d : Dict ι α) (k' : κₛ) :
    (erase (κ := κ) k d).space.peak k' = 0 := by
  by_cases hk : k' = cell ι α
  · subst hk
    rw [erase, space_peak_update]
    have h : (eraseKey k d.entries).length ≤ d.entries.length := length_eraseKey_le k d.entries
    simp only [card]
    omega
  · rw [erase, space_peak_update_of_ne _ hk]

/-- Ask how many entries the dictionary holds, at the price of one
`DictOp.size`. -/
def size (d : Dict ι α) : Charged κ κₛ ℕ :=
  Charged.op (opcode κ .size) d.entries.length

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem val_size (d : Dict ι α) : (size d : Charged κ κₛ ℕ).val = d.card := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem cost_size (d : Dict ι α) :
    (size d : Charged κ κₛ ℕ).cost = CostVec.one (opcode κ .size) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem space_size (d : Dict ι α) : (size d : Charged κ κₛ ℕ).space = 1 := rfl

/-- Compare the number of entries held against a number, at the price of one
`DictOp.cardEq`. -/
def cardEq (n : ℕ) (d : Dict ι α) : Charged κ κₛ Bool :=
  Charged.op (opcode κ .cardEq) (decide (d.entries.length = n))

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem val_cardEq (n : ℕ) (d : Dict ι α) :
    (cardEq n d : Charged κ κₛ Bool).val = decide (d.card = n) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem cost_cardEq (n : ℕ) (d : Dict ι α) :
    (cardEq n d : Charged κ κₛ Bool).cost = CostVec.one (opcode κ .cardEq) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem space_cardEq (n : ℕ) (d : Dict ι α) :
    (cardEq n d : Charged κ κₛ Bool).space = 1 := rfl

end Dict

end Arlib.Computation
