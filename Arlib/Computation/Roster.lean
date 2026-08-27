/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Abel

/-!
# A sealed finite set of keys, whose operations charge

A `Roster ι` is a finite set of keys that a program can touch only through a
charged operation.  It holds a private duplicate-free list; its `Finset` view,
its cardinality and the conversion into a `Roster` are `noncomputable`, so the
cost of a program written against a roster is the sequence of roster operations
it performs.

Values belong in `Arlib.Computation.Dict ι α`.  A roster stores membership and
nothing else.

The representation is a list rather than a `Finset` so that the elements can be
iterated: `Multiset.toList` is noncomputable, so a fold over a `Finset` is not a
program, and `filterErase` is such a fold.

## Main definitions

* `Roster ι` — a sealed finite set of keys.
* `Roster.toFinset`, `Roster.card` — the specification view; noncomputable.
* `Roster.ofFinset` — the roster holding a given set; noncomputable.
* `RosterOp`, `RosterOps` — the standard operations, and what a development's
  currency calls each of them.
* `RosterCells` — the kind of cell one element occupies.
* `Roster.empty`, `Roster.erase`, `Roster.insert`, `Roster.size`,
  `Roster.cardEq`, `Roster.mem` — the operations, one charge each.
* `Roster.filterErase` — one pass over the elements, deleting those a charged
  test rejects.
* `Roster.occupancy` — the measure an `ExactNet` obligation is stated against.
-/

namespace Arlib.Computation

universe u

/-- A finite set of keys that a program can touch only through a charged
operation.

The constructor, the list and the invariant are `private`, so outside this module
the only way to obtain a `Roster` is `empty` together with the operations
below. -/
structure Roster (ι : Type u) where
  private mk ::
  private elems : List ι
  private nodupElems : elems.Nodup

/-- The kind of storage cell a roster over `ι` occupies.

One instance per element type per development.  The kind comes from the data
rather than from a parameter at each operation, so every operation on the same
roster occupies and releases the same kind of cell. -/
class RosterCells (ι : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one element of a roster over `ι` occupies. -/
  cell : κₛ

/-- The standard roster operations.  Each of the operations below charges
exactly one of these, and takes no opcode parameter. -/
inductive RosterOp
  /-- Remove an element. -/
  | erase
  /-- Add an element. -/
  | insert
  /-- Ask how many elements are held. -/
  | size
  /-- Compare the number of elements held against a number. -/
  | cardEq
  /-- Test membership. -/
  | mem
  deriving DecidableEq, Repr, Inhabited

instance : Fintype RosterOp where
  elems := {.erase, .insert, .size, .cardEq, .mem}
  complete := fun x => by cases x <;> decide

/-- Which opcode of a development's currency `κ` names each standard roster
operation.  A name, not an amount: the amount is one charge per call, fixed by
the operations below.  `charge_injective` keeps distinct operations under
distinct names, and is discharged by `decide`. -/
class RosterOps (κ : Type) where
  /-- The development's opcode for a standard roster operation. -/
  charge : RosterOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

namespace Roster

variable {κ κₛ ι : Type} [DecidableEq κ] [DecidableEq κₛ] [DecidableEq ι]

/-- The kind of cell a roster over `ι` occupies. -/
abbrev cell (ι : Type) [RosterCells ι κₛ] : κₛ := RosterCells.cell ι

/-- The opcode a standard roster operation charges in the currency `κ`. -/
abbrev opcode (κ : Type) [RosterOps κ] (o : RosterOp) : κ := RosterOps.charge o

/-! ## The specification view

Every declaration in this section is `noncomputable`, and so cannot appear in a
program. -/

/-- The set a roster holds.  **Specification-only.** -/
noncomputable def toFinset (d : Roster ι) : Finset ι := d.elems.toFinset

/-- How many elements a roster holds.  **Specification-only**; the program
forms are `size` and `cardEq`. -/
noncomputable def card (d : Roster ι) : ℕ := d.elems.length

/-- The roster holding a given set.  **Specification-only.** -/
noncomputable def ofFinset (s : Finset ι) : Roster ι := ⟨s.toList, s.nodup_toList⟩

@[simp] theorem toFinset_ofFinset (s : Finset ι) : (ofFinset s).toFinset = s := by
  simp [toFinset, ofFinset]

/-- The cardinality view agrees with the set view. -/
@[simp] theorem card_toFinset (d : Roster ι) : d.toFinset.card = d.card := by
  simpa [toFinset, card] using List.toFinset_card_of_nodup d.nodupElems

/-! ## What a roster occupies

**A roster occupies one cell of the storage kind it is given, per element, and
nothing of any other kind.**  The `space_*` theorems below follow from this and
from what each operation does to the list. -/

/-- INTERNAL: one cell of kind `k` per element, and nothing of any other kind.
Exposed to proofs through the `space_*` theorems below, which state each
operation's residency change against the `Finset` view. -/
private def slots (k : κₛ) (d : Roster ι) : Residency κₛ :=
  Residency.ofFun fun k' => if k' = k then d.elems.length else 0

omit [DecidableEq ι] in
@[simp] theorem at'_slots_self (k : κₛ) (d : Roster ι) :
    (slots k d).at' k = d.card := by simp [slots, card]

omit [DecidableEq ι] in
@[simp] theorem at'_slots_of_ne {k k' : κₛ} (h : k' ≠ k) (d : Roster ι) :
    (slots k d).at' k' = 0 := by simp [slots, h]

/-- The measure an `Charged.ExactNet` obligation about a roster is stated
against. -/
def occupancy (k : κₛ) : Roster ι → Residency κₛ := slots k

omit [DecidableEq ι] in
@[simp] theorem occupancy_eq (k : κₛ) (d : Roster ι) : occupancy k d = slots k d := rfl

/-! ### What every operation does to what is held

Stated through `card`, the `Finset` view.  Each operation's space claim below is
a consequence of these and of what that operation does to the set. -/

omit [DecidableEq ι] in
/-- **An update's net is the change in cardinality.** -/
theorem space_net_update (o : κ) (k : κₛ) (f : Roster ι → Roster ι) (d : Roster ι) :
    (Charged.opUpdate o (slots k) f d).space.net k = ((f d).card : ℤ) - (d.card : ℤ) := by
  simp

omit [DecidableEq ι] in
/-- **An update's peak is its growth, or nothing if it shrank.** -/
theorem space_peak_update (o : κ) (k : κₛ) (f : Roster ι → Roster ι) (d : Roster ι) :
    (Charged.opUpdate o (slots k) f d).space.peak k
      = max 0 (((f d).card : ℤ) - (d.card : ℤ)) := by
  simp

omit [DecidableEq ι] in
/-- An operation on a roster changes nothing of any other kind. -/
@[simp] theorem space_net_update_of_ne (o : κ) {k k' : κₛ} (h : k' ≠ k)
    (f : Roster ι → Roster ι) (d : Roster ι) :
    (Charged.opUpdate o (slots k) f d).space.net k' = 0 := by
  simp [at'_slots_of_ne h]

omit [DecidableEq ι] in
@[simp] theorem space_peak_update_of_ne (o : κ) {k k' : κₛ} (h : k' ≠ k)
    (f : Roster ι → Roster ι) (d : Roster ι) :
    (Charged.opUpdate o (slots k) f d).space.peak k' = 0 := by
  simp [at'_slots_of_ne h]

/-! ## The operations

Each charges one operation, under the opcode its currency's `RosterOps` instance
names.  None takes an opcode or a storage kind as a parameter. -/

/-- The empty roster.  It holds nothing and charges nothing. -/
def empty : Roster ι := ⟨[], List.nodup_nil⟩

@[simp] theorem toFinset_empty : (empty : Roster ι).toFinset = ∅ := rfl

omit [DecidableEq ι] in
@[simp] theorem card_empty : (empty : Roster ι).card = 0 := rfl

variable [RosterOps κ]

/-- Remove an element, at the price of one `RosterOp.erase` and giving back its
cell. -/
def erase [RosterCells ι κₛ] (a : ι) (d : Roster ι) : Charged κ κₛ (Roster ι) :=
  Charged.opUpdate (opcode κ .erase) (slots (RosterCells.cell ι))
    (fun x => ⟨x.elems.erase a, x.nodupElems.erase a⟩) d

@[simp] theorem toFinset_erase [RosterCells ι κₛ] (a : ι) (d : Roster ι) :
    ((erase (κ := κ) a d).val).toFinset = d.toFinset.erase a := by
  ext y
  simp only [erase, Charged.val_opUpdate, toFinset, List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro h
    have := (List.Nodup.mem_erase_iff d.nodupElems).1 h
    exact ⟨this.1, this.2⟩
  · intro h
    exact (List.Nodup.mem_erase_iff d.nodupElems).2 ⟨h.1, h.2⟩

/-- An erase charges one `RosterOp.erase`. -/
@[simp] theorem cost_erase [RosterCells ι κₛ] (a : ι) (d : Roster ι) :
    (erase (κ := κ) (κₛ := κₛ) a d).cost = CostVec.one (opcode κ .erase) := rfl

/-- What an erase gives back, stated against the `Finset` view: the change in
cardinality, in cells of the roster's kind and of no other. -/
@[simp] theorem space_net_erase [RosterCells ι κₛ] (a : ι) (d : Roster ι) (k : κₛ) :
    (erase (κ := κ) a d).space.net k
      = if k = cell ι then ((d.toFinset.erase a).card : ℤ) - (d.toFinset.card : ℤ)
        else 0 := by
  by_cases hk : k = cell ι
  · subst hk
    have h : ((fun x : Roster ι => (⟨x.elems.erase a, x.nodupElems.erase a⟩ : Roster ι)) d).toFinset
        = d.toFinset.erase a := toFinset_erase (κ := κ) a d
    rw [if_pos rfl, erase, space_net_update, ← card_toFinset, ← card_toFinset, h]
  · rw [if_neg hk, erase, space_net_update_of_ne _ hk]

/-- An erase never rises above where it started. -/
@[simp] theorem space_peak_erase [RosterCells ι κₛ] (a : ι) (d : Roster ι)
    (k : κₛ) : (erase (κ := κ) a d).space.peak k = 0 := by
  by_cases hk : k = cell ι
  · subst hk
    rw [erase, space_peak_update]
    have h : ((⟨d.elems.erase a, d.nodupElems.erase a⟩ : Roster ι)).card ≤ d.card := by
      simpa [card] using List.length_erase_le (l := d.elems) (a := a)
    omega
  · rw [erase, space_peak_update_of_ne _ hk]

/-- Add an element, at the price of one `RosterOp.insert`, and of one cell if
the element was not already there. -/
def insert [RosterCells ι κₛ] (a : ι) (d : Roster ι) : Charged κ κₛ (Roster ι) :=
  Charged.opUpdate (opcode κ .insert) (slots (RosterCells.cell ι))
    (fun x => ⟨x.elems.insert a, x.nodupElems.insert⟩) d

@[simp] theorem toFinset_insert [RosterCells ι κₛ] (a : ι) (d : Roster ι) :
    ((insert (κ := κ) a d).val).toFinset = Insert.insert a d.toFinset := by
  ext y
  simp [insert, toFinset, List.mem_insert_iff]

@[simp] theorem cost_insert [RosterCells ι κₛ] (a : ι) (d : Roster ι) :
    (insert (κ := κ) (κₛ := κₛ) a d).cost = CostVec.one (opcode κ .insert) := rfl

/-- What an insertion takes, stated against the `Finset` view: one cell for a
fresh element, none for one already present. -/
@[simp] theorem space_net_insert [RosterCells ι κₛ] (a : ι) (d : Roster ι) (k : κₛ) :
    (insert (κ := κ) a d).space.net k
      = if k = cell ι then ((Insert.insert a d.toFinset).card : ℤ) - (d.toFinset.card : ℤ)
        else 0 := by
  by_cases hk : k = cell ι
  · subst hk
    have h : ((fun x : Roster ι => (⟨x.elems.insert a, x.nodupElems.insert⟩ : Roster ι)) d).toFinset
        = Insert.insert a d.toFinset := toFinset_insert (κ := κ) a d
    rw [if_pos rfl, insert, space_net_update, ← card_toFinset, ← card_toFinset, h]
  · rw [if_neg hk, insert, space_net_update_of_ne _ hk]

/-- An insertion rises by exactly what it takes. -/
@[simp] theorem space_peak_insert [RosterCells ι κₛ] (a : ι) (d : Roster ι) (k : κₛ) :
    (insert (κ := κ) a d).space.peak k
      = if k = cell ι then
          max 0 (((Insert.insert a d.toFinset).card : ℤ) - (d.toFinset.card : ℤ))
        else 0 := by
  by_cases hk : k = cell ι
  · subst hk
    have h : ((fun x : Roster ι => (⟨x.elems.insert a, x.nodupElems.insert⟩ : Roster ι)) d).toFinset
        = Insert.insert a d.toFinset := toFinset_insert (κ := κ) a d
    rw [if_pos rfl, insert, space_peak_update, ← card_toFinset, ← card_toFinset, h]
  · rw [if_neg hk, insert, space_peak_update_of_ne _ hk]

/-- An insertion adds at most one cell. -/
theorem space_peak_insert_le [RosterCells ι κₛ] (a : ι) (d : Roster ι) (k : κₛ) :
    (insert (κ := κ) a d).space.peak k ≤ 1 := by
  by_cases hk : k = cell ι
  case neg => rw [insert, space_peak_update_of_ne _ hk]; omega
  subst hk
  rw [insert, space_peak_update]
  have h : ((⟨d.elems.insert a, d.nodupElems.insert⟩ : Roster ι)).card ≤ d.card + 1 := by
    by_cases ha : a ∈ d.elems
    · simp [card, List.insert_of_mem ha]
    · simp [card, List.insert_of_not_mem ha]
  omega

/-- Ask how many elements the roster holds, at the price of one `RosterOp.size`.
The counterpart of `cardEq` for a program that needs the number itself rather
than a comparison. -/
def size (d : Roster ι) : Charged κ κₛ ℕ :=
  Charged.op (opcode κ .size) d.elems.length

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem val_size (d : Roster ι) : (size d : Charged κ κₛ ℕ).val = d.card := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem cost_size (d : Roster ι) :
    (size d : Charged κ κₛ ℕ).cost = CostVec.one (opcode κ .size) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
/-- A size query holds nothing. -/
@[simp] theorem space_size (d : Roster ι) :
    (size d : Charged κ κₛ ℕ).space = 1 := rfl

/-- Compare the number of elements held against a number, at the price of one
`RosterOp.cardEq`. -/
def cardEq (n : ℕ) (d : Roster ι) : Charged κ κₛ Bool :=
  Charged.op (opcode κ .cardEq) (decide (d.elems.length = n))

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem val_cardEq (n : ℕ) (d : Roster ι) :
    (cardEq n d : Charged κ κₛ Bool).val = decide (d.card = n) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem cost_cardEq (n : ℕ) (d : Roster ι) :
    (cardEq n d : Charged κ κₛ Bool).cost = CostVec.one (opcode κ .cardEq) := rfl

omit [DecidableEq ι] [DecidableEq κₛ] in
@[simp] theorem space_cardEq (n : ℕ) (d : Roster ι) :
    (cardEq n d : Charged κ κₛ Bool).space = 1 := rfl

/-- Test membership, at the price of one `RosterOp.mem`. -/
def mem (a : ι) (d : Roster ι) : Charged κ κₛ Bool :=
  Charged.op (opcode κ .mem) (decide (a ∈ d.elems))

omit [DecidableEq κₛ] in
@[simp] theorem val_mem (a : ι) (d : Roster ι) :
    (mem a d : Charged κ κₛ Bool).val = decide (a ∈ d.toFinset) := by
  simp [mem, toFinset]

omit [DecidableEq κₛ] in
@[simp] theorem cost_mem (a : ι) (d : Roster ι) :
    (mem a d : Charged κ κₛ Bool).cost = CostVec.one (opcode κ .mem) := rfl

omit [DecidableEq κₛ] in
@[simp] theorem space_mem (a : ι) (d : Roster ι) :
    (mem a d : Charged κ κₛ Bool).space = 1 := rfl

/-! ## One pass over the elements

`filterErase` runs a charged test on each element and deletes the ones it
rejects.  The test is a parameter, since only the development knows what its
test does; the deletion opcode is not. -/

/-- INTERNAL: the underlying list fold, deleting from the accumulator in the
order the roster stores its elements. -/
private def filterStep [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (acc : Roster ι) (x : ι) : Charged κ κₛ (Roster ι) :=
  keep x >>= fun b => if b then (pure acc : Charged κ κₛ (Roster ι)) else erase x acc

/-- One pass over the roster: run `keep` on each element and delete the ones it
rejects, each deletion charging one `RosterOp.erase`.  `cost_filterErase` gives
the total. -/
def filterErase [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool) (d : Roster ι) :
    Charged κ κₛ (Roster ι) :=
  Charged.foldl (filterStep keep) d.elems d

omit [DecidableEq κ] [RosterOps κ] in
/-- INTERNAL: what an erase-the-rejected fold does to a duplicate-free list.  The
second disjunct is the elements the pass has not visited, which it keeps. -/
private theorem foldl_eraseIf (p : ι → Bool) :
    ∀ (l acc : List ι), acc.Nodup →
      List.foldl (fun L x => if p x then L else L.erase x) acc l
        = acc.filter (fun y => p y || decide (y ∉ l)) := by
  intro l
  induction l with
  | nil =>
      intro acc _
      simp
  | cons x l ih =>
      intro acc hacc
      by_cases hx : p x
      · rw [List.foldl_cons, if_pos hx, ih acc hacc]
        refine List.filter_congr fun y _ => ?_
        by_cases hy : y = x
        · subst hy; simp [hx]
        · simp [List.mem_cons, hy]
      · rw [List.foldl_cons, if_neg hx, ih _ (hacc.erase x),
          List.Nodup.erase_eq_filter hacc x, List.filter_filter]
        refine List.filter_congr fun y _ => ?_
        by_cases hy : y = x
        · subst hy; simp [hx]
        · simp [List.mem_cons, hy]

/-- One pass leaves exactly the elements the test accepted. -/
@[simp] theorem toFinset_filterErase [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (d : Roster ι) :
    ((filterErase keep d).val).toFinset
      = d.toFinset.filter (fun x => (keep x).val) := by
  have hval : ∀ (l : List ι) (acc : Roster ι),
      ((Charged.foldl (filterStep keep) l acc).val).elems
        = List.foldl (fun L x => if (keep x).val then L else L.erase x) acc.elems l := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x l ih =>
        intro acc
        rw [Charged.val_foldl_cons, ih]
        by_cases hx : (keep x).val
        · simp [filterStep, hx]
        · simp [filterStep, hx, erase]
  have h := hval d.elems d
  have hfold := foldl_eraseIf (fun x => (keep x).val) d.elems d.elems d.nodupElems
  have hself : d.elems.filter (fun y => (keep y).val || decide (y ∉ d.elems))
      = d.elems.filter (fun y => (keep y).val) :=
    List.filter_congr fun y hy => by simp [hy]
  ext y
  simp only [filterErase, toFinset, List.mem_toFinset, h, hfold, hself,
    Finset.mem_filter, List.mem_filter]

/-- What one pass costs: the test's charge on every element, plus one deletion
for each element it rejects. -/
theorem cost_filterErase [RosterCells ι κₛ] (coin : κ) (keep : ι → Charged κ κₛ Bool)
    (d : Roster ι) (hkeep : ∀ x, (keep x).cost = CostVec.one coin) :
    (filterErase keep d).cost
      = CostVec.many coin d.card
        + CostVec.many (opcode κ .erase) (d.elems.countP (fun x => !(keep x).val)) := by
  have hstep : ∀ (acc : Roster ι) (x : ι), (filterStep keep acc x).cost
      = CostVec.one coin + (if (keep x).val then 0 else CostVec.one (opcode κ .erase)) := by
    intro acc x
    by_cases hx : (keep x).val <;> simp [filterStep, hkeep, hx]
  have hsum : ∀ l : List ι,
      (l.map (fun x =>
          CostVec.one coin + (if (keep x).val then 0 else CostVec.one (opcode κ .erase)))).sum
        = CostVec.many coin l.length
          + CostVec.many (opcode κ .erase) (l.countP (fun x => !(keep x).val)) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
        by_cases hx : (keep x).val <;>
          simp [ih, hx, CostVec.many_succ] <;> abel
  rw [filterErase, Charged.cost_foldl_eq hstep d.elems d, hsum]
  rfl

omit [DecidableEq κ] [DecidableEq κₛ] [RosterOps κ] in
/-- The number of deletions, in set terms: the elements the test rejected. -/
theorem countP_reject (keep : ι → Charged κ κₛ Bool) (d : Roster ι) :
    d.elems.countP (fun x => !(keep x).val)
      = d.card - (d.toFinset.filter (fun x => (keep x).val)).card := by
  have hlen := List.length_eq_countP_add_countP (l := d.elems) (p := fun x => (keep x).val)
  have hfilter : (d.toFinset.filter (fun x => (keep x).val)).card
      = d.elems.countP (fun x => (keep x).val) := by
    have : d.toFinset.filter (fun x => (keep x).val)
        = (d.elems.filter (fun x => (keep x).val)).toFinset := by
      ext y; simp [toFinset]
    rw [this, List.toFinset_card_of_nodup (d.nodupElems.filter _),
      List.countP_eq_length_filter]
  have hbridge : d.elems.countP (fun x => decide ¬((keep x).val = true))
      = d.elems.countP (fun x => !(keep x).val) :=
    List.countP_congr fun x _ => by simp
  rw [hbridge] at hlen
  rw [hfilter]
  simp only [card]
  omega

/-- What one pass costs, stated against the `Finset` view: the test's charge on
every element, plus one deletion for each element it rejected. -/
theorem cost_filterErase_card [RosterCells ι κₛ] (coin : κ) (keep : ι → Charged κ κₛ Bool)
    (d : Roster ι) (hkeep : ∀ x, (keep x).cost = CostVec.one coin) :
    (filterErase keep d).cost
      = CostVec.many coin d.card
        + CostVec.many (opcode κ .erase)
            (d.card - (d.toFinset.filter (fun x => (keep x).val)).card) := by
  rw [cost_filterErase coin keep d hkeep, countP_reject]

/-! ### What a pass costs in space

Nothing: a pass that only deletes cannot raise a run's high-water mark, however
many elements it visits. -/

/-- A thinning pass never rises above where it started.  The hypothesis is that
the test itself holds nothing, which `Charged.op`-built tests satisfy by
`space_op`. -/
@[simp] theorem space_peak_filterErase [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (hkeep : ∀ x k, (keep x).space.peak k ≤ 0) (d : Roster ι) (k : κₛ) :
    (filterErase keep d).space.peak k = 0 := by
  have hstep : ∀ (acc : Roster ι) (x : ι), (filterStep keep acc x).space.peak k ≤ 0 := by
    intro acc x
    have hk := hkeep x k
    have hn := (keep x).space.net_le_peak k
    by_cases hx : (keep x).val
    · simp only [filterStep, Charged.space_bind, hx, if_pos, Charged.space_pure,
        Profile.peak_mul, Profile.peak_one]
      omega
    · simp only [filterStep, Charged.space_bind, hx, if_neg, Bool.false_eq_true,
        not_false_eq_true, Profile.peak_mul, space_peak_erase]
      omega
  have := Charged.space_peak_foldl_nonpos (f := filterStep keep) k hstep d.elems d
  have h0 := (filterErase keep d).space.zero_le_peak k
  rw [filterErase] at *
  omega

/-- A pass gives back a cell for every element it discards. -/
theorem space_net_filterErase_nonpos [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (hkeep : ∀ x k, (keep x).space.peak k ≤ 0) (d : Roster ι) (k : κₛ) :
    (filterErase keep d).space.net k ≤ 0 := by
  have h := (filterErase keep d).space.net_le_peak k
  rw [space_peak_filterErase keep hkeep d k] at h
  exact h

/-- A pass is exact: its net is precisely the change in what it holds.  The
hypothesis is that the test holds nothing, which `Charged.op`-built tests
satisfy. -/
theorem exactNet_filterErase [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (hkeep : ∀ x, (keep x).space = 1) (d : Roster ι) :
    Charged.ExactNet (occupancy (cell ι)) (occupancy (cell ι)) d (filterErase keep d) := by
  refine Charged.exactNet_foldl (m := occupancy (ι := ι) (cell ι)) ?_ d.elems d
  intro acc x k'
  by_cases hx : (keep x).val
  · simp [filterStep, hkeep, hx]
  · simp only [filterStep, Charged.space_bind, hkeep, one_mul, hx, Bool.false_eq_true,
      if_neg, not_false_eq_true, Charged.val_bind, occupancy_eq]
    by_cases hk : k' = cell ι
    · subst hk
      rw [erase, space_net_update, Charged.val_opUpdate, at'_slots_self, at'_slots_self]
    · rw [erase, space_net_update_of_ne _ hk, Charged.val_opUpdate,
        at'_slots_of_ne hk, at'_slots_of_ne hk]
      simp

/-- The `Finset` reading of the same fact. -/
theorem space_net_filterErase [RosterCells ι κₛ] (keep : ι → Charged κ κₛ Bool)
    (hkeep : ∀ x, (keep x).space = 1) (d : Roster ι) (k : κₛ) :
    (filterErase keep d).space.net k
      = if k = cell ι then (((filterErase keep d).val).card : ℤ) - (d.card : ℤ)
        else 0 := by
  have h := exactNet_filterErase keep hkeep d k
  by_cases hk : k = cell ι
  · subst hk; rw [if_pos rfl]; simpa using h
  · rw [if_neg hk]; simpa [occupancy, at'_slots_of_ne hk] using h

end Roster

end Arlib.Computation
