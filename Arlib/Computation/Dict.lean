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
# A sealed dictionary, whose operations charge

`Arlib.Computation.Charged` stops a program understating a step it takes.  It
does not, on its own, stop `pure (expensiveThing x)`: Lean computes
`expensiveThing` for free.  This module closes that for the one data structure
most sampling algorithms are written against — a finite set.

The seal is `Arlib.Computation.Machine`'s, transposed.  A `Dict ι` holds a
private duplicate-free list.  Its `Finset` view, its cardinality and the
conversion *into* a `Dict` are all `noncomputable`, so a program that inspects a
dictionary without a charged operation **fails to compile**.  What is left is the
operation set below, each built by `Charged.op`, so the cost of a program written
against a dictionary is whatever sequence of dictionary operations it performs —
computed by the elaborator from the program's text, not asserted by its author.

## Why a list and not a `Finset`

A `Finset` cannot be iterated: `Multiset.toList` is noncomputable, so a fold over
a `Finset`'s elements is not a program.  Thinning a sample set — one coin per
element, one deletion per element discarded — *is* a fold over the elements, and
its cost is the thing worth getting right.  A duplicate-free list is a real
dictionary's shape, iterates, and carries the `Finset` view a specification wants.

## The boundary

`ofFinset` exists because a caller usually holds a mathematical `Finset` and has
to get a dictionary from it.  It is `noncomputable`, so it cannot appear in a
program; only in the surrounding instrumentation, which is not the algorithm.
This is the same standard as `Word.toNat`, and like it, `scripts/ComputationAudit.lean`
names it as specification vocabulary rather than letting it pass silently.

## Main definitions

* `Dict ι` — a sealed dictionary.
* `Dict.toFinset`, `Dict.card`, `Dict.ofFinset` — the specification view; noncomputable.
* `Dict.erase`, `Dict.insert`, `Dict.cardEq`, `Dict.mem` — the unit-cost operations.
* `Dict.filterErase` — one pass over the elements, deleting those a charged test rejects.
-/

namespace Arlib.Computation

universe u

/-- A dictionary over `ι`: a finite set that a program can only touch through a
charged operation.

The field is a duplicate-free list rather than a `Finset` so that iteration is a
program; the constructor, the list and the invariant are all `private`, so
outside this module the only way to obtain a `Dict` is `empty` together with the
operations below. -/
structure Dict (ι : Type u) where
  private mk ::
  private elems : List ι
  private nodupElems : elems.Nodup

namespace Dict

variable {κ ι : Type} [DecidableEq κ] [DecidableEq ι]

/-! ## The specification view

Every declaration in this section is `noncomputable` on purpose.  Each of them
would let a program read a dictionary without paying, so making them
uncompilable is what stops that. -/

/-- The set a dictionary holds.  **Specification-only.** -/
noncomputable def toFinset (d : Dict ι) : Finset ι := d.elems.toFinset

/-- How many elements a dictionary holds.  **Specification-only** — a program
that wants to know must ask, and `cardEq` is what it asks with. -/
noncomputable def card (d : Dict ι) : ℕ := d.elems.length

/-- The dictionary holding a given set.  **The boundary**, and noncomputable so
that it cannot appear inside a program: see the module header. -/
noncomputable def ofFinset (s : Finset ι) : Dict ι := ⟨s.toList, s.nodup_toList⟩

@[simp] theorem toFinset_ofFinset (s : Finset ι) : (ofFinset s).toFinset = s := by
  simp [toFinset, ofFinset]

/-- The cardinality view agrees with the set view.  Duplicate-freeness is exactly
what this needs, and is why the invariant is a field. -/
@[simp] theorem card_toFinset (d : Dict ι) : d.toFinset.card = d.card := by
  simpa [toFinset, card] using List.toFinset_card_of_nodup d.nodupElems

/-! ## The operations -/

/-- The empty dictionary.  The one free constructor: it holds nothing, so
producing it is no work. -/
def empty : Dict ι := ⟨[], List.nodup_nil⟩

@[simp] theorem toFinset_empty : (empty : Dict ι).toFinset = ∅ := rfl

omit [DecidableEq ι] in
@[simp] theorem card_empty : (empty : Dict ι).card = 0 := rfl

/-- Remove an element, at the price of one `o`. -/
def erase (o : κ) (a : ι) (d : Dict ι) : Charged κ (Dict ι) :=
  Charged.op o ⟨d.elems.erase a, d.nodupElems.erase a⟩

@[simp] theorem toFinset_erase (o : κ) (a : ι) (d : Dict ι) :
    ((erase o a d).val).toFinset = d.toFinset.erase a := by
  ext y
  simp only [erase, Charged.val_op, toFinset, List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro h
    have := (List.Nodup.mem_erase_iff d.nodupElems).1 h
    exact ⟨this.1, this.2⟩
  · intro h
    exact (List.Nodup.mem_erase_iff d.nodupElems).2 ⟨h.1, h.2⟩

@[simp] theorem cost_erase (o : κ) (a : ι) (d : Dict ι) :
    (erase o a d).cost = CostVec.one o := rfl

/-- Add an element, at the price of one `o`. -/
def insert (o : κ) (a : ι) (d : Dict ι) : Charged κ (Dict ι) :=
  Charged.op o ⟨d.elems.insert a, d.nodupElems.insert⟩

@[simp] theorem toFinset_insert (o : κ) (a : ι) (d : Dict ι) :
    ((insert o a d).val).toFinset = Insert.insert a d.toFinset := by
  ext y
  simp [insert, toFinset, List.mem_insert_iff]

@[simp] theorem cost_insert (o : κ) (a : ι) (d : Dict ι) :
    (insert o a d).cost = CostVec.one o := rfl

/-- Compare the size against a number, at the price of one `o`.  This is the only
way a program learns anything about a dictionary's cardinality. -/
def cardEq (o : κ) (n : ℕ) (d : Dict ι) : Charged κ Bool :=
  Charged.op o (decide (d.elems.length = n))

omit [DecidableEq ι] in
@[simp] theorem val_cardEq (o : κ) (n : ℕ) (d : Dict ι) :
    (cardEq o n d).val = decide (d.card = n) := rfl

omit [DecidableEq ι] in
@[simp] theorem cost_cardEq (o : κ) (n : ℕ) (d : Dict ι) :
    (cardEq o n d).cost = CostVec.one o := rfl

/-- Test membership, at the price of one `o`. -/
def mem (o : κ) (a : ι) (d : Dict ι) : Charged κ Bool :=
  Charged.op o (decide (a ∈ d.elems))

@[simp] theorem val_mem (o : κ) (a : ι) (d : Dict ι) :
    (mem o a d).val = decide (a ∈ d.toFinset) := by
  simp [mem, toFinset]

@[simp] theorem cost_mem (o : κ) (a : ι) (d : Dict ι) :
    (mem o a d).cost = CostVec.one o := rfl

/-! ## One pass over the elements

`filterErase` is the shape of every "keep some, discard the rest" line: run a
charged test on each element and delete the ones it rejects.  Its cost is a
consequence of the fold, so an author cannot get the count of deletions wrong. -/

/-- INTERNAL: the underlying list fold.  Deleting from the accumulator, in the
order the dictionary stores its elements. -/
private def filterStep (del : κ) (keep : ι → Charged κ Bool) (acc : Dict ι) (x : ι) :
    Charged κ (Dict ι) :=
  keep x >>= fun k => if k then (pure acc : Charged κ (Dict ι)) else erase del x acc

/-- One pass over the dictionary: run `keep` on each element and delete the ones
it rejects, each deletion priced at one `del`.

The cost is not written here: it is whatever `keep` charges on each element, plus
one `del` per rejection, and `cost_filterErase` computes it. -/
def filterErase (del : κ) (keep : ι → Charged κ Bool) (d : Dict ι) : Charged κ (Dict ι) :=
  Charged.foldl (filterStep del keep) d.elems d

/-- INTERNAL: what an erase-the-rejected fold does to a duplicate-free list.  The
second disjunct is the elements the pass never visited, which it therefore keeps. -/
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

/-- **What one pass leaves behind**: exactly the elements the test accepted. -/
@[simp] theorem toFinset_filterErase (del : κ) (keep : ι → Charged κ Bool) (d : Dict ι) :
    ((filterErase del keep d).val).toFinset
      = d.toFinset.filter (fun x => (keep x).val) := by
  have hval : ∀ (l : List ι) (acc : Dict ι),
      ((Charged.foldl (filterStep del keep) l acc).val).elems
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

/-- **What one pass costs**: whatever the test charges on each element, plus one
deletion for each element it rejects.

Both summands are consequences of the fold.  The count of deletions in particular
is not a number anyone supplies — it is `countP`, forced by the program. -/
theorem cost_filterErase (del coin : κ) (keep : ι → Charged κ Bool) (d : Dict ι)
    (hkeep : ∀ x, (keep x).cost = CostVec.one coin) :
    (filterErase del keep d).cost
      = CostVec.many coin d.card
        + CostVec.many del (d.elems.countP (fun x => !(keep x).val)) := by
  have hstep : ∀ (acc : Dict ι) (x : ι), (filterStep del keep acc x).cost
      = CostVec.one coin + (if (keep x).val then 0 else CostVec.one del) := by
    intro acc x
    by_cases hx : (keep x).val <;> simp [filterStep, hkeep, hx]
  have hsum : ∀ l : List ι,
      (l.map (fun x => CostVec.one coin + (if (keep x).val then 0 else CostVec.one del))).sum
        = CostVec.many coin l.length + CostVec.many del (l.countP (fun x => !(keep x).val)) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
        by_cases hx : (keep x).val <;>
          simp [ih, hx, CostVec.many_succ] <;> abel
  rw [filterErase, Charged.cost_foldl_eq hstep d.elems d, hsum]
  rfl

omit [DecidableEq κ] in
/-- **The number of deletions, in set terms**: the elements the test rejected. -/
theorem countP_reject (keep : ι → Charged κ Bool) (d : Dict ι) :
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

/-- **What one pass costs, stated without mentioning the representation**: the
test's charge on every element, plus one deletion for each element it rejected.

This is the form a caller uses.  Neither summand is a number anyone supplies. -/
theorem cost_filterErase_card (del coin : κ) (keep : ι → Charged κ Bool) (d : Dict ι)
    (hkeep : ∀ x, (keep x).cost = CostVec.one coin) :
    (filterErase del keep d).cost
      = CostVec.many coin d.card
        + CostVec.many del (d.card - (d.toFinset.filter (fun x => (keep x).val)).card) := by
  rw [cost_filterErase del coin keep d hkeep, countP_reject]

end Dict

end Arlib.Computation
