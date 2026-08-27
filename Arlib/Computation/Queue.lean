/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged

/-!
# A sealed queue, whose dequeue is destructive and charged

`Arlib.Computation.Roster` seals a *set*: membership, cardinality, one pass over
the elements.  A sampling algorithm that keeps a **list of drawn samples and
consumes them one at a time** wants something else, and the difference is not
cosmetic:

* the order matters — `σ ← Sᵢ.dequeue()` takes the *next* sample, not an
  arbitrary one;
* the read is destructive — each call must not see what an earlier call took;
* an exhausted list is a control-flow event, and in the `#NFA` estimator it is
  the `Break` whose probability is bounded separately.

A `Roster` cannot express any of the three.  Written against ordinary Lean lists
they are all free: `l.head?`, `l.tail` and `l.isEmpty` cost nothing, so a
development that keeps its samples in a `List` is doing the algorithm's
bookkeeping outside the charged world.

## What a dequeue does to what is held

`dequeue` gives back the cell the element occupied, and that is the honest
reading for a *sample* queue — the element is consumed.  It is not the honest
reading for a queue whose elements are then retained: the element leaves the
queue and lands in the caller's hands, and `Charged.ExactNet` is the obligation
that notices.  See `Charged`'s note on `pure (x, x)`; this is the same hole, and
the same discipline answers it.

## Main definitions

* `QueueOp`, `QueueOps` — the currency, and what a development calls each operation.
* `QueueCells` — which storage kind one element occupies.
* `Queue ι` — a sealed FIFO.
* `Queue.enqueue`, `Queue.dequeue`, `Queue.isEmpty` — the operations.
-/

namespace Arlib.Computation

universe u

/-- **The standard queue operations, as arlib's own currency.** -/
inductive QueueOp
  /-- Add an element at the back. -/
  | enqueue
  /-- Take the element at the front, destructively. -/
  | dequeue
  /-- Ask whether the queue is empty. -/
  | isEmpty
  deriving DecidableEq, Repr, Inhabited

instance : Fintype QueueOp where
  elems := {.enqueue, .dequeue, .isEmpty}
  complete := fun x => by cases x <;> decide

/-- **What a development's currency calls each queue operation.**  A name, never
an amount; see `RosterOps`. -/
class QueueOps (κ : Type) where
  /-- The development's opcode for a standard queue operation. -/
  charge : QueueOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The opcode a queue operation charges in the currency `κ`. -/
abbrev queueOpcode (κ : Type) [QueueOps κ] (o : QueueOp) : κ := QueueOps.charge o

/-- **Where a queue's cells come from.**  The `RosterCells` of this module, and for
the same reason: the storage kind is a property of the data, so naming it per
call would invite a choice that is not the author's. -/
class QueueCells (ι : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one element of a queue over `ι` occupies. -/
  cell : κₛ

/-- **A sealed queue.**

The list is private and its view is `noncomputable`, so outside this module the
only things one can do with a queue are the operations below.  In particular
`l.head?` and `l.tail` — the two halves of a free dequeue — do not typecheck. -/
structure Queue (ι : Type u) where
  private mk ::
  private elems : List ι

namespace Queue

variable {κ κₛ : Type} {ι : Type} [DecidableEq κ] [DecidableEq κₛ] [QueueOps κ]

/-- The kind of cell a queue over `ι` occupies. -/
abbrev cell (ι : Type) [QueueCells ι κₛ] : κₛ := QueueCells.cell ι

/-- The elements a queue holds, front first.  **Specification-only.** -/
noncomputable def toList (q : Queue ι) : List ι := q.elems

/-- How many elements a queue holds.  **Specification-only** — a program that
wants to know must ask. -/
noncomputable def length (q : Queue ι) : ℕ := q.elems.length

/-- The queue holding a given list.  **The boundary**, noncomputable so that it
cannot appear inside a program. -/
noncomputable def ofList (l : List ι) : Queue ι := ⟨l⟩

omit [DecidableEq κ] [DecidableEq κₛ] [QueueOps κ] in
@[simp] theorem toList_ofList (l : List ι) : (ofList l).toList = l := rfl

/-- The empty queue.  The one free constructor: it holds nothing. -/
def empty : Queue ι := ⟨[]⟩

omit [DecidableEq κ] [DecidableEq κₛ] [QueueOps κ] in
@[simp] theorem toList_empty : (empty : Queue ι).toList = [] := rfl

/-! ## What a queue occupies

One assertion, in one place: **a queue occupies one cell of its storage kind per
element.**  Private, for the reason `Roster.slots` is private: a program that could
call it would have a free length. -/

private def slots (k : κₛ) (p : Option ι × Queue ι) : Residency κₛ :=
  Residency.ofFun fun k' => if k' = k then p.2.elems.length else 0

omit [DecidableEq κ] [QueueOps κ] in
@[simp] theorem at'_slots_self (k : κₛ) (p : Option ι × Queue ι) :
    (slots k p).at' k = p.2.length := by simp [slots, length]

omit [DecidableEq κ] [QueueOps κ] in
@[simp] theorem at'_slots_of_ne {k k' : κₛ} (h : k' ≠ k) (p : Option ι × Queue ι) :
    (slots k p).at' k' = 0 := by simp [slots, h]

/-! ## The operations -/

/-- **Add an element at the back**, at the price of one `QueueOp.enqueue` and one
cell. -/
def enqueue [QueueCells ι κₛ] (a : ι) (q : Queue ι) : Charged κ κₛ (Queue ι) :=
  Prod.snd <$> Charged.opUpdate (queueOpcode κ .enqueue) (slots (QueueCells.cell ι))
    (fun p => (p.1, ⟨p.2.elems ++ [a]⟩)) (none, q)

@[simp] theorem toList_enqueue [QueueCells ι κₛ] (a : ι) (q : Queue ι) :
    ((enqueue (κ := κ) a q).val).toList = q.toList ++ [a] := rfl

@[simp] theorem cost_enqueue [QueueCells ι κₛ] (a : ι) (q : Queue ι) :
    (enqueue (κ := κ) (κₛ := κₛ) a q).cost = CostVec.one (queueOpcode κ .enqueue) := by
  simp [enqueue]

/-- **An enqueue takes exactly one cell**, stated against the list view. -/
@[simp] theorem space_net_enqueue [QueueCells ι κₛ] (a : ι) (q : Queue ι) (k : κₛ) :
    (enqueue (κ := κ) a q).space.net k
      = if k = cell ι then 1 else 0 := by
  by_cases hk : k = cell ι
  · subst hk
    simp only [enqueue, Charged.space_map, Charged.space_opUpdate, Profile.net_between,
      at'_slots_self, length]
    simp
  · simp only [enqueue, Charged.space_map, Charged.space_opUpdate, Profile.net_between,
      at'_slots_of_ne hk, if_neg hk]
    simp

/-- **Take the element at the front, destructively**, at the price of one
`QueueOp.dequeue`, giving back the cell it occupied.

Returns `none` on an empty queue, which is the control-flow event a `Break`
branches on — and asking is the same operation, so a program cannot discover
that a queue is exhausted without paying. -/
def dequeue [QueueCells ι κₛ] (q : Queue ι) : Charged κ κₛ (Option ι × Queue ι) :=
  Charged.opUpdate (queueOpcode κ .dequeue) (slots (QueueCells.cell ι))
    (fun p => (p.2.elems.head?, ⟨p.2.elems.tail⟩)) (none, q)

@[simp] theorem val_dequeue [QueueCells ι κₛ] (q : Queue ι) :
    (dequeue (κ := κ) (κₛ := κₛ) q).val
      = (q.toList.head?, ofList q.toList.tail) := rfl

@[simp] theorem cost_dequeue [QueueCells ι κₛ] (q : Queue ι) :
    (dequeue (κ := κ) (κₛ := κₛ) q).cost = CostVec.one (queueOpcode κ .dequeue) := rfl

/-- **A dequeue never rises above where it started.**  The half a loop invariant
consumes: a pass that only consumes samples cannot push a run over a ceiling. -/
@[simp] theorem space_peak_dequeue [QueueCells ι κₛ] (q : Queue ι) (k : κₛ) :
    (dequeue (κ := κ) (κₛ := κₛ) q).space.peak k = 0 := by
  by_cases hk : k = cell ι
  · subst hk
    simp only [dequeue, Charged.space_opUpdate, Profile.peak_between, at'_slots_self]
    have : (⟨q.elems.tail⟩ : Queue ι).length ≤ q.length := by
      simp [length]
    omega
  · simp [dequeue, at'_slots_of_ne hk]

/-- **Ask whether the queue is empty**, at the price of one `QueueOp.isEmpty`.

`length` is the specification's view and is noncomputable, so a program cannot
read a queue's size; it has to ask, and asking is an operation. -/
def isEmpty (q : Queue ι) : Charged κ κₛ Bool :=
  Charged.op (queueOpcode κ .isEmpty) q.elems.isEmpty

omit [DecidableEq κₛ] in
@[simp] theorem val_isEmpty (q : Queue ι) :
    (isEmpty q : Charged κ κₛ Bool).val = q.toList.isEmpty := rfl

omit [DecidableEq κₛ] in
@[simp] theorem cost_isEmpty (q : Queue ι) :
    (isEmpty q : Charged κ κₛ Bool).cost = CostVec.one (queueOpcode κ .isEmpty) := rfl

omit [DecidableEq κₛ] in
@[simp] theorem space_isEmpty (q : Queue ι) :
    (isEmpty q : Charged κ κₛ Bool).space = 1 := rfl

end Queue

end Arlib.Computation
