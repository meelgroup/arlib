/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Machine

/-!
# The standard currency, and what it costs on the machine

A tally is `CostVec κ = κ → ℕ`, one function over one type, while an algorithm
touches several sealed carriers, each with its own operation type.  Somebody has
to supply the type that covers all of them, and until now that was the
development: it declared an inductive, wrote a `RosterOps`/`RandOps`/`SlotOps`
instance mapping arlib's operations onto its own names, and discharged
`charge_injective` by `decide`.

That table is a translation a reader has to check, and it buys nothing when every
operation a development performs is already one of arlib's.  `StdOp` is the
coproduct, supplied here, with the three instances as injections — so there is
nothing to choose and nothing to check.

**A development declares an operation only when arlib has no analogue for it**,
and then declares that operation and its cost, and nothing else.

## Where cost becomes machine operations

`StdImpl` is the join to `Arlib.Computation.Machine`: `rate` says what one
standard operation costs in word operations, and `Charged.exchange` carries a
bound in `StdOp` across to a bound in `Op`.  It is a **hypothesis** — a
description of an implementation, not an implementation — and `StdImpl.trivial`
exists only so that theorems taking one are not vacuously true.

Discharging it is the open work: write a `Roster` as a `RAM` program over
`HoldsList`, prove its five operations meet an `StdImpl`, and every bound stated
against `StdOp` becomes a bound in word operations with a witness behind it.

## Main definitions

* `StdOp` — every operation arlib's sealed carriers perform.
* `Cell` — one storage kind, for a development holding one structure.
* `StdImpl` — what one standard operation costs in word operations.
-/

namespace Arlib.Computation

universe u

/-! ## The work currency -/

/-- Every operation arlib's sealed carriers perform: the dictionary operations of
`Roster`, the randomness operations of `Block`/`Coins`/`Sampler`, and the
answer-register operations of `Slot`. -/
inductive StdOp
  | roster : RosterOp → StdOp
  | rand : RandOp → StdOp
  | slot : SlotOp → StdOp
  deriving DecidableEq

namespace StdOp

/-- Every standard operation, as a list. -/
def all : List StdOp :=
  [.roster .erase, .roster .insert, .roster .size, .roster .cardEq, .roster .mem,
   .rand .flip, .rand .accept, .rand .halve, .rand .inflate,
   .slot .test, .slot .fill]

/-- INTERNAL: `all` is exhaustive, which is what makes `Fintype` legal. -/
theorem mem_all (o : StdOp) : o ∈ all := by
  cases o <;> rename_i x <;> cases x <;> simp [all]

/-- The currency is finite, so `CostVec.steps` can sum over it. -/
instance : Fintype StdOp := Fintype.ofList all mem_all

end StdOp

/-- The dictionary operations, under their own names.  An injection, so
`charge_injective` is a `cases` rather than a table to read. -/
instance stdRosterOps : RosterOps StdOp where
  charge := StdOp.roster
  charge_injective := by intro a b h; simpa using h

/-- The randomness operations, under their own names. -/
instance stdRandOps : RandOps StdOp where
  charge := StdOp.rand
  charge_injective := by intro a b h; simpa using h

/-- The answer-register operations, under their own names. -/
instance stdSlotOps : SlotOps StdOp where
  charge := StdOp.slot
  charge_injective := by intro a b h; simpa using h

/-! ## The storage currency -/

/-- One kind of storage cell, for a development that holds one structure.

A development holding two structures whose cells should be bounded separately
declares its own kind type: that is a genuine choice about what is being
counted, unlike the naming of an operation, which is not. -/
inductive Cell
  | cell
  deriving DecidableEq

namespace Cell

/-- INTERNAL: the currency is finite. -/
instance : Fintype Cell := Fintype.ofList [Cell.cell] (by intro k; cases k; simp)

end Cell

/-- One element of any roster occupies one `Cell`.  Low priority, so a
development that declares its own kinds wins. -/
instance (priority := low) stdRosterCells (ι : Type u) : RosterCells ι Cell :=
  ⟨Cell.cell⟩

/-! ## What a standard operation costs on the machine -/

/-- An implementation of the sealed carriers, described only by what its
operations cost in word operations.

`rate o` is the tally of machine operations one `o` performs and `bound` is a
uniform ceiling on it.  Nothing here says the implementation exists or is
correct; it says what it would cost, which is all `Charged.exchange` needs. -/
structure StdImpl where
  /-- What one standard operation costs, in word operations. -/
  rate : StdOp → CostVec Op
  /-- A uniform ceiling on the cost of a single operation. -/
  bound : ℕ
  /-- Every standard operation is within the ceiling. -/
  bound_ok : ∀ o, CostVec.steps CostModel.unitCost (rate o) ≤ bound

namespace StdImpl

/-- A witness that `StdImpl` is satisfiable: every operation is five loads.

This is not a claim that any structure achieves it.  It exists because a
hypothesis nothing can satisfy makes every theorem taking it vacuously true, and
`#print axioms` cannot detect that. -/
def trivial : StdImpl where
  rate := fun _ => CostVec.many .load 5
  bound := 5
  bound_ok := by intro o; simp [CostVec.steps_many]

end StdImpl

end Arlib.Computation
