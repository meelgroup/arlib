/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
import Arlib.Computation.Space
import Arlib.Computation.Charged
import Arlib.Computation.ChargedPMF
import Arlib.Computation.Roster
import Arlib.Computation.Dict
import Arlib.Computation.Heap
import Arlib.Computation.Rand
import Arlib.Computation.Num
import Arlib.Computation.Queue
import Arlib.Computation.Slot
import Arlib.Computation.Std
import Arlib.Computation.Machine
import Arlib.Computation.Loop
import Arlib.Computation.Data
import Arlib.Computation.Lib.Arr
import Arlib.Computation.Lib.Reduce
import Arlib.Computation.Lib.Search
import Arlib.Computation.Lib.Sort
import Arlib.Computation.Footprint

/-!
# Arlib.Computation

**A model of computation, so that a running-time claim can be about something.**

Everywhere else in the library an algorithm's cost is a number its author
supplies. `Arlib.Approximation` says so at length: `RandAlg α β := α → PMF
(β × ℕ)` records a step count that nothing relates to work done, and
`IsFPRAS.pinnedTime_of_cost_zero` proves that the algorithm reporting zero steps
satisfies every running-time clause in the area. This area is the other half: a
machine, a language written against it, and a time operator that computes an
algorithm's cost from its text rather than accepting it from its author.

## The shape of it

* `Computation/Charged.lean` — `Charged κ α`, a value paired with the tally that
  produced it, for algorithms written against an abstract interface rather than
  against words. Same discipline, no machine: the constructor is private, so the
  only ways to build one are `pure`, `bind` and one operation at a time.
* `Computation/Roster.lean` — `Roster ι`, a sealed finite set with charged
  operations, including `filterErase`, one pass whose deletion count is read off
  the pass rather than supplied. This is the data seal that makes `Charged` bite.
  Its operations take no opcode and no storage kind: `RosterOps` and `RosterCells`
  say what a development *calls* an erase and a cell, and this module fixes what
  each one *is* — one charge per call, one cell per element. A development
  declares the cost of its own operations, which is all it is in a position to
  know; it does not get to price an erase.
* `Computation/Dict.lean` — `Dict ι α`, a sealed finite map: keys with values
  behind them, and a charged `find`. A `Roster` stores membership alone, so
  anything with values — a table of counts, a memo — belongs here. There is no
  `modify`: changing the value at a key is a `find` and an `insert`.
* `Computation/Heap.lean` — `Heap α`, a sealed leftist priority queue, whose
  operations are not constant-time. The merge charges one `HeapOp.cmp` per key
  comparison it performs, and `Heap.rank_le_log`, `Heap.steps_push_le` and
  `Heap.steps_pop_le` bound that count by `log₂ (n + 1)`.
* `Computation/Space.lean` — `Residency` and `Profile`, the algebra of a
  resource that is *given back*.  Time is a commutative monoid under `+`; space
  is a `(net, peak)` pair whose composition is a `max`, and the two are not the
  same shape.  `peak_foldProfiles_le` is the lemma with no time-side counterpart:
  a loop that keeps itself below a ceiling stays below it however long it runs,
  because residency is a property of the state and an invariant can cap it, while
  time is cumulative and no invariant can.  See
  `docs/dev/Space-Modelling-Design.md`.
* `Computation/Rand.lean` — `Block`, `Coins` and `Sampler`: the randomness a
  sampling algorithm consumes, sealed the same way its data is. A bare
  `bits : Fin n → Bool` is a free oracle and a bare `level : ℕ` is a free read;
  `Sampler` is the cut that removes both, because a rate `2⁻ˡ` is the object the
  algorithm actually has and its level never leaves the structure.
* `Computation/Slot.lean` — `Slot α`, the answer register, and the last
  `Charged.op` a streaming algorithm needs.
* `Computation/Num.lean` — `Num α`, a sealed number, and `Num.iterate`, the loop
  whose length the algorithm itself computed. Arithmetic on held values is free
  in Lean, and a paper's pseudocode is full of it: `Y ← Y + 1`, `⌈Σ/max⌉`,
  `(Y/t)·Σ` are three lines of one Karp–Luby estimator.
* `Computation/Queue.lean` — `Queue ι`, a sealed FIFO with a destructive charged
  `dequeue`. A `Roster` is a set: no order, no consumption, and no way to say that
  a sample list ran out.
* `Computation/Cost.lean` — `Op`, the primitive operations; `CostVec κ`, a tally
  of work in a currency `κ`; `Rate κ`, a charge per operation with every entry at
  least one; and `CostVec.steps`, which turns a tally into a number. Costs are
  *vectors* so that a program accumulates what it did and the price is applied
  once, at the end. The currency is a parameter because word operations are not
  the only unit worth counting.
* `Computation/Machine.lean` — `Word`, `RamState`, the `RAM` monad, the
  primitives, and `RAM.cost`, the time operator. One module, because the seal
  below is file-scoped.
* `Computation/Loop.lean` — bounded iteration and the two lemmas every cost bound
  goes through.
* `Computation/Data.lean` — `HoldsList`, which lets a postcondition speak about a
  Mathlib `List` rather than about cells.
* `Computation/Lib/` — the subroutines: `arrFill`, `arrSum`, `arrMax`, `binSearch`, `mergeSortRam`.

## What makes the cost honest

An algorithm here is an ordinary Lean function, which invites the objection that
a Lean function computes anything for free. Three things answer it, and two are
checked by the compiler:

1. `Word` has a private constructor and field and carries no arithmetic or order
   instances, so `x + y` and `if x < y` do not elaborate.
2. `RAM` has a private constructor, so no client can build a program except from
   the primitives and the monad operations.
3. `Word.toNat` — the view a specification needs — is `noncomputable`, so a
   program that inspects a word without a primitive **fails to compile**.

The abstract half is sealed the same way. `Charged.val` is `noncomputable`, so
`pure p.val` cannot copy a program's result and drop its charges; `Roster`'s
contents, its size and the conversion from a `Finset` are all `noncomputable`, so
outside `Roster.lean` the only thing one can do with a roster is call a charged
operation on it.

`ArlibTest/Computation.lean` §3 and §8 test all of this by writing the cheats and
checking they are rejected.

## What is not claimed

Three things, stated here rather than discovered later.

**The cost table is declared.** `Op` and its charges are asserted to be what a
machine does; there is no machine underneath them and no compilation theorem.
This is a smaller debt than the one the area exists to close — a caller supplies
`RandAlg`'s number once per algorithm, while this table is fixed, small and
inspectable, and every bound in the library is derived from it — but it is a
debt.

**Adequacy is not proved.** That this model's polynomial time is Turing-machine
polynomial time is what licenses reading a bound here as a complexity claim in
the usual sense. It is stated, not proved, and no theorem depends on it.

**One route past the seal is open.** `Word.casesOn` — and likewise `Roster.casesOn`
and `Charged.casesOn` — is generated public and is compiled, so a determined
author can project the field out. It is greppable, it is what
`scripts/ComputationAudit.lean` looks for, and for `Word` its worst case is a
constant factor: what leaks is the contents of words already in hand, on which
the primitives are unit-cost anyway, while memory stays unreachable without
`load`. For `Roster` it is not bounded that way, which is why the audit is the
answer rather than a shrug.

**`#print axioms` gives no signal here** once the randomised layer lands, because
`PMF` pulls `Classical.choice`. A clean audit is not evidence.

## Conventions the area commits to

* **Cost is derived, never written.** No tick, no annotation, no cost argument.
* **Explicit bounds, never asymptotics**, per `CONVENTIONS.md` §5. Each entry
  states its cost twice: symbolically in the `CostModel`, so it survives a change
  to the instruction set, and as a numeral under `CostModel.unitCost`.
* **Every entry states its correctness against Mathlib**, joined to the machine
  by `HoldsList`.

See `docs/dev/Computation-ROADMAP.md` for the design, the alternatives that were
rejected, and the prior art.
-/
