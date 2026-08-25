/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
import Arlib.Computation.Charged
import Arlib.Computation.Dict
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
* `Computation/Dict.lean` — `Dict ι`, a sealed finite set with charged
  operations, including `filterErase`, one pass whose deletion count is read off
  the pass rather than supplied. This is the data seal that makes `Charged` bite.
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
`pure p.val` cannot copy a program's result and drop its charges; `Dict`'s
contents, its size and the conversion from a `Finset` are all `noncomputable`, so
outside `Dict.lean` the only thing one can do with a dictionary is call a charged
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

**One route past the seal is open.** `Word.casesOn` — and likewise `Dict.casesOn`
and `Charged.casesOn` — is generated public and is compiled, so a determined
author can project the field out. It is greppable, it is what
`scripts/ComputationAudit.lean` looks for, and for `Word` its worst case is a
constant factor: what leaks is the contents of words already in hand, on which
the primitives are unit-cost anyway, while memory stays unreachable without
`load`. For `Dict` it is not bounded that way, which is why the audit is the
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
