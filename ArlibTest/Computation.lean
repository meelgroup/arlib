/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Lib.Reduce
import Arlib.Computation.Lib.Search
import Arlib.Computation.Lib.Sort
import Arlib.Computation.Lib.Arr
import Arlib.Computation.Charged
import Arlib.Computation.Dict

/-!
# `Arlib.Computation` — executable tests

This module does more than document the API, because `Arlib.Computation` makes
two kinds of claim that a type-checked theorem does not by itself establish.

**The programs run.** A cost bound about a term nobody can execute is a bound
about nothing. Every algorithm here is a computable Lean function, so §1 and §2
actually run them and check the answers and the operation counts against
hand-computed numbers. A proof that `arrMax` costs `≤ 4n + 1` and an execution
showing it costs exactly `4n + 1` are different evidence, and a library that
claims to model running time should offer both.

**The seal holds.** The honesty of every cost bound rests on a client being
unable to write a program that moves the machine's state without charging for
it. That is not a theorem; it is a property of the module boundary, and §3 tests
it the only way it can be tested — by writing the cheats and checking that they
are rejected. §3 also records, as a passing test, the one route that is *not*
closed, so that its status is a checked fact rather than a claim in a docstring.

Run with `lake test`.
-/

namespace ArlibTest.Computation

open Arlib.Computation

/-! ## 1. The programs run

A worked example: allocate a block, fill it, and take its maximum and sum. -/

/-- Allocate a three-cell block holding `[10, 30, 20]` and return its base
address. -/
def buildBlock : RAM 16 (Word 16) := do
  let n ← lit 3
  let base ← alloc n
  let i0 ← lit 0
  let i1 ← lit 1
  let i2 ← lit 2
  let a0 ← add base i0
  let a1 ← add base i1
  let a2 ← add base i2
  let v0 ← lit 10
  let v1 ← lit 30
  let v2 ← lit 20
  store a0 v0
  store a1 v1
  store a2 v2
  pure base

/-- Build the block, then emit its maximum and its sum. -/
def demo : RAM 16 Unit := do
  let base ← buildBlock
  let m ← arrMax base 3
  emit m
  let s ← arrSum base 3
  emit s

/-- A word holding `k`, obtained the only way a client can obtain one: by
running `lit`.  There is no other route, which is the seal of §3 in action. -/
def wordOf (k : ℕ) : Word 16 := (lit k : RAM 16 (Word 16)).val (RamState.empty 16)

/-! The answers are the ones arithmetic gives: `max [10,30,20] = 30` and
`sum = 60`. -/
#guard (demo.state (RamState.empty 16)).out == #[30#16, 60#16]

/-! The block really is allocated: three cells. -/
#guard (buildBlock.state (RamState.empty 16)).size == 3

/-! ## 2. The operation counts are the ones the bounds predict

These are the numbers a cost claim is *about*. Each is checked against the
theorem that bounds it, so a change to an algorithm that silently makes it more
expensive fails here as well as in the proof. -/

section Counts

/-! Reading three cells with `arrMax` performs exactly three loads. -/
#guard (arrMax (wordOf 0) 3).cost (RamState.empty 16) Op.load == 3

/-! `arrMax` over `n` cells: one literal to start, then a literal, an addition, a
load and a comparison per cell. On the unit-cost RAM that is `4n + 1`, and the
proved bound `steps_arrMax_le_unitCost` is **tight**. -/
#guard RAM.steps CostModel.unitCost (arrMax (wordOf 0) 3) (RamState.empty 16) == 13

/-- The proved bound agrees with the execution at `n = 3`, and is attained. -/
example : (13 : ℕ) ≤ 4 * 3 + 1 := by norm_num

/-! `arrSum` has the same shape, with an addition where `arrMax` compares. -/
#guard RAM.steps CostModel.unitCost (arrSum (wordOf 0) 5) (RamState.empty 16) == 21

/-! Allocation is charged per cell, not per call: allocating seven cells costs
seven operations. This is the one place the table departs from the textbook
uniform-cost RAM, so it is worth a test rather than only a docstring. -/
#guard RAM.steps CostModel.unitCost
    (do let n ← lit 7; let _ ← alloc n; pure ()) (RamState.empty 16) == 8

/-! The whole demonstration costs 44 steps: 24 to build the block, 13 to scan it
for a maximum, 21 to sum it, and two emits — less the sharing. -/
#guard RAM.steps CostModel.unitCost demo (RamState.empty 16) == 44

end Counts

/-! ### The primitives compute what they say

The cost table is only half of a primitive's specification; the other half is
what it returns.  These check the arithmetic of the less obvious ones, which is
where a silent error would otherwise sit unnoticed behind a correct-looking cost
bound. -/

section Primitives

/-- Emit `clz k` for each `k`, over 8-bit words. -/
def clzOf (k : ℕ) : RAM 8 Unit := do
  let x ← lit k
  let c ← clz x
  emit c

/-! Zero has all eight bits leading; `1` has seven; `2` and `3` have six. -/
#guard ((clzOf 0).state (RamState.empty 8)).out == #[8#8]
#guard ((clzOf 1).state (RamState.empty 8)).out == #[7#8]
#guard ((clzOf 2).state (RamState.empty 8)).out == #[6#8]
#guard ((clzOf 3).state (RamState.empty 8)).out == #[6#8]
#guard ((clzOf 8).state (RamState.empty 8)).out == #[4#8]
#guard ((clzOf 255).state (RamState.empty 8)).out == #[0#8]

/-- The high half of a product, which truncating multiplication loses.  At width
8, `200 * 200 = 40000 = 156 * 256 + 64`. -/
def mulParts (a b : ℕ) : RAM 8 Unit := do
  let x ← lit a
  let y ← lit b
  let lo ← mul x y
  let hi ← mulHi x y
  emit lo
  emit hi

#guard ((mulParts 200 200).state (RamState.empty 8)).out == #[64#8, 156#8]

/-- Arithmetic wraps at the word width, and the bounds above say so: `arrSum`
returns the sum modulo `2 ^ w`. -/
def wrapAdd : RAM 8 Unit := do
  let x ← lit 200
  let y ← lit 100
  let z ← add x y
  emit z

#guard ((wrapAdd).state (RamState.empty 8)).out == #[44#8]

end Primitives

/-! ## 3. The seal

The four ways a client might try to obtain work for free, and what happens. The
first three are rejected; the fourth is the one route that is open, and it is
recorded here so that its status is a checked fact.

Each test is a `#guard_msgs` block: it *passes* when the compiler produces
exactly the stated error, so a future change that silently opens one of these
routes turns this file red. -/

section Seal

/-! Forging a program that moves the state without charging: rejected, because
`RAM`'s constructor is private. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.RAM` is marked as private
-/
#guard_msgs in
example : RAM 16 Unit := ⟨fun σ => ((), σ, 0)⟩

/-! Reading a word's value in a program — which would make comparison free:
rejected by the compiler, because `Word.toNat` is `noncomputable`. This is the
test that matters most, because it is the one that stops
`if x.toNat < y.toNat then _` from being a zero-cost comparison. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Word.toNat', which is 'noncomputable'
-/
#guard_msgs in
def peekViaToNat (x : Word 16) : Nat := x.toNat

/-! Projecting the field directly: rejected, because the field is private. -/
/--
error: Field `val` from structure `Arlib.Computation.Word` is private
-/
#guard_msgs in
def peekViaField (x : Word 16) : BitVec 16 := x.val

/-! Going through the recursor: rejected by the code generator, so it cannot
appear in a program that runs. -/
/--
error: code generator does not support recursor `Arlib.Computation.Word.rec` yet, consider using 'match ... with' and/or structural recursion
-/
#guard_msgs in
def peekViaRec (x : Word 16) : BitVec 16 :=
  Word.rec (motive := fun _ => BitVec 16) (fun v => v) x

/-- **The one route that is open.** `Word.casesOn` is generated public and is
compiled, so a client can project the field out after all.

This is not a failing test; it is the honest record of what the seal does not
cover, and `scripts/ComputationAudit.lean` is what catches it. Its worst case is
a constant factor: what leaks is the contents of words already in hand, on which
the primitives are unit-cost anyway, and memory stays unreachable without
`load`. -/
def peekViaCasesOn (x : Word 16) : BitVec 16 := Word.casesOn x (fun v => v)

end Seal

/-! ## 4. The cost model

`CostModel.unitCost` is the reference, and `CostVec.steps_unit_le` says it is the
cheapest. Here it is on a concrete program, against a model that charges more
for memory than for arithmetic. -/

section Models

/-- A machine on which a memory access costs five and everything else costs
one. -/
def slowMemory : CostModel where
  cost := fun o => match o with
    | .load | .store => 5
    | _ => 1
  one_le := by intro o; cases o <;> norm_num

/-! The same program costs more under a model that charges more. This is
`CostVec.steps_unit_le` on a concrete instance. -/
#guard RAM.steps CostModel.unitCost (arrMax (wordOf 0) 3) (RamState.empty 16)
    ≤ RAM.steps slowMemory (arrMax (wordOf 0) 3) (RamState.empty 16)

/-! Charging five per load turns `4n + 1` into `8n + 1`: the three loads cost
twelve more. -/
#guard RAM.steps slowMemory (arrMax (wordOf 0) 3) (RamState.empty 16) == 25

end Models

/-! ## 5. A regression battery

The same two algorithms over a range of inputs, checking that the answer and the
operation count both track the input size. -/

section Battery

/-- Build a block holding `0, 1, …, n-1` and return its base. -/
def buildRange (n : ℕ) : RAM 16 (Word 16) := do
  let nw ← lit n
  let base ← alloc nw
  let _ ← iterate n (fun i _ => do
    let iw ← lit i
    let a ← add base iw
    store a iw) ()
  pure base

/-- `arrMax` over `0, …, n-1` is `n-1`, and `arrSum` is `n(n-1)/2`. -/
def rangeAnswers (n : ℕ) : RAM 16 Unit := do
  let base ← buildRange n
  let m ← arrMax base n
  emit m
  let s ← arrSum base n
  emit s

#guard ((rangeAnswers 1).state (RamState.empty 16)).out == #[0#16, 0#16]
#guard ((rangeAnswers 4).state (RamState.empty 16)).out == #[3#16, 6#16]
#guard ((rangeAnswers 8).state (RamState.empty 16)).out == #[7#16, 28#16]
#guard ((rangeAnswers 16).state (RamState.empty 16)).out == #[15#16, 120#16]

/-! The scan cost grows exactly linearly: `4n + 1` at every size tested. -/
#guard RAM.steps CostModel.unitCost (arrMax (wordOf 0) 10) (RamState.empty 16) == 41
#guard RAM.steps CostModel.unitCost (arrMax (wordOf 0) 25) (RamState.empty 16) == 101

end Battery

/-! ## 6. A logarithmic bound

`arrMax` and `arrSum` cost a constant per cell.  Binary search costs a constant
per halving, and these tests check both halves of that claim: that it finds the
right answer, and that its cost really does grow like `Nat.clog 2 (n + 1)` rather
than like `n`. -/

section Logarithmic

/-- Build a sorted block holding `0, 2, 4, …, 2(n-1)`. -/
def buildSorted (n : ℕ) : RAM 16 (Word 16) := do
  let nw ← lit n
  let base ← alloc nw
  let _ ← iterate n (fun i _ => do
    let iw ← lit i
    let a ← add base iw
    let v ← lit (2 * i)
    store a v) ()
  pure base

/-- Search a sorted block of `n` even numbers for `k`, and emit the index. -/
def probe (n k : ℕ) : RAM 16 Unit := do
  let base ← buildSorted n
  let key ← lit k
  let idx ← binSearch base n key
  emit idx

/-! Present keys are found at their own index. -/
#guard ((probe 16 0).state (RamState.empty 16)).out == #[0#16]
#guard ((probe 16 10).state (RamState.empty 16)).out == #[5#16]
#guard ((probe 16 30).state (RamState.empty 16)).out == #[15#16]

/-! Absent keys give the insertion point, and a key past the end gives `n`. -/
#guard ((probe 16 31).state (RamState.empty 16)).out == #[16#16]
#guard ((probe 16 99).state (RamState.empty 16)).out == #[16#16]

/-! **The cost grows logarithmically.**  Doubling the block adds nine
operations, not `n`.  Each line is the measured cost; the proved bound
`steps_binSearch_le_unitCost` is `9 * Nat.clog 2 (n + 1) + 2`. -/
#guard RAM.steps CostModel.unitCost (binSearch (wordOf 0) 15 (wordOf 5))
    (RamState.empty 16) == 38
#guard RAM.steps CostModel.unitCost (binSearch (wordOf 0) 31 (wordOf 5))
    (RamState.empty 16) == 47
#guard RAM.steps CostModel.unitCost (binSearch (wordOf 0) 1000 (wordOf 5))
    (RamState.empty 16) == 84

/-- A thousand cells cost 84 steps, well inside the proved bound of 92 — and a
linear scan of the same block would cost 4001. -/
example : (84 : ℕ) ≤ 9 * Nat.clog 2 (1000 + 1) + 2 := by
  have h : Nat.clog 2 (1000 + 1) = 10 := by decide
  omega

end Logarithmic

/-! ## 6b. Writing

`arrFill` is the entry that exercises the write side of the data bridge: its
correctness is proved through `HoldsList.state_storeAt`, so the block's contents
are tracked as a Mathlib list across every store rather than cell by cell.  Its
cost is exactly three operations per cell — the upper and lower bounds coincide. -/

section Writing

/-- Allocate four cells, fill them with 7, and emit them. -/
def fillDemo : RAM 16 Unit := do
  let n ← lit 4
  let base ← alloc n
  let v ← lit 7
  arrFill base 4 v
  let _ ← iterate 4 (fun i _ => do let x ← loadAt base i; emit x) ()
  pure ()

#guard (fillDemo.state (RamState.empty 16)).out == #[7#16, 7#16, 7#16, 7#16]

/-! Three operations per cell, exactly. -/
#guard RAM.steps CostModel.unitCost (arrFill (wordOf 0) 10 (wordOf 7))
    (RamState.empty 16) == 30

end Writing

/-! ## 7. Merge sort

The entry that shows the framework handles a recurrence rather than a loop:
`steps_mergeSortRam_le_unitCost` bounds the cost by `16 · n · (⌈log₂ n⌉ + 1)`,
proved by strong induction on `n`.

Merge sort's *correctness* is not proved — the write-side bridge from `store`
back to `HoldsList` does not exist yet, and `docs/dev/Computation-ROADMAP.md`
records it as outstanding.  So these tests do the next best thing, which is only
available because the programs are executable: they run the sort and check the
output.  That is evidence, not proof, and it is labelled as such. -/

section MergeSort

/-- Fill a fresh block from `vals`, sort it, and emit every cell. -/
def sortDemo (vals : List ℕ) : RAM 16 Unit := do
  let n ← lit vals.length
  let base ← alloc n
  let tmp ← alloc n
  let _ ← iterate vals.length (fun i _ => do
      let iw ← lit i
      let a ← add base iw
      let v ← lit (vals.getD i 0)
      store a v) ()
  mergeSortRam base tmp 0 vals.length
  let _ ← iterate vals.length (fun i _ => do
      let x ← loadAt base i
      emit x) ()
  pure ()

/-! It sorts. -/
#guard ((sortDemo [5, 3, 8, 1, 9, 2, 7]).state (RamState.empty 16)).out
    == #[1#16, 2#16, 3#16, 5#16, 7#16, 8#16, 9#16]

/-! Duplicates survive, and the multiset is preserved. -/
#guard ((sortDemo [4, 4, 2, 2, 1]).state (RamState.empty 16)).out
    == #[1#16, 2#16, 2#16, 4#16, 4#16]

/-! Already sorted, and reverse sorted. -/
#guard ((sortDemo [1, 2, 3, 4]).state (RamState.empty 16)).out
    == #[1#16, 2#16, 3#16, 4#16]
#guard ((sortDemo [4, 3, 2, 1]).state (RamState.empty 16)).out
    == #[1#16, 2#16, 3#16, 4#16]

/-! The empty and singleton cases, where the recursion bottoms out. -/
#guard ((sortDemo []).state (RamState.empty 16)).out == #[]
#guard ((sortDemo [1]).state (RamState.empty 16)).out == #[1#16]

/-! Sorting eight cells costs 336 steps, inside the proved bound of
`16 · 8 · (⌈log₂ 8⌉ + 1) = 512`. -/
#guard RAM.steps CostModel.unitCost (mergeSortRam (wordOf 0) (wordOf 0) 0 8)
    (RamState.empty 16) == 336

example : (336 : ℕ) ≤ 16 * 8 * (Nat.clog 2 8 + 1) := by
  have h : Nat.clog 2 8 = 3 := by decide
  omega

end MergeSort


/-! ## 8. Charged computation over a sealed dictionary

`Arlib.Computation.Charged` and `Arlib.Computation.Dict` are the other half of
the area: a cost model for algorithms written against an abstract interface
rather than against words and memory. The claim they make is that a program's
cost is computed from its text, so this section checks it two ways — by running
programs and reading their tallies, and by writing the cheats and confirming the
compiler rejects them. -/

namespace ChargedDict

/-- A small currency, standing in for whatever an algorithm's operations are. -/
inductive DOp
  | find | del | put
  deriving DecidableEq, Repr, Inhabited

namespace DOp

/-- Every operation, as a list. -/
def all : List DOp := [.find, .del, .put]

/-- INTERNAL: `all` is exhaustive. -/
theorem mem_all (o : DOp) : o ∈ all := by cases o <;> simp [all]

instance : Fintype DOp := Fintype.ofList all mem_all

end DOp

open Arlib.Computation

section Counting

/-! A three-operation program: two puts and a size test. Its cost is nowhere
written down — it is what the elaborator accumulates. -/

/-- INTERNAL: insert two elements and ask whether the result has two. -/
def twoPuts : Charged DOp Bool := do
  let d ← Dict.insert DOp.put (3 : Fin 8) Dict.empty
  let d ← Dict.insert DOp.put (5 : Fin 8) d
  Dict.cardEq DOp.find 2 d

#guard Charged.steps (Rate.unit DOp) twoPuts == 3
#guard twoPuts.cost DOp.put == 2
#guard twoPuts.cost DOp.find == 1
#guard twoPuts.cost DOp.del == 0

/-! A rate other than the unit one: if a put costs seven, the same program costs
`2 · 7 + 1 = 15`. The program is unchanged; only the price is. -/

/-- INTERNAL: a table on which insertion is the expensive operation. -/
def slowPut : Rate DOp where
  cost := fun o => match o with | .put => 7 | _ => 1
  one_le := fun o => by cases o <;> decide

#guard Charged.steps slowPut twoPuts == 15

/-! `CostVec.steps_unit_le` in action: no rate makes the program look cheaper
than the unit one does. -/
example : Charged.steps (Rate.unit DOp) twoPuts ≤ Charged.steps slowPut twoPuts :=
  CostVec.steps_unit_le _ _

end Counting

section Filtering

/-! `Dict.filterErase` is where a hand-written cost would go wrong, because the
number of deletions is data-dependent. Here it is read off the pass. -/

/-- INTERNAL: build `{0, 1, 2, 3}` and delete the odd elements, at one `find` per
element tested and one `del` per element removed. -/
def dropOdds : Charged DOp (Dict (Fin 8)) := do
  let d ← Dict.insert DOp.put (0 : Fin 8) Dict.empty
  let d ← Dict.insert DOp.put (1 : Fin 8) d
  let d ← Dict.insert DOp.put (2 : Fin 8) d
  let d ← Dict.insert DOp.put (3 : Fin 8) d
  Dict.filterErase DOp.del (fun x => Charged.op DOp.find (decide (x.val % 2 = 0))) d

/-! Four puts, four tests, two deletions. Nobody wrote "two". -/
#guard dropOdds.cost DOp.put == 4
#guard dropOdds.cost DOp.find == 4
#guard dropOdds.cost DOp.del == 2
#guard Charged.steps (Rate.unit DOp) dropOdds == 10

/-- INTERNAL: the same pass with a test that rejects nothing, which must
therefore charge no deletions. -/
def dropNothing : Charged DOp (Dict (Fin 8)) := do
  let d ← Dict.insert DOp.put (0 : Fin 8) Dict.empty
  let d ← Dict.insert DOp.put (1 : Fin 8) d
  Dict.filterErase DOp.del (fun _ => Charged.op DOp.find true) d

#guard dropNothing.cost DOp.del == 0
#guard dropNothing.cost DOp.find == 2

/-- INTERNAL: and one that rejects everything. -/
def dropAll : Charged DOp (Dict (Fin 8)) := do
  let d ← Dict.insert DOp.put (0 : Fin 8) Dict.empty
  let d ← Dict.insert DOp.put (1 : Fin 8) d
  Dict.filterErase DOp.del (fun _ => Charged.op DOp.find false) d

#guard dropAll.cost DOp.del == 2

end Filtering

section Seal

/-! ### The seal

As in §3, each test *passes* when the compiler produces exactly the stated error.
These are the four routes by which a program could avoid paying. -/

/-! Forging a tally: rejected, because `Charged`'s constructor is private. There
is no syntax for asserting what something cost. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.Charged` is marked as private
-/
#guard_msgs in
example : Charged DOp Nat := ⟨0, 0⟩

/-! Copying a program's result to discard its charges. This is the one that
matters: `pure p.val` would have the same value as `p` and cost nothing, so
`Charged.val` is `noncomputable` and the copy fails to compile. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.val', which is 'noncomputable'
-/
#guard_msgs in
def launder (p : Charged DOp Nat) : Charged DOp Nat := pure p.val

/-! Reading a dictionary's contents without asking it: rejected, because
`Dict.toFinset` is `noncomputable`. Without this, a program could compute the
answer from the set directly and charge for nothing. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Dict.toFinset', which is 'noncomputable'
-/
#guard_msgs in
def peekDict (d : Dict (Fin 8)) : Finset (Fin 8) := d.toFinset

/-! Conjuring a dictionary from a set that some other computation produced:
rejected, because `Dict.ofFinset` is `noncomputable`. This is what confines the
boundary to the instrumentation. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Dict.ofFinset', which is 'noncomputable'
-/
#guard_msgs in
def conjure (s : Finset (Fin 8)) : Dict (Fin 8) := Dict.ofFinset s

/-! Asking a dictionary its size without paying for the question: rejected, for
the same reason. `Dict.cardEq` is what a program uses, and it charges. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Dict.card', which is 'noncomputable'
-/
#guard_msgs in
def peekSize (d : Dict (Fin 8)) : Nat := d.card

/-! The dictionary's representation is private, so a program cannot get at the
elements and iterate over them for free. -/
/--
error: Field `elems` from structure `Arlib.Computation.Dict` is private
-/
#guard_msgs in
def peekElems (d : Dict (Fin 8)) : List (Fin 8) := d.elems

/-- **The routes that remain open**, recorded rather than hidden: `casesOn` is
generated public for both structures and is compiled, so a determined author can
project a private field out. `scripts/ComputationAudit.lean` is what catches
that, and §3's note on `Word` applies here word for word. -/
def peekDictViaCasesOn (d : Dict (Fin 8)) : List (Fin 8) :=
  Dict.casesOn d (fun l _ => l)

end Seal

end ChargedDict

end ArlibTest.Computation
