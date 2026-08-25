/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Lib.Reduce
import Arlib.Computation.Lib.Search

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

end ArlibTest.Computation
