/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation

/-!
# The standard currency, and what a program costs on the machine

`ArlibTest/Computation/Structures.lean` writes a development the way one is
written when it has an operation of its own: it declares a currency, names each
arlib operation in it, and pays for the naming table with a `charge_injective`.

This file writes the other case, which is the common one: a program **every one
of whose operations is already arlib's**.  It declares no currency, no storage
kinds and no instances — it writes `StdOp` and `Cell` and starts — and then it
asks the question the standard currency exists to answer: *what does this cost in
word operations?*

The answer is not one number, because it is not one machine.  The same tally,
exchanged at `StdImpl.listBacked` and at `StdImpl.balanced`, gives different word
counts, and the gap is the size of the structure.  That is what the size
parameter of `StdImpl.rate` is for, and this file is where it is exercised rather
than described.
-/

namespace ArlibTest.Standard

open Arlib.Computation

/-! ## A program with no currency of its own

Not a line of naming table: `StdOp` is the currency, `Cell` is the storage kind,
and `Arlib.Computation.Std` supplies every instance the operations ask for. -/

/-- INTERNAL: keep a key if it is even.  Arithmetic on a held value is not free,
so the test charges one `NumOp.cmp` — a standard operation, under the name
`Arlib.Computation.Std` supplies for it. -/
def keepEven (a : Fin 8) : Charged StdOp Cell Bool :=
  Charged.op (.num .cmp) (decide (a.val % 2 = 0))

/-- Insert four keys, then thin the roster down to the even ones. -/
def thin : Charged StdOp Cell (Roster (Fin 8)) := do
  let d ← Roster.insert 1 (Roster.empty : Roster (Fin 8))
  let d ← Roster.insert 2 d
  let d ← Roster.insert 3 d
  let d ← Roster.insert 4 d
  Roster.filterErase keepEven d

/-! Four insertions, four tests — one per element the pass visits — and **two**
erases, because two of the four keys are odd.  Nobody wrote the two: it is what
the pass did. -/
#guard thin.cost (.roster .insert) == 4
#guard thin.cost (.num .cmp) == 4
#guard thin.cost (.roster .erase) == 2
#guard Charged.steps (Rate.unit StdOp) thin == 10

/-- **And the two is derived, not observed.**  `Roster.cost_filterErase` reads
the deletion count off the pass, and the test's charge is exactly the hypothesis
it asks for. -/
example (d : Roster (Fin 8)) :
    (Roster.filterErase keepEven d : Charged StdOp Cell (Roster (Fin 8))).cost
      = CostVec.many (.num .cmp) d.card
        + CostVec.many (.roster .erase)
            (d.card - (d.toFinset.filter (fun x => (keepEven x).val)).card) :=
  Roster.cost_filterErase_card (.num .cmp) keepEven d (fun _ => rfl)

/-! And the pass gives cells back rather than taking them: the run peaks at the
four it inserted and ends holding two. -/
#guard thin.peakAt Cell.roster == 4
#guard thin.netAt Cell.roster == 2

/-! Each carrier has its own storage kind, so a roster's cells are not confused
with a queue's or a heap's — the reason `Cell` has four constructors and not
one. -/
#guard thin.peakAt Cell.queue == 0
#guard thin.peakAt Cell.heap == 0
#guard thin.peakAt Cell.dict == 0

/-! ## The same ten operations, on two machines

`10` is the honest count of standard operations, and on its own it is not a
running time.  What it costs depends on how a roster is represented, and that is
what `StdImpl` says.  The roster never holds more than four keys, so `4` is the
size the exchange is taken at. -/

/-- INTERNAL: the roster is a singly-linked list, so a membership test is a scan
and an erase is a scan followed by an unlink.  One operation against four
elements costs `3 * 4 + 1 + 1 = 14` word operations. -/
abbrev listy : StdImpl := StdImpl.listBacked 1

/-- INTERNAL: the roster is a balanced search tree, so a membership test is a
descent.  One operation against four elements costs
`3 * log₂ 5 + 1 + 1 = 3 * 2 + 2 = 8` word operations. -/
abbrev treey : StdImpl := StdImpl.balanced 1

#guard listy.ceiling 4 == 14
#guard treey.ceiling 4 == 8

/-! The same ten operations, re-priced.  The exchange is per-operation, so the
six that touch the roster pay the ceiling and the four comparisons — which are a
word of arithmetic on either machine — pay two. -/
#guard CostVec.steps CostModel.unitCost
    (CostVec.exchange (listy.atSize 4) thin.cost) == 92

#guard CostVec.steps CostModel.unitCost
    (CostVec.exchange (treey.atSize 4) thin.cost) == 56

/-! And both are under the crude bound `StdImpl.wordSteps_le` gives — ten
operations at the dearest rate — which is the form an asymptotic argument uses
when it does not want to know which operation was which. -/
example : CostVec.steps CostModel.unitCost
    (CostVec.exchange (listy.atSize 4) thin.cost)
      ≤ listy.ceiling 4 * Charged.steps (Rate.unit StdOp) thin :=
  listy.wordSteps_le 4 thin

#guard listy.ceiling 4 * Charged.steps (Rate.unit StdOp) thin == 140

/-! ### The gap is the point

At four keys the two differ by a factor under two, and reading anything into that
would be reading into a constant.  At sixty-four they differ by an order of
magnitude, and *that* is the claim a uniform `bound : ℕ` could not make: the
ceiling is a function of what the structure holds. -/

#guard listy.ceiling 64 == 194
#guard treey.ceiling 64 == 20

#guard treey.ceiling 64 < listy.ceiling 64

/-- **And the ordering is a theorem, not an arithmetic accident**: the tree is
never dearer than the list, at any size, because a descent is never longer than
a pass. -/
example (n : ℕ) : treey.ceiling n ≤ listy.ceiling n :=
  StdImpl.ceiling_balanced_le_listBacked 1 n

/-! ## What a thinning pass really costs

`Roster.cost_filterErase` says a pass over `d` elements charges one test per
element and one erase per rejection — at most `2 * d` standard operations, and
that count is honest.  On a list-backed roster each of those is itself a pass, so
the pass is quadratic; on a tree it is `n log n`.  Neither number is written
down anywhere: both are the `2 * n` operations multiplied by a ceiling that knows
the size. -/

example (n : ℕ) (p : Charged StdOp Cell (Roster (Fin 8)))
    (hp : Charged.steps (Rate.unit StdOp) p ≤ 2 * n) :
    Charged.steps CostModel.unitCost (Charged.exchange (listy.atSize n) p)
      ≤ (3 * n + 1 + 1) * (2 * n) :=
  StdImpl.listBacked_thin_wordSteps_le 1 n p hp

example (n : ℕ) (p : Charged StdOp Cell (Roster (Fin 8)))
    (hp : Charged.steps (Rate.unit StdOp) p ≤ 2 * n) :
    Charged.steps CostModel.unitCost (Charged.exchange (treey.atSize n) p)
      ≤ (3 * Nat.log 2 (n + 1) + 1 + 1) * (2 * n) :=
  StdImpl.balanced_thin_wordSteps_le 1 n p hp

/-! ## The seal

`StdImpl` prices operations; it cannot price them at nothing. -/

/-! **No free implementation.**  `one_le_bound` is the field that rejects it, and
it is the `StdImpl` counterpart of `Rate.one_le`: without it there is a legal
implementation under which every carrier operation is free, and every bound
carried across `exchange` collapses to zero.  The test passes when the goal it
leaves behind is the one below. -/
/--
error: unsolved goals
o : StdOp
s : ℕ
⊢ 1 ≤ 0
-/
#guard_msgs in
example : StdImpl where
  rate := fun _ _ => 0
  bound := fun _ _ => 0
  bound_ok := by intro o s; simp
  bound_mono := fun _ => monotone_const
  one_le_bound := by intro o s

/-- **The size ceiling is a claim about the run, and it has to be discharged.**
`atSize n` prices the run as though no carrier ever held more than `n`;
`size_le_of_peak_le` is what proves that from the run's profile, for every
prefix and not merely at the end. -/
example (s₀ n : ℕ) (pre post : Profile Cell)
    (h : (s₀ : ℤ) + (pre * post).peak Cell.roster ≤ (n : ℤ)) :
    (s₀ : ℤ) + pre.net Cell.roster ≤ (n : ℤ) :=
  size_le_of_peak_le Cell.roster s₀ n pre post h

end ArlibTest.Standard
