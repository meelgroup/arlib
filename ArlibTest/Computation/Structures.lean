/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation

/-!
# The two structures that are not sets

`ArlibTest/Computation.lean` exercises `Roster`, which stores membership and
nothing else.  This file exercises the two structures a development reaches for
when membership is not enough:

* `Dict ι α` — a finite **map**.  The worked example is a table of counts, and it
  shows the rule that a development notices first: there is no `modify`, so
  `Y[k] ← Y[k] + 1` is a `find` and an `insert`, and both are charged.
* `Heap α` — a **priority queue**, and the first structure here whose operations
  are not constant-time.  The worked example builds a heap of four elements and
  asks what it cost; the answer, **three comparisons**, is not a number anyone
  wrote down — it is what the merges did, and `#guard` runs them.
-/

namespace ArlibTest.Structures

open Arlib.Computation

/-! ## A table of counts

The currency has six constructors and **five of them name an arlib operation**.
`report` is the development's own — whatever it does with a finished table — and
it is the only one this development is in a position to price. -/

/-- A currency for a program that keeps a table. -/
inductive TOp
  | find | put | del | size | card
  | report
  deriving DecidableEq, Repr, Inhabited

namespace TOp

/-- Every operation, as a list. -/
def all : List TOp := [.find, .put, .del, .size, .card, .report]

/-- INTERNAL: `all` is exhaustive. -/
theorem mem_all (o : TOp) : o ∈ all := by cases o <;> simp [all]

instance : Fintype TOp := Fintype.ofList all mem_all

end TOp

/-- INTERNAL: the storage currency — one cell per table entry. -/
inductive TKind | entry deriving DecidableEq
instance : Fintype TKind := Fintype.ofList [.entry] (by intro k; cases k; simp)

/-- One entry of a `Fin 8 ↦ ℕ` table occupies one `entry`.  Declared once, from
the data, rather than named at each call. -/
instance : DictCells (Fin 8) ℕ TKind := ⟨TKind.entry⟩

/-- What this currency *calls* each standard map operation.  Not a price: what a
`find` costs is fixed in `Arlib.Computation.Dict`. -/
instance : DictOps TOp where
  charge
    | .find => .find
    | .insert => .put
    | .erase => .del
    | .size => .size
    | .cardEq => .card
  charge_injective := by decide

/-- **The line a counter table is made of.**

`Y[k] ← Y[k] + 1` is two operations here, and that is the module's design showing
through: an in-place `modify` taking `fun v => v + 1` would apply the caller's
function to the stored value at the price of one operation, and the caller's
function is not something arlib can price. -/
def bumpAt (k : Fin 8) (d : Dict (Fin 8) ℕ) : Charged TOp TKind (Dict (Fin 8) ℕ) := do
  let cur ← Dict.find k d
  Dict.insert k (cur.getD 0 + 1) d

/-- INTERNAL: three increments over two keys. -/
def tally : Charged TOp TKind (Dict (Fin 8) ℕ) := do
  let d ← bumpAt 3 Dict.empty
  let d ← bumpAt 5 d
  bumpAt 3 d

/-! Three increments: three lookups and three stores, and nobody wrote either
number. -/
#guard tally.cost TOp.find == 3
#guard tally.cost TOp.put == 3
#guard tally.cost TOp.del == 0
#guard Charged.steps (Rate.unit TOp) tally == 6

/-! And two cells held, not three: the second increment of key `3` overwrites,
which is what the entry list does rather than what anyone asserted. -/
#guard tally.peakAt TKind.entry == 2
#guard tally.netAt TKind.entry == 2

/-- **What the table ends up holding.**  Stated through `lookup`, which is the
specification's view and is noncomputable — so this is a theorem, not a `#guard`. -/
example : (tally.val).lookup 3 = some 2 := by
  simp [tally, bumpAt, Dict.lookup_insert]

example : (tally.val).lookup 5 = some 1 := by
  simp [tally, bumpAt, Dict.lookup_insert]

example : (tally.val).keys = {3, 5} := by
  simp only [tally, bumpAt, Charged.val_bind, Dict.keys_insert, Dict.keys_empty]
  decide

/-! ### The seal

Reading a table without paying is what the module exists to stop, and it is
stopped by the compiler rather than by review. -/

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Dict.lookup', which is 'noncomputable'
-/
#guard_msgs in
def peekTable (d : Dict (Fin 8) ℕ) (k : Fin 8) : Option ℕ := d.lookup k

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Dict.card', which is 'noncomputable'
-/
#guard_msgs in
def peekTableSize (d : Dict (Fin 8) ℕ) : ℕ := d.card

/-! **Blurring two operations into one name**: rejected by `charge_injective`,
and rejected by `decide` rather than by a reviewer. -/
/--
error: Tactic `decide` proved that the proposition
  Function.Injective fun x => TOp.find
is false
-/
#guard_msgs in
example : DictOps TOp where
  charge := fun _ => .find
  charge_injective := by decide

/-! ## A priority queue

The currency's `cmp` is what makes this different from every other structure in
the library: it is charged once per key comparison, by the merge that performs
it.  Nothing here says what a push costs. -/

/-- A currency for a program that keeps a heap. -/
inductive HOp
  | ins | take | look | count | empty | cmp
  deriving DecidableEq, Repr, Inhabited

namespace HOp

/-- Every operation, as a list. -/
def all : List HOp := [.ins, .take, .look, .count, .empty, .cmp]

/-- INTERNAL: `all` is exhaustive. -/
theorem mem_all (o : HOp) : o ∈ all := by cases o <;> simp [all]

instance : Fintype HOp := Fintype.ofList all mem_all

end HOp

/-- INTERNAL: the storage currency — one cell per heap element. -/
inductive HKind | node deriving DecidableEq
instance : Fintype HKind := Fintype.ofList [.node] (by intro k; cases k; simp)

instance : HeapCells (Fin 16) HKind := ⟨HKind.node⟩

instance : HeapOps HOp where
  charge
    | .push => .ins
    | .pop => .take
    | .peek => .look
    | .size => .count
    | .isEmpty => .empty
    | .cmp => .cmp
  charge_injective := by decide

/-- INTERNAL: four pushes, in an order that makes the merges do something. -/
def build : Charged HOp HKind (Heap (Fin 16)) := do
  let h ← Heap.push 5 Heap.empty
  let h ← Heap.push 2 h
  let h ← Heap.push 9 h
  Heap.push 1 h

/-! Four pushes cost four `ins` — and **three comparisons**.  Not four: the first
push merges into an empty heap and compares nothing.  That number is not written
anywhere in this file or in `Arlib.Computation.Heap`; it is what the four merges
did, and `#guard` re-runs them to check. -/
#guard build.cost HOp.ins == 4
#guard build.cost HOp.cmp == 3
#guard build.cost HOp.take == 0
#guard Charged.steps (Rate.unit HOp) build == 7

/-! Four elements held, and the heap never rose above them. -/
#guard build.peakAt HKind.node == 4
#guard build.netAt HKind.node == 4

/-- INTERNAL: take the smallest. -/
def drain : Charged HOp HKind (Option (Fin 16) × Heap (Fin 16)) := do
  let h ← build
  Heap.pop h

/-! A pop is one `take` plus the comparisons that repair the heap — here one,
because the root's children are a single node and an empty tree. -/
#guard drain.cost HOp.take == 1
#guard drain.cost HOp.ins == 4
#guard drain.cost HOp.cmp == 3
#guard drain.netAt HKind.node == 3

/-- **A rate that makes comparisons dear.**  Nothing about the program changes;
the same three comparisons are simply priced differently.  This is the separation
the module is built around — the count belongs to the program, the price belongs
to the machine. -/
def dearCompare : Rate HOp where
  cost
    | .cmp => 4
    | _ => 1
  one_le := by intro o; cases o <;> norm_num

#guard Charged.steps dearCompare build == 4 + 3 * 4

/-- **The logarithmic bound, applied.**  `Heap.steps_push_le` is the general
statement; here it is instantiated at the empty heap, where it says a first push
takes at most two steps under the unit rate. -/
example : Charged.steps (Rate.unit HOp)
    (Heap.push (κ := HOp) (κₛ := HKind) 7 (Heap.empty : Heap (Fin 16)))
      ≤ 1 + 1 * (Nat.log 2 ((Heap.empty : Heap (Fin 16)).card + 1) + 1) :=
  Heap.steps_push_le _ _ Heap.valid_empty

/-! ### The seal

A heap's contents, its size and its smallest element are all behind a charged
operation. -/

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Heap.root', which is 'noncomputable'
-/
#guard_msgs in
def peekHeap (h : Heap (Fin 16)) : Option (Fin 16) := h.root

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Heap.card', which is 'noncomputable'
-/
#guard_msgs in
def peekHeapSize (h : Heap (Fin 16)) : ℕ := h.card

end ArlibTest.Structures
