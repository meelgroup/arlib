/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Loop

/-!
# Arrays, and what they hold

A cost bound is worthless without a correctness theorem, and a correctness
theorem stated about a machine state is unreadable.  `HoldsList` is the join: it
says that a block of memory holds a Mathlib `List ℕ`, so every theorem in
`Arlib.Computation.Lib` can state its postcondition in Mathlib's vocabulary and
never mention a cell.

Addresses are `ℕ` inside the state, so there is no wraparound condition to carry
in the predicate.  Wraparound enters exactly once, in `toNat_loadAt`, where a
`ℕ` index is turned into a machine address, and `HoldsList.bounded` is what
discharges it.

## Main definitions

* `HoldsList σ a l` — the cells from `a` hold `l`.
* `loadAt base i` — read the `i`-th cell of a block, and its cost.
-/

namespace Arlib.Computation

variable {w : ℕ}

/-- `HoldsList σ a l` — the `l.length` cells at addresses `a, a+1, …` hold `l`.

`fits` and `bounded` are data rather than side conditions on the lemmas below
because without them the predicate is satisfiable by a state that does not hold
the list at all: an index could run past the allocated region, or an address
could wrap, and every bound in `Lib/` would then be true of a machine that holds
something else. -/
structure HoldsList (σ : RamState w) (a : ℕ) (l : List ℕ) : Prop where
  /-- The block lies inside the allocated region. -/
  fits : a + l.length ≤ σ.size
  /-- Every allocated address fits in a word.  This is the width hypothesis, in
  the one place it is needed. -/
  bounded : σ.size ≤ 2 ^ w
  /-- The `i`-th cell holds the `i`-th entry. -/
  get : ∀ (i : ℕ) (h : i < l.length), (σ.get (a + i)).toNat = l[i]

namespace HoldsList

variable {σ : RamState w} {a : ℕ} {l : List ℕ}

/-- An in-range index addresses a cell that fits in a word. -/
theorem index_lt (H : HoldsList σ a l) {i : ℕ} (hi : i < l.length) : a + i < 2 ^ w := by
  have := H.fits
  have := H.bounded
  omega

end HoldsList

/-- Read the `i`-th cell of the block based at `base`.

The index arithmetic is done with real primitives — a literal, an addition and a
load — so the three operations a machine performs to index an array are the three
this charges.  Only the loop's own back-branch is uncharged, which is the
constant factor recorded in `Arlib.Computation.Loop`. -/
def loadAt (base : Word w) (i : ℕ) : RAM w (Word w) := do
  let iw ← lit i
  let addr ← add base iw
  load addr

@[simp] theorem state_loadAt (base : Word w) (i : ℕ) (σ : RamState w) :
    (loadAt base i).state σ = σ := rfl

@[simp] theorem cost_loadAt (base : Word w) (i : ℕ) (σ : RamState w) :
    (loadAt base i).cost σ = CostVec.one .lit + (CostVec.one .add + CostVec.one .load) := rfl

@[simp] theorem steps_loadAt (C : CostModel) (base : Word w) (i : ℕ) (σ : RamState w) :
    RAM.steps C (loadAt base i) σ = C.cost .lit + C.cost .add + C.cost .load := by
  simp [loadAt, RAM.steps, Nat.add_assoc]

/-- **Reading the `i`-th cell of a block that holds `l` returns `l[i]`.**  This
is where a `ℕ` index becomes a machine address, and the only place wraparound has
to be ruled out. -/
theorem toNat_loadAt {σ : RamState w} {a : ℕ} {l : List ℕ} (H : HoldsList σ a l)
    {base : Word w} (hb : base.toNat = a) {i : ℕ} (hi : i < l.length) :
    ((loadAt base i).val σ).toNat = l[i] := by
  have hai : a + i < 2 ^ w := H.index_lt hi
  have hi' : i < 2 ^ w := by omega
  simp only [loadAt, RAM.val_bind, state_lit, state_add, toNat_load,
    toNat_add, toNat_lit, hb]
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hai]
  exact H.get i hi

end Arlib.Computation
