/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Data
import Mathlib.Data.Nat.Log

/-!
# Binary search

The entry that shows the framework is not restricted to linear bounds.

`arrMax` and `arrSum` cost a constant per cell, so their bounds fall out of
`steps_iterate_le` with a constant per-iteration charge.  Binary search costs a
constant per *halving*, and the number of halvings is `Nat.clog 2 (n + 1)` — so
the same lemma, applied to a loop whose trip count is logarithmic in the input,
gives a logarithmic bound.  Nothing about the cost machinery changes; only the
number of iterations does.

The loop is written with an explicit trip count rather than as a `while`, which
is what makes its termination structural and keeps fuel out of every statement
about it.  For binary search the trip count is exactly the quantity the textbook
analysis names, so writing it down costs nothing and buys the bound directly.

## Main definitions

* `binSearch base n key` — the first index at which `key` could be inserted.
* `steps_binSearch_le` — its cost, logarithmic in `n`.
-/

namespace Arlib.Computation

variable {w : ℕ}

/-- One halving step of binary search: given the current window `(lo, hi)`,
either narrow it or leave it alone once it is empty. -/
private def binStep (base key : Word w) (p : Word w × Word w) : RAM w (Word w × Word w) := do
  let (lo, hi) := p
  let c ← lt lo hi
  if c then do
    let s ← add lo hi
    let two ← lit 2
    let mid ← udiv s two
    let addr ← add base mid
    let x ← load addr
    let c2 ← lt x key
    if c2 then do
      let one ← lit 1
      let lo' ← add mid one
      pure (lo', hi)
    else
      pure (lo, mid)
  else
    pure (lo, hi)

/-- Binary search over the `n` cells based at `base`, assumed sorted: returns the
first index at which `key` could be inserted.

The loop runs `Nat.clog 2 (n + 1)` times, which is the number of halvings needed
to reduce a window of width `n` to width zero. -/
def binSearch (base : Word w) (n : ℕ) (key : Word w) : RAM w (Word w) := do
  let lo ← lit 0
  let hi ← lit n
  let p ← iterate (Nat.clog 2 (n + 1)) (fun _ p => binStep base key p) (lo, hi)
  pure p.1

/-- Searching does not disturb memory. -/
@[simp] theorem state_binStep (base key : Word w) (p : Word w × Word w) (σ : RamState w) :
    (binStep base key p).state σ = σ := by
  simp only [binStep, RAM.state_bind, state_lt]
  split
  · simp only [RAM.state_bind, state_add, state_lit, state_udiv, state_load]
    split <;> simp [RAM.state_bind]
  · rfl

/-- **One halving costs at most nine operations**, whichever branch it takes.
The count is stated as a maximum over the branches rather than per branch,
because the loop bound needs a single number. -/
theorem steps_binStep_le (C : CostModel) (base key : Word w) (p : Word w × Word w)
    (σ : RamState w) :
    RAM.steps C (binStep base key p) σ
      ≤ C.cost .lt + (C.cost .add + C.cost .lit + C.cost .udiv + C.cost .add
          + C.cost .load + C.cost .lt + (C.cost .lit + C.cost .add)) := by
  simp only [binStep, RAM.steps_bind, steps_lt, state_lt]
  split
  · simp only [RAM.steps_bind, steps_add, steps_lit, steps_udiv, steps_load, steps_lt,
      state_add, state_lit, state_udiv, state_load]
    split <;> simp [RAM.steps_bind] <;> omega
  · simp

/-- **The cost of binary search is logarithmic in the size of the block.**

Two literals to set up the window, then `Nat.clog 2 (n + 1)` halvings of at most
nine operations each. -/
theorem steps_binSearch_le (C : CostModel) (base : Word w) (n : ℕ) (key : Word w)
    (σ : RamState w) :
    RAM.steps C (binSearch base n key) σ
      ≤ C.cost .lit + C.cost .lit
        + Nat.clog 2 (n + 1) *
            (C.cost .lt + (C.cost .add + C.cost .lit + C.cost .udiv + C.cost .add
              + C.cost .load + C.cost .lt + (C.cost .lit + C.cost .add))) := by
  have hloop := steps_iterate_le C (Nat.clog 2 (n + 1))
    (fun _ p => binStep base key p)
    ((lit 0 : RAM w (Word w)).val σ, (lit n : RAM w (Word w)).val σ) σ
    (C.cost .lt + (C.cost .add + C.cost .lit + C.cost .udiv + C.cost .add
      + C.cost .load + C.cost .lt + (C.cost .lit + C.cost .add)))
    (fun j x τ _ => steps_binStep_le C base key x τ)
  simp only [binSearch, RAM.steps_bind, steps_lit, state_lit, RAM.steps_pure]
  omega

/-- The cost of binary search on the unit-cost RAM: **nine operations per
halving, plus two.** -/
theorem steps_binSearch_le_unitCost (base : Word w) (n : ℕ) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (binSearch base n key) σ ≤ 9 * Nat.clog 2 (n + 1) + 2 := by
  have := steps_binSearch_le CostModel.unitCost base n key σ
  simp only [CostModel.unitCost_cost] at this
  omega

end Arlib.Computation
