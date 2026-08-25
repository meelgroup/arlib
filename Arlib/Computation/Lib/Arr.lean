/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Footprint

/-!
# Writing over a block

`Lib/Reduce` and `Lib/Search` only read.  This is the first entry that writes,
and it exists to exercise the write side of the data bridge: `arrFill`'s
correctness is proved through `HoldsList.state_storeAt`, so the block's contents
are tracked as a Mathlib `List ℕ` across `n` stores rather than reasoned about
cell by cell.

The loop invariant is the one a paper proof would state — after `k` iterations
the block holds `k` copies of the value followed by the untouched tail — and the
only piece of list surgery it needs is `set_replicate_append`, proved below.

## Main definitions

* `arrFill base n v` — overwrite `n` cells with `v`.
-/

namespace Arlib.Computation

variable {w : ℕ}

/-- Setting the cell just past a run of copies extends the run.

This is the list-level content of one iteration of `arrFill`: the invariant says
the block holds `List.replicate k x ++ l.drop k`, and one store takes it to the
same shape at `k + 1`. -/
private theorem set_replicate_append {α : Type*} (x : α) (l : List α) (k : ℕ)
    (hk : k < l.length) :
    (List.replicate k x ++ l.drop k).set k x = List.replicate (k + 1) x ++ l.drop (k + 1) := by
  have hdrop : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hk
  rw [List.set_append_right k x (by simp)]
  rw [show k - (List.replicate k x).length = 0 by simp]
  rw [hdrop]
  rw [show (l[k] :: l.drop (k + 1)).set 0 x = x :: l.drop (k + 1) from rfl]
  rw [List.replicate_succ']
  simp

/-- Overwrite the `n` cells based at `base` with `v`. -/
def arrFill (base : Word w) (n : ℕ) (v : Word w) : RAM w Unit :=
  iterate n (fun i _ => storeAt base i v) ()

/-- **The cost of `arrFill`**: a literal, an addition and a store per cell. -/
theorem steps_arrFill_le (C : CostModel) (base : Word w) (n : ℕ) (v : Word w)
    (σ : RamState w) :
    RAM.steps C (arrFill base n v) σ
      ≤ n * (C.cost .lit + C.cost .add + C.cost .store) := by
  refine steps_iterate_le C n _ _ _ _ ?_
  intro j x τ _
  simp

/-- The cost of `arrFill` from below.  With `steps_arrFill_le` this is an
equality, so the bound is exactly attained. -/
theorem steps_arrFill_ge (C : CostModel) (base : Word w) (n : ℕ) (v : Word w)
    (σ : RamState w) :
    n * (C.cost .lit + C.cost .add + C.cost .store)
      ≤ RAM.steps C (arrFill base n v) σ := by
  refine steps_iterate_ge C n _ _ _ _ ?_
  intro j x τ
  simp

/-- On the unit-cost RAM, filling costs **exactly three operations per cell**. -/
theorem steps_arrFill_le_unitCost (base : Word w) (n : ℕ) (v : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (arrFill base n v) σ ≤ 3 * n := by
  have := steps_arrFill_le CostModel.unitCost base n v σ
  simp only [CostModel.unitCost_cost] at this
  omega

/-- Filling allocates nothing. -/
theorem noAlloc_arrFill (base : Word w) (n : ℕ) (v : Word w) : NoAlloc (arrFill base n v) :=
  noAlloc_iterate n _ _ (fun j _ => noAlloc_storeAt base j v)

/-- **`arrFill` leaves the block holding `n` copies of `v`.**

Proved through `HoldsList.state_storeAt`, so the block's contents are carried as
a Mathlib list across all `n` stores. -/
theorem holdsList_state_arrFill {σ : RamState w} {a : ℕ} {l : List ℕ}
    (H : HoldsList σ a l) {base : Word w} (hb : base.toNat = a) {n : ℕ} (hn : n ≤ l.length)
    (v : Word w) :
    HoldsList ((arrFill base n v).state σ) a (List.replicate n v.toNat ++ l.drop n) := by
  have key := iterate_induction n (fun i _ => storeAt base i v) () σ
    (fun k (_ : Unit) (τ : RamState w) =>
      HoldsList τ a (List.replicate k v.toNat ++ l.drop k))
    (by simpa using H) ?step
  · exact key
  case step =>
    intro j x τ hj hτ
    have hjl : j < (List.replicate j v.toNat ++ l.drop j).length := by
      simp only [List.length_append, List.length_replicate, List.length_drop]
      omega
    have := hτ.state_storeAt hb hjl v
    rwa [set_replicate_append v.toNat l j (by omega)] at this

end Arlib.Computation
