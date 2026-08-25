/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Data

/-!
# Linear scans over an array

The two simplest entries of the library, and the template every later one
follows: an implementation that is an ordinary Lean function in `RAM`, a
correctness theorem stated against a Mathlib `List`, and a cost bound whose
constants are explicit.

Each entry states its cost twice.  The primary form is symbolic in the
`CostModel`, so it survives a change to the instruction set; the numeral form is
the corollary at `CostModel.unitCost`, which is what a reader wants to see.

## Main definitions

* `arrSum base n` — the sum of `n` cells, modulo `2 ^ w`.
* `arrMax base n` — the largest of `n` cells.
-/

namespace Arlib.Computation

variable {w : ℕ}

/-! ## A left fold over a block

`arrSum` and `arrMax` differ only in the body, so the shared shape is worth
naming: the loop's cost is `n` times the body's, and its correctness is an
induction with the accumulator as the invariant. -/

/-- The largest of the first `i` entries, as a left fold. -/
private theorem foldl_max_take_succ (l : List ℕ) (a i : ℕ) (hi : i < l.length) :
    (l.take (i + 1)).foldl max a = max ((l.take i).foldl max a) l[i] := by
  have h : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  rw [h, List.foldl_append]
  simp

/-! ## Sum -/

/-- The sum of the `n` cells based at `base`, accumulated in a word — so the
answer is the true sum reduced modulo `2 ^ w`.  Wrapping is not hidden: it is in
the statement of `toNat_arrSum`. -/
def arrSum (base : Word w) (n : ℕ) : RAM w (Word w) := do
  let z ← lit 0
  iterate n (fun i acc => do
    let x ← loadAt base i
    add acc x) z

/-- Summing does not disturb memory. -/
@[simp] theorem state_arrSum (base : Word w) (n : ℕ) (σ : RamState w) :
    (arrSum base n).state σ = σ := by
  simp only [arrSum, RAM.state_bind, state_lit]
  refine iterate_induction n _ _ σ (fun _ _ τ => τ = σ) rfl ?_
  intro j x τ _ h
  simpa [RAM.state_bind] using h

/-- **The cost of `arrSum`**, symbolic in the cost model: one literal to start,
then `n` iterations of a literal, an addition, a load and an addition. -/
theorem steps_arrSum_le (C : CostModel) (base : Word w) (n : ℕ) (σ : RamState w) :
    RAM.steps C (arrSum base n) σ
      ≤ C.cost .lit + n * (C.cost .lit + C.cost .add + C.cost .load + C.cost .add) := by
  simp only [arrSum, RAM.steps_bind, steps_lit]
  gcongr
  refine steps_iterate_le C n _ _ _ _ ?_
  intro j x τ _
  simp [RAM.steps_bind, Nat.add_assoc]

/-- The cost of `arrSum` on the unit-cost RAM: **four operations per cell, plus
one.** -/
theorem steps_arrSum_le_unitCost (base : Word w) (n : ℕ) (σ : RamState w) :
    RAM.steps CostModel.unitCost (arrSum base n) σ ≤ 4 * n + 1 := by
  have := steps_arrSum_le CostModel.unitCost base n σ
  simp only [CostModel.unitCost_cost] at this
  omega

/-- **`arrSum` returns the sum of the block, modulo `2 ^ w`.** -/
theorem toNat_arrSum {σ : RamState w} {a : ℕ} {l : List ℕ} (H : HoldsList σ a l)
    {base : Word w} (hb : base.toNat = a) {n : ℕ} (hn : n ≤ l.length) :
    ((arrSum base n).val σ).toNat = (l.take n).sum % 2 ^ w := by
  simp only [arrSum, RAM.val_bind, state_lit]
  have key := iterate_induction n
    (fun i acc => do let x ← loadAt base i; add acc x)
    ((lit 0 : RAM w (Word w)).val σ) σ
    (fun k (acc : Word w) (τ : RamState w) => τ = σ ∧ acc.toNat = (l.take k).sum % 2 ^ w)
    ⟨rfl, by simp⟩ ?step
  · exact key.2
  case step =>
    rintro j x τ hj ⟨hτ, hacc⟩
    subst hτ
    have hjl : j < l.length := by omega
    refine ⟨by simp [RAM.state_bind], ?_⟩
    simp only [RAM.val_bind, state_loadAt, toNat_add, hacc, toNat_loadAt H hb hjl]
    rw [List.sum_take_succ l j hjl]
    conv_rhs => rw [Nat.add_mod]
    simp

/-- **`arrSum` charges.**  The deterministic analogue of
`Arlib.Approximation.IsFPRAS.Charges`: the zero-cost non-algorithm that
predicate exists to exclude is not expressible here, because a program that
performs a primitive has positive cost and this one begins with a literal. -/
theorem steps_arrSum_pos (C : CostModel) (base : Word w) (n : ℕ) (σ : RamState w) :
    0 < RAM.steps C (arrSum base n) σ :=
  RAM.steps_pos_bind C _ (steps_lit_pos σ C 0)

/-! ## Maximum -/

/-- The largest of the `n` cells based at `base`; zero when `n = 0`.

The running maximum starts at zero rather than at the first cell, which costs
nothing — the entries are natural numbers, so zero is the identity for `max` —
and removes the `n ≠ 0` side condition from every statement below. -/
def arrMax (base : Word w) (n : ℕ) : RAM w (Word w) := do
  let z ← lit 0
  iterate n (fun i m => do
    let x ← loadAt base i
    let c ← lt m x
    if c then pure x else pure m) z

/-- Taking a maximum does not disturb memory. -/
@[simp] theorem state_arrMax (base : Word w) (n : ℕ) (σ : RamState w) :
    (arrMax base n).state σ = σ := by
  simp only [arrMax, RAM.state_bind, state_lit]
  refine iterate_induction n _ _ σ (fun _ _ (τ : RamState w) => τ = σ) rfl ?_
  intro j x τ _ h
  subst h
  simp only [RAM.state_bind, state_loadAt, state_lt]
  split <;> rfl

/-- **The cost of `arrMax`**, symbolic in the cost model. -/
theorem steps_arrMax_le (C : CostModel) (base : Word w) (n : ℕ) (σ : RamState w) :
    RAM.steps C (arrMax base n) σ
      ≤ C.cost .lit + n * (C.cost .lit + C.cost .add + C.cost .load + C.cost .lt) := by
  simp only [arrMax, RAM.steps_bind, steps_lit]
  gcongr
  refine steps_iterate_le C n _ _ _ _ ?_
  intro j x τ _
  by_cases hc : ((lt x ((loadAt base j).val τ)).val τ) = true <;>
    simp [RAM.steps_bind, hc, Nat.add_assoc]

/-- The cost of `arrMax` on the unit-cost RAM: **four operations per cell, plus
one.** -/
theorem steps_arrMax_le_unitCost (base : Word w) (n : ℕ) (σ : RamState w) :
    RAM.steps CostModel.unitCost (arrMax base n) σ ≤ 4 * n + 1 := by
  have := steps_arrMax_le CostModel.unitCost base n σ
  simp only [CostModel.unitCost_cost] at this
  omega

/-- **`arrMax` charges.**  See `steps_arrSum_pos`. -/
theorem steps_arrMax_pos (C : CostModel) (base : Word w) (n : ℕ) (σ : RamState w) :
    0 < RAM.steps C (arrMax base n) σ :=
  RAM.steps_pos_bind C _ (steps_lit_pos σ C 0)

/-- **`arrMax` returns the largest of the first `n` entries.** -/
theorem toNat_arrMax {σ : RamState w} {a : ℕ} {l : List ℕ} (H : HoldsList σ a l)
    {base : Word w} (hb : base.toNat = a) {n : ℕ} (hn : n ≤ l.length) :
    ((arrMax base n).val σ).toNat = (l.take n).foldl max 0 := by
  simp only [arrMax, RAM.val_bind, state_lit]
  have key := iterate_induction n
    (fun i m => do let x ← loadAt base i; let c ← lt m x; if c then pure x else pure m)
    ((lit 0 : RAM w (Word w)).val σ) σ
    (fun k (m : Word w) (τ : RamState w) => τ = σ ∧ m.toNat = (l.take k).foldl max 0)
    ⟨rfl, by simp⟩ ?step
  · exact key.2
  case step =>
    rintro j x τ hj ⟨hτ, hm⟩
    subst hτ
    have hjl : j < l.length := by omega
    have hx : ((loadAt base j).val τ).toNat = l[j] := toNat_loadAt H hb hjl
    refine ⟨by simp only [RAM.state_bind, state_loadAt, state_lt]; split <;> rfl, ?_⟩
    rw [foldl_max_take_succ l 0 j hjl, ← hm, ← hx]
    simp only [RAM.val_bind, state_loadAt, val_lt]
    by_cases hc : x.toNat < ((loadAt base j).val τ).toNat
    · simp only [hc, decide_true, if_true, RAM.val_pure]
      omega
    · simp only [hc, decide_false, Bool.false_eq_true, if_false, RAM.val_pure]
      omega

end Arlib.Computation
