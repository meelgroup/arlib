/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Machine
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounded iteration, and its cost

Algorithms here are Lean functions, so their loops are Lean's recursion.  This
module supplies the one shape almost every loop takes — run a body once per index
of a range, threading an accumulator — together with the two cost lemmas that
every bound in `Arlib.Computation.Lib` goes through.

Why a combinator rather than open recursion in each algorithm: the cost of a loop
is a sum over its iterations, and the induction proving that is the same every
time.  Doing it once is the difference between a cost proof that is three lines
and one that is thirty.

The per-iteration bound comes in two forms.  `steps_iterate_le` is the uniform
one — every iteration costs at most `b`, so the loop costs at most `n * b` — and
it is what linear scans use.  `steps_iterate_le_sum` lets the bound depend on the
index, which is what a merge or a sift-down needs; retrofitting it later would
mean restating every rule, so both exist from the start.

## What `iterate` does not charge

**The loop's own back-branch is free.**  A real machine pays a comparison and an
increment per iteration to decide whether to go round again; `iterate` recurses
on a Lean `ℕ` and charges neither.  Two consequences, and the second is the
reason this is written down rather than left to be discovered.

*For the entries in `Arlib.Computation.Lib` the understatement is a constant
factor*, because each of their bodies performs at least two primitives.  That is
not a hope: `steps_iterate_ge` gives the matching lower bound, and each entry
states it (`steps_arrMax_ge`, `steps_arrSum_ge`), so every cost claim in the
library is a sandwich rather than an upper bound quoted alone.

*In general it is not a constant factor.*  `iterate n (fun _ a => pure a) a`
costs nothing, while the machine it models would pay `Θ(n)`.  Nothing in the
library relies on that, but the model permits it, and a bound proved here is a
bound on this model.  The fix is known and is not free: have `iterate` carry its
index as a `Word` and perform the increment and the guard with real primitives,
which charges two operations per iteration honestly and lets the body reuse the
index register rather than recomputing it with `lit`.  That is a refactor of
every entry and every proof, and it is recorded in
`docs/dev/Computation-ROADMAP.md` as outstanding.

## Main definitions

* `iterate n f a` — run `f 0`, `f 1`, …, `f (n-1)`, threading an accumulator.
* `steps_iterate_le`, `steps_iterate_le_sum` — the cost of a loop, from above.
* `steps_iterate_ge` — from below.
* `iterate_induction` — the loop invariant.
-/

namespace Arlib.Computation

universe u
variable {w : ℕ} {α : Type u}

/-- `iterate.go f i k a` runs the body at indices `i, i+1, …, i+k-1`. -/
private def iterateGo (f : ℕ → α → RAM w α) : ℕ → ℕ → α → RAM w α
  | _, 0, a => pure a
  | i, k + 1, a => do
      let a' ← f i a
      iterateGo f (i + 1) k a'

/-- Run `f 0`, `f 1`, …, `f (n-1)` in order, threading an accumulator.

This is the library's `for i in [0:n]`.  Its termination is structural, so no
measure has to be exhibited and no fuel appears in any statement about it. -/
def iterate (n : ℕ) (f : ℕ → α → RAM w α) (a : α) : RAM w α := iterateGo f 0 n a

@[simp] theorem iterate_zero (f : ℕ → α → RAM w α) (a : α) :
    iterate 0 f a = pure a := rfl

private theorem iterateGo_succ (f : ℕ → α → RAM w α) (i k : ℕ) (a : α) :
    iterateGo f i (k + 1) a = (f i a >>= fun a' => iterateGo f (i + 1) k a') := rfl

/-- **The cost of a loop is the sum of the costs of its iterations**, when the
per-iteration bound may depend on the index. -/
theorem steps_iterateGo_le_sum (C : CostModel) (f : ℕ → α → RAM w α)
    (b : ℕ → ℕ) :
    ∀ (k i : ℕ) (a : α) (σ : RamState w),
      (∀ j x τ, i ≤ j → j < i + k → RAM.steps C (f j x) τ ≤ b j) →
      RAM.steps C (iterateGo f i k a) σ ≤ ∑ j ∈ Finset.range k, b (i + j) := by
  intro k
  induction k with
  | zero => intro i a σ _; simp [iterateGo]
  | succ k ih =>
      intro i a σ h
      rw [iterateGo_succ, RAM.steps_bind, Finset.sum_range_succ']
      have hhead : RAM.steps C (f i a) σ ≤ b i :=
        h i a σ (le_refl i) (by omega)
      have htail :
          RAM.steps C (iterateGo f (i + 1) k ((f i a).val σ)) ((f i a).state σ)
            ≤ ∑ j ∈ Finset.range k, b (i + 1 + j) := by
        refine ih (i + 1) _ _ ?_
        intro j x τ hj hj'
        exact h j x τ (by omega) (by omega)
      have heq : ∑ j ∈ Finset.range k, b (i + 1 + j)
          = ∑ j ∈ Finset.range k, b (i + (j + 1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        omega
      rw [heq] at htail
      have hz : b (i + 0) = b i := by congr 1
      omega

/-- The cost of `iterate`, with an index-dependent per-iteration bound. -/
theorem steps_iterate_le_sum (C : CostModel) (n : ℕ) (f : ℕ → α → RAM w α)
    (a : α) (σ : RamState w) (b : ℕ → ℕ)
    (h : ∀ j x τ, j < n → RAM.steps C (f j x) τ ≤ b j) :
    RAM.steps C (iterate n f a) σ ≤ ∑ j ∈ Finset.range n, b j := by
  have := steps_iterateGo_le_sum C f b n 0 a σ (by intro j x τ _ hj; exact h j x τ (by omega))
  simpa [iterate] using this

/-- **A loop costs at least the sum of its iterations.**  The companion to
`steps_iterateGo_le_sum`, and the reason a cost claim here is a sandwich rather
than an upper bound quoted alone. -/
theorem steps_iterateGo_ge (C : CostModel) (f : ℕ → α → RAM w α) (b : ℕ) :
    ∀ (k i : ℕ) (a : α) (σ : RamState w),
      (∀ j x τ, b ≤ RAM.steps C (f j x) τ) →
      k * b ≤ RAM.steps C (iterateGo f i k a) σ := by
  intro k
  induction k with
  | zero => intro i a σ _; simp [iterateGo]
  | succ k ih =>
      intro i a σ h
      rw [iterateGo_succ, RAM.steps_bind]
      have hhead : b ≤ RAM.steps C (f i a) σ := h i a σ
      have htail := ih (i + 1) ((f i a).val σ) ((f i a).state σ) h
      have : (k + 1) * b = k * b + b := by ring
      omega

/-- A loop's cost is at least `n` times its cheapest iteration. -/
theorem steps_iterate_ge (C : CostModel) (n : ℕ) (f : ℕ → α → RAM w α)
    (a : α) (σ : RamState w) (b : ℕ)
    (h : ∀ j x τ, b ≤ RAM.steps C (f j x) τ) :
    n * b ≤ RAM.steps C (iterate n f a) σ :=
  steps_iterateGo_ge C f b n 0 a σ h

/-- **Induction along a loop.**  A predicate on (index, accumulator, state) that
holds at the start and is preserved by the body holds at the end.

This is how a `Lib/` entry's correctness is proved: the loop invariant is `P`,
and the two obligations are exactly the ones a paper proof states. -/
theorem iterateGo_induction (f : ℕ → α → RAM w α) (P : ℕ → α → RamState w → Prop) :
    ∀ (k i : ℕ) (a : α) (σ : RamState w),
      P i a σ →
      (∀ j x τ, i ≤ j → j < i + k → P j x τ →
        P (j + 1) ((f j x).val τ) ((f j x).state τ)) →
      P (i + k) ((iterateGo f i k a).val σ) ((iterateGo f i k a).state σ) := by
  intro k
  induction k with
  | zero => intro i a σ h0 _; simpa [iterateGo] using h0
  | succ k ih =>
      intro i a σ h0 hstep
      rw [iterateGo_succ]
      have hnext : P (i + 1) ((f i a).val σ) ((f i a).state σ) :=
        hstep i a σ (le_refl i) (by omega) h0
      have := ih (i + 1) ((f i a).val σ) ((f i a).state σ) hnext
        (by intro j x τ hj hj' hP; exact hstep j x τ (by omega) (by omega) hP)
      have hidx : i + 1 + k = i + (k + 1) := by omega
      rw [hidx] at this
      simpa [RAM.val_bind, RAM.state_bind] using this

/-- Induction along `iterate`: the loop invariant `P` holds at the end. -/
theorem iterate_induction (n : ℕ) (f : ℕ → α → RAM w α) (a : α) (σ : RamState w)
    (P : ℕ → α → RamState w → Prop) (h0 : P 0 a σ)
    (hstep : ∀ j x τ, j < n → P j x τ → P (j + 1) ((f j x).val τ) ((f j x).state τ)) :
    P n ((iterate n f a).val σ) ((iterate n f a).state σ) := by
  have := iterateGo_induction f P n 0 a σ h0
    (by intro j x τ _ hj hP; exact hstep j x τ (by omega) hP)
  simpa [iterate] using this

/-- The cost of `iterate`, with a uniform per-iteration bound: **`n` iterations
costing `b` each cost `n * b`.** -/
theorem steps_iterate_le (C : CostModel) (n : ℕ) (f : ℕ → α → RAM w α)
    (a : α) (σ : RamState w) (b : ℕ)
    (h : ∀ j x τ, j < n → RAM.steps C (f j x) τ ≤ b) :
    RAM.steps C (iterate n f a) σ ≤ n * b := by
  have := steps_iterate_le_sum C n f a σ (fun _ => b) h
  simpa [Finset.sum_const, mul_comm] using this

end Arlib.Computation
