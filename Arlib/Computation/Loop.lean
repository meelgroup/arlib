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

## Main definitions

* `iterate n f a` — run `f 0`, `f 1`, …, `f (n-1)`, threading an accumulator.
* `steps_iterate_le`, `steps_iterate_le_sum` — the cost of a loop.
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
