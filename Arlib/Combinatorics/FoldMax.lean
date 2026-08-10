/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `Finset.fold max` as a "sup with a floor"

`Finset.sup'` computes a maximum over a `Finset`, but demands a nonemptiness
proof at *every* call site.  When the index set is allowed to be empty — a
`Finset` of "active" elements that may legitimately be empty — the resulting
side conditions dominate the proof.

`maxOver s b f = s.fold max b f` is the maximum of `f` over `s` **floored at
`b`**.  It is total: no nonemptiness hypothesis anywhere, and the floor is
usually available for free (a norm is floored at `0`, an expected time at `1`).
This module names the pattern and packages the four bounds one actually uses,
in the `≤`/`<` shapes that `linarith` and `gcongr` want.

Companion to `Arlib.Combinatorics.ListFold`, which does the same job for
`List.foldr min`.

## Main statements

* `maxOver_le_iff` — the characterisation: `maxOver s b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c`.
* `le_maxOver_of_mem`, `base_le_maxOver` — the two lower bounds.
* `maxOver_le`, `maxOver_lt` — the non-strict and strict upper bounds.
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

namespace Arlib.Combinatorics

/-- `maxOver s b f` is `max b (maxₓ∈ₛ f x)` — the maximum of `f` over `s`,
floored at `b`.  Total: no nonemptiness side condition. -/
noncomputable def maxOver {α : Type*} [DecidableEq α] (s : Finset α) (b : ℝ) (f : α → ℝ) : ℝ :=
  s.fold max b f

/-- **The characterisation.**  `maxOver s b f ≤ c` iff the floor and every
member of `s` are `≤ c`.  Every upper bound below is this lemma. -/
theorem maxOver_le_iff {α : Type*} [DecidableEq α] (s : Finset α) (b c : ℝ) (f : α → ℝ) :
    maxOver s b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c :=
  Finset.fold_max_le c

/-- Each member of `s` is below the max. -/
theorem le_maxOver_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {b : ℝ} {f : α → ℝ}
    {x : α} (hx : x ∈ s) : f x ≤ maxOver s b f :=
  (Finset.le_fold_max (f x)).2 (Or.inr ⟨x, hx, le_refl _⟩)

/-- The floor is below the max — this is what makes `maxOver` total. -/
theorem base_le_maxOver {α : Type*} [DecidableEq α] (s : Finset α) (b : ℝ) (f : α → ℝ) :
    b ≤ maxOver s b f :=
  (Finset.le_fold_max b).2 (Or.inl (le_refl _))

/-- The upper bound, in the form proofs use it. -/
theorem maxOver_le {α : Type*} [DecidableEq α] {s : Finset α} {b c : ℝ} {f : α → ℝ}
    (hb : b ≤ c) (hf : ∀ x ∈ s, f x ≤ c) : maxOver s b f ≤ c :=
  (maxOver_le_iff s b c f).2 ⟨hb, hf⟩

/-- The strict companion of `maxOver_le`: a max over a `Finset`, floored at `b`,
is `< c` as soon as the floor and every member are.  (Strictness does *not*
follow from `maxOver_le_iff`, since `<` is not a `fold`-stable predicate; the
induction is genuine.) -/
theorem maxOver_lt {α : Type*} [DecidableEq α] {s : Finset α} {b c : ℝ} {f : α → ℝ}
    (hb : b < c) (hf : ∀ x ∈ s, f x < c) : maxOver s b f < c := by
  classical
  induction s using Finset.induction with
  | empty => simpa [maxOver] using hb
  | @insert a s ha ih =>
      rw [maxOver, Finset.fold_insert ha]
      exact max_lt (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

end Arlib.Combinatorics
