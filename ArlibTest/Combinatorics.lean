/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `Arlib.Combinatorics`

Generic `Finset` / `List` / `BigOperators` helpers that Mathlib does not have.
-/
import Arlib.Combinatorics

namespace ArlibTest.Combinatorics

open Arlib.Combinatorics

/-- `maxOver s b f` is the maximum of `f` over `s` floored at `b`. Because of the
floor it is total — no `Nonempty` side condition at the call site, which is the
whole point when `s` is a set of "active" elements that may legitimately be
empty. It is characterised by a single `iff`. -/
example (s : Finset ℕ) (f : ℕ → ℝ) (b c : ℝ) :
    maxOver s b f ≤ c ↔ b ≤ c ∧ ∀ i ∈ s, f i ≤ c :=
  maxOver_le_iff s b c f

/-- The floor is always a lower bound, and so is every value attained. -/
example (s : Finset ℕ) (f : ℕ → ℝ) (b : ℝ) (i : ℕ) (hi : i ∈ s) :
    b ≤ maxOver s b f ∧ f i ≤ maxOver s b f :=
  ⟨base_le_maxOver s b f, le_maxOver_of_mem hi⟩

/-- The strict upper bound, which does not follow from the `iff` above. -/
example (s : Finset ℕ) (f : ℕ → ℝ) (b c : ℝ) (hb : b < c) (hf : ∀ i ∈ s, f i < c) :
    maxOver s b f < c :=
  maxOver_lt hb hf

end ArlibTest.Combinatorics
