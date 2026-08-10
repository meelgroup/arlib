/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `Arlib.Prelude`

The relative-error interval `relErr ε b = [(1-ε)·b, (1+ε)·b]` is the shape every
approximation guarantee in the library is stated in.
-/
import Arlib.Prelude

namespace ArlibTest.Prelude

open Arlib

/-- Membership unfolds to the two inequalities, definitionally. -/
example (ε b a : ℝ) (h : a ∈ relErr ε b) : (1 - ε) * b ≤ a ∧ a ≤ (1 + ε) * b := h

/-- The exact value is always within any tolerance of itself, for `b ≥ 0`. -/
example (b : ℝ) (hb : 0 ≤ b) (ε : ℝ) (hε : 0 ≤ ε) : b ∈ relErr ε b := by
  constructor <;> nlinarith

/-- Tightening the tolerance shrinks the window: this is how a `(1 ± ε/2)`
guarantee is handed to a consumer that only asked for `(1 ± ε)`. -/
example (b : ℝ) (hb : 0 ≤ b) (ε : ℝ) (hε : 0 ≤ ε) (a : ℝ) (h : a ∈ relErr (ε / 2) b) :
    a ∈ relErr ε b :=
  relErr_subset_of_le hb (by linarith) h

end ArlibTest.Prelude
