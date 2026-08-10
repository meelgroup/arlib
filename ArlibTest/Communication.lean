/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `Arlib.Communication`

Two-party communication complexity, used here as a measure of combinatorial
structure rather than as a model of computation. A rectangle is a pair of
locality constraints, one per party; the content is that a rectangle cannot
distinguish inputs it does not separate.
-/
import Arlib.Communication

namespace ArlibTest.Communication

open Arlib.Communication

/-- **The rectangle property**, which is the whole reason rectangles are the
right object: if `(x, y)` and `(x', y')` both lie in a rectangle, so do the two
"crossed" pairs. Every lower bound in the library is ultimately an argument that
some function does not have this closure on few pieces. -/
example {X Y : Type*} {R : TPRect X Y} {x x' : X} {y y' : Y}
    (h : R.Mem x y) (h' : R.Mem x' y') : R.Mem x y' ∧ R.Mem x' y :=
  ⟨TPRect.mem_cross h h', TPRect.mem_cross h' h⟩

/-- A partition of a fibre is in particular a cover of it, so a cover lower
bound is the weaker of the two. -/
example {X Y : Type*} {k : ℕ} {F : X → Y → Bool} {b : Bool}
    (h : HasTPPartition F b k) : HasTPCover F b k :=
  h.hasTPCover

end ArlibTest.Communication
