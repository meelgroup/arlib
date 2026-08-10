/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Snoc as an equivalence

`Fin.snoc` presents a length-`(n+1)` tuple as a length-`n` tuple together with one
more entry.  Packaging that as an `Equiv` is what lets a sum or product over
`Fin (n + 1) → β` be reindexed as a double sum over `(Fin n → β) × β`
(`Equiv.sum_comp`), which is the induction step of every "peel off the last
coordinate" argument.

This is pure `Fin` combinatorics — no probability and no information theory — so it
lives here rather than in either of the areas that consume it.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Prelude
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Basic

namespace Arlib.Combinatorics

/-- Bundling a length-`n` tuple with one more entry is the same as a length-`(n+1)`
tuple, up to the evident relabelling `Fin.snoc`. -/
def snocEquiv (β : Type) {n : ℕ} : ((Fin n → β) × β) ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv p := by
    ext j
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc, Fin.init]

end Arlib.Combinatorics
