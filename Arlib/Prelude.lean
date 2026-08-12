/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Prelude: shared notation

This file collects small, reusable definitions used across the development,
in particular the "relative-error interval" `(1 ± ε)·b` used pervasively in
approximation-error statements.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.RingNF

namespace Arlib

/-- The multiplicative relative-error interval `(1 ± ε)·b = [(1-ε)b, (1+ε)b]`,
the usual notation `a ∈ (1 ± ε) b`.  Marked `@[reducible]` so that it
is definitionally transparent to `Set.Icc` (keeps `isDefEq` cheap where the two
forms are interchanged). -/
@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1 - ε) * b) ((1 + ε) * b)

@[simp] theorem mem_relErr {ε b a : ℝ} :
    a ∈ relErr ε b ↔ (1 - ε) * b ≤ a ∧ a ≤ (1 + ε) * b := Iff.rfl

/-- Membership in `(1 ± ε) b` is symmetric in the sense that if `a ∈ (1 ± ε) b`
then the two defining inequalities hold. Convenience destructor. -/
theorem relErr.lower {ε b a : ℝ} (h : a ∈ relErr ε b) : (1 - ε) * b ≤ a := h.1

theorem relErr.upper {ε b a : ℝ} (h : a ∈ relErr ε b) : a ≤ (1 + ε) * b := h.2

/-- Monotonicity of the relative-error interval in the tolerance `ε`
(for nonnegative base `b`): a tighter tolerance sits inside a looser one.
Used when relating the "loose" (ε/2) and "failing" (via (1±ε)⁻¹) blocks. -/
theorem relErr_subset_of_le {ε₁ ε₂ b : ℝ} (hb : 0 ≤ b) (h : ε₁ ≤ ε₂) :
    relErr ε₁ b ⊆ relErr ε₂ b := by
  intro a ha
  refine ⟨?_, ?_⟩
  · calc (1 - ε₂) * b ≤ (1 - ε₁) * b := by
              apply mul_le_mul_of_nonneg_right _ hb; linarith
        _ ≤ a := ha.1
  · calc a ≤ (1 + ε₁) * b := ha.2
        _ ≤ (1 + ε₂) * b := by
              apply mul_le_mul_of_nonneg_right _ hb; linarith

end Arlib
