/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The weighted maximum norm `‖Q‖_w`

    ‖Q‖_w := max_{(s,a) ∈ Sₙₜ × A} |Q(s,a)| / w(s,a)

Two presentations, and the bridge between them:

* `wnorm` — the norm itself, as a `Finset` maximum over `SAnt` floored at `0`
  (`maxOver`), so it is total even when there are no non-terminal pairs.  This
  is the form the *statements* use.
* `WLe w Q c` — the pointwise predicate `∀ (s,a) ∈ Sₙₜ × A, |Q(s,a)| ≤ c·w(s,a)`.
  This is the form the *proofs* use: it turns every `max`/`div` manipulation
  into arithmetic on a fixed pair.

`wnorm_le_iff` and `WLe_wnorm` are the bridge, valid whenever the weight is
strictly positive on `SAnt` — which for `w = T_s` is `Property (Almost-sure
termination)`'s `1 ≤ T_s`.
-/
import Arlib.MDP.Basic

namespace Arlib

open scoped BigOperators
open Finset
open Arlib.Combinatorics

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A)

/-- **`‖Q‖_w = max_{(s,a) ∈ Sₙₜ × A} |Q(s,a)|/w(s,a)`**, floored at `0` so that
it is defined also when `Sₙₜ × A = ∅`. -/
noncomputable def wnorm (w : S → A → ℝ) (Q : S → A → ℝ) : ℝ :=
  maxOver M.SAnt 0 fun p => |Q p.1 p.2| / w p.1 p.2

/-- **The pointwise form of `‖Q‖_w ≤ c`.**  Every proof below is phrased in this
form; `wnorm_le_iff` converts. -/
def WLe (w : S → A → ℝ) (Q : S → A → ℝ) (c : ℝ) : Prop :=
  ∀ s a, M.isTerm s = false → a ∈ M.enabled s → |Q s a| ≤ c * w s a

theorem wnorm_nonneg (w Q : S → A → ℝ) : 0 ≤ M.wnorm w Q :=
  base_le_maxOver _ _ _

/-- `‖Q‖_w ≤ c` unfolds to `0 ≤ c` together with the pointwise bound. -/
theorem wnorm_le_iff {w Q : S → A → ℝ} {c : ℝ}
    (hw : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < w s a) :
    M.wnorm w Q ≤ c ↔ (0 ≤ c ∧ M.WLe w Q c) := by
  rw [wnorm, maxOver_le_iff]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun s a hs ha => ?_⟩
    have := h (s, a) (M.mk_mem_SAnt hs ha)
    exact (div_le_iff₀ (hw s a hs ha)).1 this
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun p hp => ?_⟩
    obtain ⟨hs, ha⟩ := (M.mem_SAnt).1 hp
    exact (div_le_iff₀ (hw p.1 p.2 hs ha)).2 (h p.1 p.2 hs ha)

/-- The norm realises its own bound: `‖Q‖_w` is a valid `c` in `WLe`. -/
theorem WLe_wnorm {w Q : S → A → ℝ}
    (hw : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < w s a) :
    M.WLe w Q (M.wnorm w Q) :=
  ((M.wnorm_le_iff hw).1 le_rfl).2

theorem wnorm_le_of_WLe {w Q : S → A → ℝ} {c : ℝ}
    (hw : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < w s a)
    (hc : 0 ≤ c) (h : M.WLe w Q c) : M.wnorm w Q ≤ c :=
  (M.wnorm_le_iff hw).2 ⟨hc, h⟩

theorem WLe.mono {w Q : S → A → ℝ} {c d : ℝ}
    (hw : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 ≤ w s a)
    (h : M.WLe w Q c) (hcd : c ≤ d) : M.WLe w Q d := fun s a hs ha =>
  le_trans (h s a hs ha) (mul_le_mul_of_nonneg_right hcd (hw s a hs ha))

/-- `‖Q‖_w = 0` forces `Q = 0` on `Sₙₜ × A`. -/
theorem eq_zero_of_wnorm_eq_zero {w Q : S → A → ℝ}
    (hw : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < w s a)
    (h : M.wnorm w Q = 0) {s : S} {a : A} (hs : M.isTerm s = false) (ha : a ∈ M.enabled s) :
    Q s a = 0 := by
  have := M.WLe_wnorm (Q := Q) hw s a hs ha
  rw [h, zero_mul] at this
  exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))

end MDP

end Arlib
