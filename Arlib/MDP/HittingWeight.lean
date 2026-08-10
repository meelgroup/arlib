/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The hitting-time weight `T_s` and the contraction factor `β`

The weight the contraction uses is the worst-case expected time to termination,

    T_s := sup_π E^π[T ∣ s₀ = s],   T = inf{t ≥ 0 : s_t ∈ S_term}.

Following the interface/instance discipline, we do **not** define `T` by an
infimum over policies here.  We isolate the three facts about `T` that the whole
convergence argument consumes, as the fields of a structure:

* `T_term`  — `T_s = 0` on terminal states (the standard `T_{s'} = 0` for
  `s' ∈ S_term`, used in the hitting-time Bellman inequality);
* `one_le_T` — `1 ≤ T_s` on non-terminal states ("reaching `S_term` from a
  non-terminal state takes at least one transition"), which is also the
  positivity invariant that makes the weighted norm well-defined;
* `step` — the **one-step inequality** `∑_{s'} P(s'∣s,a)·T_{s'} + 1 ≤ T_s`
  (the hitting-time Bellman inequality, "leaving `s` consumes one step").

`Almost-sure termination` is exactly the assertion that a
`HittingWeight` exists under the no-EC assumption; that is proved separately, in
`Arlib.MDP.Termination`, and everything downstream depends only on this
interface.  In particular `Tmax` is finite *by construction* here, which is the
positivity/well-definedness invariant baked in up front.

`beta = 1 − 1/Tmax ∈ [0,1)` is the standard contraction factor.
-/
import Arlib.MDP.Basic

namespace Arlib.MDP

open scoped BigOperators
open Finset
open Arlib.Combinatorics

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- **A hitting-time weight for `M`** — the three properties of
`T_s = sup_π E^π[T ∣ s₀ = s]` that the convergence proof uses.  Existence under
the no-EC assumption is the almost-sure termination property (`Arlib.MDP.Termination`). -/
structure HittingWeight (M : MDP S A) where
  /-- The worst-case expected time to termination, `T_s`. -/
  T : S → ℝ
  /-- `T_s = 0` on terminal states. -/
  T_term : ∀ s, M.isTerm s = true → T s = 0
  /-- `1 ≤ T_s` on non-terminal states. -/
  one_le_T : ∀ s, M.isTerm s = false → 1 ≤ T s
  /-- **the hitting-time Bellman inequality**: `∑_{s'} P(s' ∣ s,a)·T_{s'} + 1 ≤ T_s`. -/
  step : ∀ s a, M.isTerm s = false → a ∈ M.enabled s →
    (∑ s', M.P s a s' * T s') + 1 ≤ T s

namespace HittingWeight

variable {M : MDP S A} (hw : HittingWeight M)

/-- `T_s ≥ 0` everywhere (`0` on terminals, `≥ 1` elsewhere). -/
theorem T_nonneg (s : S) : 0 ≤ hw.T s := by
  by_cases h : M.isTerm s = true
  · exact le_of_eq (hw.T_term s h).symm
  · exact le_trans zero_le_one (hw.one_le_T s (by simpa using h))

/-- `0 < T_s` on non-terminal states — the positivity invariant that makes the
weighted norm's division legitimate. -/
theorem T_pos {s : S} (h : M.isTerm s = false) : 0 < hw.T s :=
  lt_of_lt_of_le zero_lt_one (hw.one_le_T s h)

/-- **The weight `w(s,a) := T_s`** of the contraction property. -/
def w : S → A → ℝ := fun s _ => hw.T s

theorem w_pos : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < hw.w s a :=
  fun _ _ hs _ => hw.T_pos hs

theorem w_nonneg : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 ≤ hw.w s a :=
  fun s _ _ _ => hw.T_nonneg s

/-- **`max_{s ∈ Sₙₜ} T_s`**, floored at `1` (so the degenerate case `Sₙₜ = ∅`
still gives `1 ≤ Tmax`, keeping `beta = 0` well-defined). -/
noncomputable def Tmax : ℝ := maxOver M.nontermSet 1 hw.T

theorem one_le_Tmax : 1 ≤ hw.Tmax := base_le_maxOver _ _ _

theorem Tmax_pos : 0 < hw.Tmax := lt_of_lt_of_le zero_lt_one hw.one_le_Tmax

theorem T_le_Tmax {s : S} (h : M.isTerm s = false) : hw.T s ≤ hw.Tmax :=
  le_maxOver_of_mem ((M.mem_nontermSet).2 h)

/-- **The contraction factor `β = 1 − 1/max_{s ∈ Sₙₜ} T_s`** of
the contraction property. -/
noncomputable def beta : ℝ := 1 - 1 / hw.Tmax

theorem beta_nonneg : 0 ≤ hw.beta := by
  have h : 1 / hw.Tmax ≤ 1 := by
    rw [div_le_one hw.Tmax_pos]; exact hw.one_le_Tmax
  simpa [beta] using h

theorem beta_lt_one : hw.beta < 1 := by
  have : 0 < 1 / hw.Tmax := one_div_pos.2 hw.Tmax_pos
  simpa [beta] using this

theorem beta_le_one : hw.beta ≤ 1 := le_of_lt hw.beta_lt_one

/-- **The per-pair contraction bound.**  At a non-terminal `s`, the standard
`(T_s − 1)/T_s ≤ β`; multiplied out, `T_s − 1 ≤ β · T_s`.  This is where
`T_s ≤ Tmax` enters. -/
theorem sub_one_le_beta_mul {s : S} (h : M.isTerm s = false) :
    hw.T s - 1 ≤ hw.beta * hw.T s := by
  have hTs : 0 < hw.T s := hw.T_pos h
  have hle : hw.T s ≤ hw.Tmax := hw.T_le_Tmax h
  have hinv : hw.T s / hw.Tmax ≤ 1 := (div_le_one hw.Tmax_pos).2 hle
  have : hw.beta * hw.T s = hw.T s - hw.T s / hw.Tmax := by
    field_simp [beta]; ring
  rw [this]
  linarith

end HittingWeight

end Arlib.MDP
