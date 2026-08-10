/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Reachability values `V*`, `Q*`, and the Bellman optimality equations

`Arlib.MDP.FixedPoint` defines `Q*` as *the fixed point of `H`*, on the source
paper's own authority that "the `Q`-Bellman optimality equation determines `Q*`
completely" (that paper is not identified in this library; see
`Arlib/MDP.lean`).  This file
supplies the missing half of that sentence — the **coupling back to the real
object**: it defines the optimal reachability value semantically, as the
supremum over policies of the probability of reaching `S_T`, and proves it is
the same function.

Everything is finite-horizon-first, so no trajectory measure is needed:
`reachVal k s` is the largest probability, over all policies, of reaching `S_T`
within `k` steps from `s`.  It is monotone in `k` and bounded by `1`, hence
convergent; `Vstar` is its limit, and

    Qsem(s,a) = ∑_{s'} P(s' ∣ s,a) · extVal-of-Vstar (s')

is the state–action value.  The theorem `Qsem_eq_Qstar` closes the loop.
-/
import Arlib.MDP.FixedPoint

namespace Arlib

open scoped BigOperators Topology
open Finset Filter

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A)

/-- **`reachVal k s`** — the largest probability, over all policies, of reaching
a target state within `k` steps from `s`.  Terminal states are absorbing, so the
value is pinned at `1` on `S_T` and `0` on `S_N` at every horizon. -/
noncomputable def reachVal : ℕ → S → ℝ
  | 0, s => if M.isTarget s = true then 1 else 0
  | (k + 1), s =>
      if M.isTerm s = true then (if M.isTarget s = true then 1 else 0)
      else (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * reachVal k s'

theorem reachVal_zero (s : S) :
    M.reachVal 0 s = if M.isTarget s = true then 1 else 0 := rfl

theorem reachVal_succ (k : ℕ) (s : S) :
    M.reachVal (k + 1) s =
      if M.isTerm s = true then (if M.isTarget s = true then 1 else 0)
      else (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * M.reachVal k s' := rfl

/-- On a terminal state the horizon is irrelevant: the value is pinned at `1` on
`S_T` and `0` on `S_N`. -/
theorem reachVal_term (k : ℕ) {s : S} (h : M.isTerm s = true) :
    M.reachVal k s = if M.isTarget s = true then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [M.reachVal_succ, if_pos h]

/-- On a non-terminal state, `reachVal (k+1)` is the one-step lookahead. -/
theorem reachVal_succ_nonterm (k : ℕ) {s : S} (h : M.isTerm s = false) :
    M.reachVal (k + 1) s = (M.enabled s).sup' (M.enabled_nonempty s)
      fun a => ∑ s', M.P s a s' * M.reachVal k s' := by
  rw [M.reachVal_succ, if_neg (by simp [h])]

/-- A non-terminal state is not a target (targets are terminal). -/
theorem isTarget_false_of_isTerm_false {s : S} (h : M.isTerm s = false) :
    M.isTarget s = false := by
  by_contra hc
  have h' : M.isTarget s = true := by simpa using hc
  rw [M.target_isTerm s h'] at h
  exact Bool.noConfusion h

theorem reachVal_nonneg (k : ℕ) (s : S) : 0 ≤ M.reachVal k s := by
  induction k generalizing s with
  | zero => rw [M.reachVal_zero]; split <;> norm_num
  | succ k ih =>
      rw [M.reachVal_succ]
      split
      · split <;> norm_num
      · obtain ⟨a, ha⟩ := M.enabled_nonempty s
        refine le_trans ?_
          (Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.reachVal k s') ha)
        exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg s a s') (ih s')

theorem reachVal_le_one (k : ℕ) (s : S) : M.reachVal k s ≤ 1 := by
  induction k generalizing s with
  | zero => rw [M.reachVal_zero]; split <;> norm_num
  | succ k ih =>
      rw [M.reachVal_succ]
      split
      · split <;> norm_num
      · refine Finset.sup'_le _ _ fun a _ => ?_
        calc ∑ s', M.P s a s' * M.reachVal k s'
            ≤ ∑ s', M.P s a s' * 1 :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s a s')
          _ = 1 := by simpa using M.P_sum_one s a

/-- The horizon can only help: `reachVal` is monotone in `k`. -/
theorem reachVal_mono (k : ℕ) (s : S) : M.reachVal k s ≤ M.reachVal (k + 1) s := by
  induction k generalizing s with
  | zero =>
      by_cases h : M.isTerm s = true
      · rw [M.reachVal_term 0 h, M.reachVal_term 1 h]
      · have h' : M.isTerm s = false := by simpa using h
        rw [M.reachVal_zero, if_neg (by simp [M.isTarget_false_of_isTerm_false h'])]
        exact M.reachVal_nonneg 1 s
  | succ k ih =>
      by_cases h : M.isTerm s = true
      · rw [M.reachVal_term (k + 1) h, M.reachVal_term (k + 2) h]
      · have h' : M.isTerm s = false := by simpa using h
        rw [M.reachVal_succ_nonterm k h', M.reachVal_succ_nonterm (k + 1) h']
        refine Finset.sup'_le _ _ fun a ha => ?_
        refine le_trans ?_
          (Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.reachVal (k + 1) s') ha)
        exact Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s a s')

/-- **`V*(s)`** — the optimal reachability value, as the limit of the
finite-horizon values. -/
noncomputable def Vstar (s : S) : ℝ := ⨆ k, M.reachVal k s

theorem Vstar_def (s : S) : M.Vstar s = ⨆ k, M.reachVal k s := rfl

theorem bddAbove_reachVal (s : S) : BddAbove (Set.range fun k => M.reachVal k s) := by
  refine ⟨1, ?_⟩
  rintro x ⟨k, rfl⟩
  exact M.reachVal_le_one k s

theorem reachVal_le_Vstar (k : ℕ) (s : S) : M.reachVal k s ≤ M.Vstar s :=
  le_ciSup (M.bddAbove_reachVal s) k

theorem Vstar_nonneg (s : S) : 0 ≤ M.Vstar s :=
  le_trans (M.reachVal_nonneg 0 s) (M.reachVal_le_Vstar 0 s)

theorem tendsto_reachVal (s : S) : Tendsto (fun k => M.reachVal k s) atTop (𝓝 (M.Vstar s)) := by
  have hmono : Monotone fun k => M.reachVal k s :=
    monotone_nat_of_le_succ fun k => M.reachVal_mono k s
  exact tendsto_atTop_ciSup hmono (M.bddAbove_reachVal s)

/-- **the `V`-Bellman optimality equation** — `V*` satisfies the Bellman optimality equation. -/
theorem Vstar_eq (s : S) (hs : M.isTerm s = false) :
    M.Vstar s = (M.enabled s).sup' (M.enabled_nonempty s)
      fun a => ∑ s', M.P s a s' * M.Vstar s' := by
  refine le_antisymm ?_ ?_
  · -- `≤`: every finite horizon is dominated by the one-step lookahead of `V*`.
    have hstep : ∀ k : ℕ, M.reachVal (k + 1) s ≤
        (M.enabled s).sup' (M.enabled_nonempty s)
          fun a => ∑ s', M.P s a s' * M.Vstar s' := by
      intro k
      rw [M.reachVal_succ_nonterm k hs]
      refine Finset.sup'_le _ _ fun a ha => ?_
      refine le_trans ?_
        (Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.Vstar s') ha)
      exact Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (M.reachVal_le_Vstar k s') (M.P_nonneg s a s')
    rw [M.Vstar_def]
    refine ciSup_le fun k => ?_
    cases k with
    | zero => exact (M.reachVal_mono 0 s).trans (hstep 0)
    | succ k => exact hstep k
  · -- `≥`: pass to the limit inside the finite sum.
    refine Finset.sup'_le _ _ fun a ha => ?_
    have hlim : Tendsto (fun k => ∑ s', M.P s a s' * M.reachVal k s') atTop
        (𝓝 (∑ s', M.P s a s' * M.Vstar s')) :=
      tendsto_finset_sum _ fun s' _ => (M.tendsto_reachVal s').const_mul (M.P s a s')
    refine le_of_tendsto hlim ?_
    filter_upwards with k
    calc ∑ s', M.P s a s' * M.reachVal k s' ≤ M.reachVal (k + 1) s := by
          rw [M.reachVal_succ_nonterm k hs]
          exact Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.reachVal k s') ha
      _ ≤ M.Vstar s := M.reachVal_le_Vstar (k + 1) s

@[simp] theorem Vstar_target {s : S} (h : M.isTarget s = true) : M.Vstar s = 1 := by
  have hk : ∀ k : ℕ, M.reachVal k s = 1 := fun k => by
    rw [M.reachVal_term k (M.target_isTerm s h), if_pos h]
  rw [M.Vstar_def]
  simp only [hk]
  exact ciSup_const

@[simp] theorem Vstar_nontarget {s : S} (h : M.isTerm s = true) (h' : M.isTarget s = false) :
    M.Vstar s = 0 := by
  have hk : ∀ k : ℕ, M.reachVal k s = 0 := fun k => by
    rw [M.reachVal_term k h, if_neg (by simp [h'])]
  rw [M.Vstar_def]
  simp only [hk]
  exact ciSup_const

/-- **the optimal reachability `Q`-value / the `Q`-Bellman optimality equation** — the optimal state–action reachability value. -/
noncomputable def Qsem (s : S) (a : A) : ℝ := ∑ s', M.P s a s' * M.Vstar s'

theorem Qsem_apply (s : S) (a : A) : M.Qsem s a = ∑ s', M.P s a s' * M.Vstar s' := rfl

/-- The boundary extension of `Qsem` is exactly `V*`: `1` on `S_T`, `0` on `S_N`,
and `max_{a'} Qsem(s',a') = V*(s')` on `Sₙₜ` by the Bellman equation. -/
theorem extVal_Qsem (s : S) : M.extVal (fun s a => M.Qsem s a) s = M.Vstar s := by
  by_cases ht : M.isTerm s = true
  · by_cases htg : M.isTarget s = true
    · rw [M.extVal_target htg, M.Vstar_target htg]
    · have htg' : M.isTarget s = false := by simpa using htg
      rw [M.extVal_nontarget ht htg', M.Vstar_nontarget ht htg']
  · have ht' : M.isTerm s = false := by simpa using ht
    rw [M.extVal_nonterm ht', M.Vstar_eq s ht']
    rfl

/-- **`Qsem` is a fixed point of the Bellman optimality operator `H`.**  This is
the bridge from the semantics to `Arlib.MDP.FixedPoint`. -/
theorem H_Qsem : M.H (fun s a => M.Qsem s a) = fun s a => M.Qsem s a := by
  funext s a
  rw [M.H_apply]
  simp only [M.extVal_Qsem]
  rfl

/-- **The coupling.**  The semantic optimal value — the actual probability of
reaching `S_T` — is the fixed point `Q*` that `Arlib.MDP.FixedPoint`
constructs and the convergence theorem proves the algorithm converges to.  This is what makes
the headline theorem a statement about the *real* object. -/
theorem Qsem_eq_Qstar (hw : HittingWeight M) (s : S) (a : A)
    (hs : M.isTerm s = false) (ha : a ∈ M.enabled s) : M.Qsem s a = M.Qstar s a :=
  M.eq_Qstar_of_fixed hw M.H_Qsem hs ha

/-- `V*(s) = max_{a ∈ A(s)} Q*(s,a)` — the standard "recovers the state values by
`V*(s) = max_a Q*(s,a)`". -/
theorem Vstar_eq_vmax_Qstar (hw : HittingWeight M) (s : S) (hs : M.isTerm s = false) :
    M.Vstar s = M.vmax M.Qstar s := by
  rw [M.Vstar_eq s hs]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun a ha => ?_
    have h : ∑ s', M.P s a s' * M.Vstar s' = M.Qstar s a := M.Qsem_eq_Qstar hw s a hs ha
    rw [h]
    exact M.le_vmax ha
  · refine M.vmax_le fun a ha => ?_
    have h : M.Qstar s a = ∑ s', M.P s a s' * M.Vstar s' :=
      (M.Qsem_eq_Qstar hw s a hs ha).symm
    rw [h]
    exact Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.Vstar s') ha

end MDP

end Arlib
