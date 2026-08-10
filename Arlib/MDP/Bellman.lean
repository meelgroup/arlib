/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The Bellman optimality operator `H` for reachability

    (H Q)(s,a) := ∑_{s' ∈ S_T} P(s' ∣ s,a)  +  ∑_{s' ∈ Sₙₜ} P(s' ∣ s,a) · max_{a'} Q(s',a')

We define `H` through the **boundary extension** `extVal Q : S → ℝ`, which reads
a state's one-step contribution: `1` on a target, `0` on a non-target terminal,
and the greedy value `max_{a'} Q(s',a')` on a non-terminal.  Then

    H Q (s,a) = kernel.act (extVal Q) (s,a) = ∑ s', P(s' ∣ s,a) · extVal Q s'

which is the `FinKernel.act` verbatim, so the algebra of the operator
(`act_sub`, `act_const`) is inherited.  `H_eq_sum_target_add_sum_nonterm`
proves this agrees with the two-sum display of the source paper (not identified
in this library; see `Arlib/MDP.lean`), so the reader can audit
the definition against the Bellman optimality operator without unfolding
anything.
-/
import Arlib.MDP.Basic

namespace Arlib

open scoped BigOperators
open Finset MarkovChains

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A)

/-- **The boundary extension of a `Q`-table.**  The value a successor `s'`
contributes to a one-step lookahead: `1` on a target state, `0` on a non-target
terminal, and `max_{a'} Q(s',a')` on a non-terminal.  This is the standard
"`V^π` and `Q^π` equal `1` on `S_T` and `0` on `S_N` for every `π`". -/
noncomputable def extVal (Q : S → A → ℝ) : S → ℝ := fun s' =>
  if M.isTerm s' = true then (if M.isTarget s' = true then (1 : ℝ) else 0) else M.vmax Q s'

@[simp] theorem extVal_target {Q : S → A → ℝ} {s : S} (h : M.isTarget s = true) :
    M.extVal Q s = 1 := by
  simp [extVal, M.target_isTerm s h, h]

@[simp] theorem extVal_nontarget {Q : S → A → ℝ} {s : S}
    (h : M.isTerm s = true) (h' : M.isTarget s = false) : M.extVal Q s = 0 := by
  simp [extVal, h, h']

@[simp] theorem extVal_nonterm {Q : S → A → ℝ} {s : S} (h : M.isTerm s = false) :
    M.extVal Q s = M.vmax Q s := by simp [extVal, h]

/-- **The Bellman optimality operator `H`** (the Bellman optimality operator). -/
noncomputable def H (Q : S → A → ℝ) : S → A → ℝ := fun s a =>
  M.kernel.act (M.extVal Q) (s, a)

theorem H_apply (Q : S → A → ℝ) (s : S) (a : A) :
    M.H Q s a = ∑ s', M.P s a s' * M.extVal Q s' := rfl

/-- **Audit against the Bellman optimality operator.**  The definition above is literally
the standard display:

    (H Q)(s,a) = ∑_{s' ∈ S_T} P(s'∣s,a) + ∑_{s' ∈ Sₙₜ} P(s'∣s,a)·max_{a'} Q(s',a'). -/
theorem H_eq_sum_target_add_sum_nonterm (Q : S → A → ℝ) (s : S) (a : A) :
    M.H Q s a =
      (∑ s' ∈ M.targetSet, M.P s a s')
        + ∑ s' ∈ M.nontermSet, M.P s a s' * M.vmax Q s' := by
  rw [H_apply]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s' => M.isTerm s' = true)]
  have hnt : (univ.filter fun s' => ¬ (M.isTerm s' = true)) = M.nontermSet := by
    ext s'; simp [nontermSet]
  rw [hnt]
  congr 1
  · -- the terminal part: targets contribute `P`, non-targets contribute `0`
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun s' => M.isTerm s' = true)
        (fun s' => M.isTarget s' = true)]
    have h1 : ((univ.filter fun s' => M.isTerm s' = true).filter
        fun s' => M.isTarget s' = true) = M.targetSet := by
      ext s'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_targetSet]
      exact ⟨fun h => h.2, fun h => ⟨M.target_isTerm s' h, h⟩⟩
    have h2 : ∀ s' ∈ ((univ.filter fun s' => M.isTerm s' = true).filter
        fun s' => ¬ (M.isTarget s' = true)), M.P s a s' * M.extVal Q s' = 0 := by
      intro s' hs'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
      rw [M.extVal_nontarget hs'.1 (by simpa using hs'.2), mul_zero]
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    rw [M.extVal_target ((mem_targetSet M).1 hs'), mul_one]
  · refine Finset.sum_congr rfl fun s' hs' => ?_
    rw [M.extVal_nonterm ((mem_nontermSet M).1 hs')]

/-- The difference of two one-step lookaheads is the kernel acting on the
difference of the boundary extensions — the first line of the contraction proof
of the contraction property, and where the target terms cancel. -/
theorem H_sub (Q Q' : S → A → ℝ) (s : S) (a : A) :
    M.H Q s a - M.H Q' s a = ∑ s', M.P s a s' * (M.extVal Q s' - M.extVal Q' s') := by
  rw [H_apply, H_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s' _ => by ring

/-- On terminal states the two boundary extensions agree — this is the
cancellation the literature performs when it writes "the target terms
of the Bellman optimality operator cancel". -/
theorem extVal_sub_eq_zero_of_term {Q Q' : S → A → ℝ} {s : S} (h : M.isTerm s = true) :
    M.extVal Q s - M.extVal Q' s = 0 := by
  by_cases ht : M.isTarget s = true
  · rw [M.extVal_target ht, M.extVal_target ht, sub_self]
  · rw [M.extVal_nontarget h (by simpa using ht), M.extVal_nontarget h (by simpa using ht),
      sub_self]

end MDP

end Arlib
