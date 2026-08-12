/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The value `V^π` of a policy, greedy optimality, and the asymptotic guarantee

`Arlib.MDP.Reachability` builds the *optimal* reachability value `V*` as the
limit of the finite-horizon optimal values.  This file does the same one policy
at a time, and then closes the loop with the asymptotic guarantee.

* `reachValPi π k s` — the probability of reaching `S_T` within `k` steps from
  `s` **under the stationary deterministic policy `π`**; `Vpi π = ⨆ k` is its
  limit, the standard `V^π` of the optimal reachability value.  Every lemma of `Reachability.lean`
  transfers verbatim with the `max` over `A(s)` replaced by the single action
  `π s`.
* `Vpi_le_Vstar` — `V^π ≤ V*` for every valid `π`.
* `Hpi` — the *policy* Bellman operator, a `β`-contraction in the very same
  hitting-time weighted norm as `H` (`Hpi_contraction`, proved by the same
  computation as `MDP.H_contraction`, only with the `max` deleted), hence with a
  unique fixed point on `Sₙₜ` (`eq_of_Hpi_fixed`).
* `Vpi_eq_Vstar` — **a policy that is greedy for `Q*` is optimal**: `V^π = V*`
  whenever every `π s` attains `max_a Q*(s,a)`.  Both `V^π` and `V*` solve the
  same `π`-linear system, so the contraction identifies them.
* `greedy_eventually_optimal` — if `Q_t → Q*` pointwise then, eventually, every
  greedy action of `Q_t` is *already* a maximiser of `Q*`.  The greedy policy
  itself may oscillate forever among tied optimal actions; what stabilises is
  the set it oscillates in.  Finiteness gives a strictly positive gap between
  the optimum and the best strictly-suboptimal value (`exists_gap`).
* `tendsto_Vpi_greedy` — the payoff, and the asymptotic guarantee on the nose:
  `V^{π_t}(s₀) → V*(s₀)` for the induced greedy policies `π_t`.
-/
import Arlib.MDP.Reachability

namespace Arlib

open scoped BigOperators Topology
open Finset Filter

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

/-! ## Finite-horizon values of a stationary deterministic policy -/

/-- **`reachValPi π k s`** — the probability of reaching a target state within
`k` steps from `s` when the actions are chosen by the stationary deterministic
policy `π`.  This is `MDP.reachVal` with the maximisation over `A(s)` replaced
by the single action `π s`. -/
noncomputable def reachValPi (M : MDP S A) (π : S → A) : ℕ → S → ℝ
  | 0, s => if M.isTarget s = true then 1 else 0
  | (k + 1), s =>
      if M.isTerm s = true then (if M.isTarget s = true then 1 else 0)
      else ∑ s', M.P s (π s) s' * reachValPi M π k s'

variable (M : MDP S A)

section Policy

variable (π : S → A)

theorem reachValPi_zero (s : S) :
    M.reachValPi π 0 s = if M.isTarget s = true then 1 else 0 := rfl

theorem reachValPi_succ (k : ℕ) (s : S) :
    M.reachValPi π (k + 1) s =
      if M.isTerm s = true then (if M.isTarget s = true then 1 else 0)
      else ∑ s', M.P s (π s) s' * M.reachValPi π k s' := rfl

/-- On a terminal state the horizon is irrelevant: the value is pinned at `1` on
`S_T` and `0` on `S_N`, for every policy. -/
theorem reachValPi_term (k : ℕ) {s : S} (h : M.isTerm s = true) :
    M.reachValPi π k s = if M.isTarget s = true then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [M.reachValPi_succ, if_pos h]

/-- On a non-terminal state, `reachValPi (k+1)` is the one-step lookahead along
the action `π s`. -/
theorem reachValPi_succ_nonterm (k : ℕ) {s : S} (h : M.isTerm s = false) :
    M.reachValPi π (k + 1) s = ∑ s', M.P s (π s) s' * M.reachValPi π k s' := by
  rw [M.reachValPi_succ, if_neg (by simp [h])]

theorem reachValPi_nonneg (k : ℕ) (s : S) : 0 ≤ M.reachValPi π k s := by
  induction k generalizing s with
  | zero => rw [M.reachValPi_zero]; split <;> norm_num
  | succ k ih =>
      rw [M.reachValPi_succ]
      split
      · split <;> norm_num
      · exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg s (π s) s') (ih s')

theorem reachValPi_le_one (k : ℕ) (s : S) : M.reachValPi π k s ≤ 1 := by
  induction k generalizing s with
  | zero => rw [M.reachValPi_zero]; split <;> norm_num
  | succ k ih =>
      rw [M.reachValPi_succ]
      split
      · split <;> norm_num
      · calc ∑ s', M.P s (π s) s' * M.reachValPi π k s'
            ≤ ∑ s', M.P s (π s) s' * 1 :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s (π s) s')
          _ = 1 := by simpa using M.P_sum_one s (π s)

/-- The horizon can only help: `reachValPi` is monotone in `k`. -/
theorem reachValPi_mono (k : ℕ) (s : S) :
    M.reachValPi π k s ≤ M.reachValPi π (k + 1) s := by
  induction k generalizing s with
  | zero =>
      by_cases h : M.isTerm s = true
      · rw [M.reachValPi_term π 0 h, M.reachValPi_term π 1 h]
      · have h' : M.isTerm s = false := by simpa using h
        rw [M.reachValPi_zero, if_neg (by simp [M.isTarget_false_of_isTerm_false h'])]
        exact M.reachValPi_nonneg π 1 s
  | succ k ih =>
      by_cases h : M.isTerm s = true
      · rw [M.reachValPi_term π (k + 1) h, M.reachValPi_term π (k + 2) h]
      · have h' : M.isTerm s = false := by simpa using h
        rw [M.reachValPi_succ_nonterm π k h', M.reachValPi_succ_nonterm π (k + 1) h']
        exact Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s (π s) s')

/-- **`V^π(s)` (the optimal reachability value)** — the probability of reaching `S_T` from `s` under
the stationary deterministic policy `π`, as the limit of the finite-horizon
values. -/
noncomputable def Vpi (M : MDP S A) (π : S → A) (s : S) : ℝ := ⨆ k, M.reachValPi π k s

theorem Vpi_def (s : S) : M.Vpi π s = ⨆ k, M.reachValPi π k s := rfl

theorem bddAbove_reachValPi (s : S) :
    BddAbove (Set.range fun k => M.reachValPi π k s) := by
  refine ⟨1, ?_⟩
  rintro x ⟨k, rfl⟩
  exact M.reachValPi_le_one π k s

theorem reachValPi_le_Vpi (k : ℕ) (s : S) : M.reachValPi π k s ≤ M.Vpi π s :=
  le_ciSup (M.bddAbove_reachValPi π s) k

theorem Vpi_nonneg (s : S) : 0 ≤ M.Vpi π s :=
  le_trans (M.reachValPi_nonneg π 0 s) (M.reachValPi_le_Vpi π 0 s)

theorem Vpi_le_one (s : S) : M.Vpi π s ≤ 1 :=
  ciSup_le fun k => M.reachValPi_le_one π k s

theorem tendsto_reachValPi (s : S) :
    Tendsto (fun k => M.reachValPi π k s) atTop (𝓝 (M.Vpi π s)) := by
  have hmono : Monotone fun k => M.reachValPi π k s :=
    monotone_nat_of_le_succ fun k => M.reachValPi_mono π k s
  exact tendsto_atTop_ciSup hmono (M.bddAbove_reachValPi π s)

@[simp] theorem Vpi_target {s : S} (h : M.isTarget s = true) : M.Vpi π s = 1 := by
  have hk : ∀ k : ℕ, M.reachValPi π k s = 1 := fun k => by
    rw [M.reachValPi_term π k (M.target_isTerm s h), if_pos h]
  rw [M.Vpi_def]
  simp only [hk]
  exact ciSup_const

@[simp] theorem Vpi_nontarget {s : S} (h : M.isTerm s = true) (h' : M.isTarget s = false) :
    M.Vpi π s = 0 := by
  have hk : ∀ k : ℕ, M.reachValPi π k s = 0 := fun k => by
    rw [M.reachValPi_term π k h, if_neg (by simp [h'])]
  rw [M.Vpi_def]
  simp only [hk]
  exact ciSup_const

/-- **The fixed-point equation for `V^π`**: on a non-terminal state, `V^π` is
its own one-step lookahead along `π`. -/
theorem Vpi_eq {s : S} (hs : M.isTerm s = false) :
    M.Vpi π s = ∑ s', M.P s (π s) s' * M.Vpi π s' := by
  have h1 : Tendsto (fun k => M.reachValPi π (k + 1) s) atTop (𝓝 (M.Vpi π s)) :=
    (M.tendsto_reachValPi π s).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => ∑ s', M.P s (π s) s' * M.reachValPi π k s') atTop
      (𝓝 (∑ s', M.P s (π s) s' * M.Vpi π s')) :=
    tendsto_finsetSum _ fun s' _ => (M.tendsto_reachValPi π s').const_mul (M.P s (π s) s')
  exact tendsto_nhds_unique
    (Filter.Tendsto.congr (fun k => M.reachValPi_succ_nonterm π k hs) h1) h2

/-! ## `V^π ≤ V*` -/

/-- Every horizon-`k` policy value is dominated by the horizon-`k` optimum. -/
theorem reachValPi_le_reachVal (hmem : ∀ s, π s ∈ M.enabled s) (k : ℕ) (s : S) :
    M.reachValPi π k s ≤ M.reachVal k s := by
  induction k generalizing s with
  | zero => rw [M.reachValPi_zero, M.reachVal_zero]
  | succ k ih =>
      by_cases h : M.isTerm s = true
      · rw [M.reachValPi_term π (k + 1) h, M.reachVal_term (k + 1) h]
      · have h' : M.isTerm s = false := by simpa using h
        rw [M.reachValPi_succ_nonterm π k h', M.reachVal_succ_nonterm k h']
        refine le_trans (Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s (π s) s')) ?_
        exact Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.reachVal k s') (hmem s)

/-- **`V^π ≤ V*`** — no policy beats the optimum. -/
theorem Vpi_le_Vstar (hmem : ∀ s, π s ∈ M.enabled s) (s : S) : M.Vpi π s ≤ M.Vstar s :=
  ciSup_le fun k =>
    le_trans (M.reachValPi_le_reachVal π hmem k s) (M.reachVal_le_Vstar k s)

end Policy

/-! ## The policy Bellman operator and its contraction -/

/-- `max_{a ∈ A(s)}` of a table that does not depend on the action is the value
itself — the bridge that lets a state function `f : S → ℝ` be fed to `extVal`
(and hence reuse the whole `Bellman` toolkit) as the constant table
`fun s _ => f s`. -/
theorem vmax_lift (f : S → ℝ) (s : S) : M.vmax (fun s _ => f s) s = f s := by
  obtain ⟨a, ha⟩ := M.enabled_nonempty s
  exact le_antisymm (M.vmax_le fun _ _ => le_rfl)
    (M.le_vmax (Q := fun s _ => f s) ha)

/-- **The policy Bellman operator `H^π`** — `H` with the maximisation over `A(s)`
replaced by the single action `π s`. -/
noncomputable def Hpi (M : MDP S A) (π : S → A) (f : S → ℝ) : S → ℝ := fun s =>
  ∑ s', M.P s (π s) s' * M.extVal (fun s _ => f s) s'

theorem Hpi_apply (π : S → A) (f : S → ℝ) (s : S) :
    M.Hpi π f s = ∑ s', M.P s (π s) s' * M.extVal (fun s _ => f s) s' := rfl

theorem Hpi_sub (π : S → A) (f g : S → ℝ) (s : S) :
    M.Hpi π f s - M.Hpi π g s =
      ∑ s', M.P s (π s) s' *
        (M.extVal (fun s _ => f s) s' - M.extVal (fun s _ => g s) s') := by
  rw [Hpi_apply, Hpi_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s' _ => by ring

/-- **the contraction property for a fixed policy, pointwise form.**  Identical to
`MDP.H_contraction_WLe` — the target terms cancel, `HittingWeight.step` supplies
`∑ P·T ≤ T_s − 1`, and `HittingWeight.sub_one_le_beta_mul` supplies
`T_s − 1 ≤ β·T_s`.  The only change is that the `max` over `A(s)` has become the
single action `π s`, which removes the need for `abs_vmax_sub_le`. -/
theorem Hpi_contraction_WLe (hw : HittingWeight M) {π : S → A}
    (hmem : ∀ s, π s ∈ M.enabled s) {f g : S → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : M.WLe hw.w (fun s _ => f s - g s) c) :
    M.WLe hw.w (fun s _ => M.Hpi π f s - M.Hpi π g s) (hw.beta * c) := by
  intro s a hs ha
  show |M.Hpi π f s - M.Hpi π g s| ≤ hw.beta * c * hw.w s a
  have hext : M.WLe hw.w
      (fun s a => (fun s _ => f s) s a - (fun s _ => g s) s a) c := h
  have h1 : |∑ s', M.P s (π s) s' *
      (M.extVal (fun s _ => f s) s' - M.extVal (fun s _ => g s) s')|
      ≤ ∑ s', M.P s (π s) s' * (c * hw.T s') := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun s' _ => ?_)
    rw [abs_mul, abs_of_nonneg (M.P_nonneg s (π s) s')]
    exact mul_le_mul_of_nonneg_left
      (M.abs_extVal_sub_le hw hext s') (M.P_nonneg s (π s) s')
  have h2 : ∑ s', M.P s (π s) s' * (c * hw.T s') = c * ∑ s', M.P s (π s) s' * hw.T s' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  have h3 : (∑ s', M.P s (π s) s' * hw.T s') ≤ hw.T s - 1 := by
    have := hw.step s (π s) hs (hmem s); linarith
  have h4 : c * (∑ s', M.P s (π s) s' * hw.T s') ≤ c * (hw.T s - 1) :=
    mul_le_mul_of_nonneg_left h3 hc
  have h5 : c * (hw.T s - 1) ≤ c * (hw.beta * hw.T s) :=
    mul_le_mul_of_nonneg_left (hw.sub_one_le_beta_mul hs) hc
  have h6 : hw.beta * c * hw.w s a = c * (hw.beta * hw.T s) := by
    show hw.beta * c * hw.T s = c * (hw.beta * hw.T s)
    ring
  rw [M.Hpi_sub, h6]
  linarith

/-- **`H^π` is a `β`-contraction** in the hitting-time weighted maximum norm,
with the same `β = 1 − 1/max_{s ∈ Sₙₜ} T_s` as `MDP.H_contraction`. -/
theorem Hpi_contraction (hw : HittingWeight M) {π : S → A}
    (hmem : ∀ s, π s ∈ M.enabled s) (f g : S → ℝ) :
    M.wnorm hw.w (fun s _ => M.Hpi π f s - M.Hpi π g s)
      ≤ hw.beta * M.wnorm hw.w (fun s _ => f s - g s) :=
  M.wnorm_le_of_WLe hw.w_pos (mul_nonneg hw.beta_nonneg (M.wnorm_nonneg _ _))
    (M.Hpi_contraction_WLe hw hmem (M.wnorm_nonneg _ _) (M.WLe_wnorm hw.w_pos))

/-- **Uniqueness of the fixed point of `H^π` on `Sₙₜ`.**  Banach, by the same
one-line argument as `MDP.eq_Qstar_of_fixed`: the weighted norm of the
difference is `≤ β` times itself, hence `0`.  (Off `Sₙₜ` there is nothing to
prove: `H^π` reads its argument only through `extVal`, which pins the terminal
values at `1`/`0` regardless of `f`.) -/
theorem eq_of_Hpi_fixed (hw : HittingWeight M) {π : S → A}
    (hmem : ∀ s, π s ∈ M.enabled s) {f g : S → ℝ}
    (hf : ∀ s, M.isTerm s = false → M.Hpi π f s = f s)
    (hg : ∀ s, M.isTerm s = false → M.Hpi π g s = g s)
    {s : S} (hs : M.isTerm s = false) : f s = g s := by
  set N := M.wnorm hw.w (fun s _ => f s - g s) with hNdef
  have h0 : 0 ≤ N := M.wnorm_nonneg _ _
  have hstep := M.Hpi_contraction_WLe hw hmem h0 (M.WLe_wnorm (Q := fun s _ => f s - g s)
    hw.w_pos)
  have hWLe2 : M.WLe hw.w (fun s _ => f s - g s) (hw.beta * N) := by
    intro s' a hs' ha
    have h1 : |M.Hpi π f s' - M.Hpi π g s'| ≤ hw.beta * N * hw.w s' a := hstep s' a hs' ha
    rw [hf s' hs', hg s' hs'] at h1
    exact h1
  have hle : N ≤ hw.beta * N :=
    M.wnorm_le_of_WLe hw.w_pos (mul_nonneg hw.beta_nonneg h0) hWLe2
  have hb := hw.beta_lt_one
  have hNzero : N = 0 := by nlinarith [hle, h0, hb]
  have := M.eq_zero_of_wnorm_eq_zero (w := hw.w) (Q := fun s _ => f s - g s)
    hw.w_pos (by rw [← hNdef]; exact hNzero) hs (hmem s)
  exact sub_eq_zero.1 this

/-! ## Greedy policies are optimal -/

/-- The boundary extension of (the constant lift of) `V^π` is `V^π` itself:
`V^π = 1` on `S_T` and `0` on `S_N`, as the literature records. -/
theorem extVal_Vpi (π : S → A) (s : S) :
    M.extVal (fun s _ => M.Vpi π s) s = M.Vpi π s := by
  by_cases ht : M.isTerm s = true
  · by_cases htg : M.isTarget s = true
    · rw [M.extVal_target htg, M.Vpi_target π htg]
    · have htg' : M.isTarget s = false := by simpa using htg
      rw [M.extVal_nontarget ht htg', M.Vpi_nontarget π ht htg']
  · rw [M.extVal_nonterm (by simpa using ht), M.vmax_lift]

/-- The boundary extension of (the constant lift of) `V*` is `V*`. -/
theorem extVal_Vstar (s : S) : M.extVal (fun s _ => M.Vstar s) s = M.Vstar s := by
  by_cases ht : M.isTerm s = true
  · by_cases htg : M.isTarget s = true
    · rw [M.extVal_target htg, M.Vstar_target htg]
    · have htg' : M.isTarget s = false := by simpa using htg
      rw [M.extVal_nontarget ht htg', M.Vstar_nontarget ht htg']
  · rw [M.extVal_nonterm (by simpa using ht), M.vmax_lift]

/-- `V^π` is a fixed point of `H^π` on the non-terminal states. -/
theorem Hpi_Vpi (π : S → A) {s : S} (hs : M.isTerm s = false) :
    M.Hpi π (M.Vpi π) s = M.Vpi π s := by
  rw [M.Hpi_apply]
  simp only [M.extVal_Vpi π]
  exact (M.Vpi_eq π hs).symm

/-- **`V*` is a fixed point of `H^π` whenever `π` is greedy for `Q*`.**  By
`MDP.Vstar_eq` the optimal value is the *maximum* over `A(s)` of the one-step
lookaheads, and `MDP.Qsem_eq_Qstar` says that lookahead is `Q*(s,a)`; so the
maximum is attained exactly at the maximisers of `Q*(s,·)`, `π s` among them. -/
theorem Hpi_Vstar (hw : HittingWeight M) {π : S → A} (hmem : ∀ s, π s ∈ M.enabled s)
    (hopt : ∀ s, M.isTerm s = false → M.Qstar s (π s) = M.vmax M.Qstar s)
    {s : S} (hs : M.isTerm s = false) : M.Hpi π M.Vstar s = M.Vstar s := by
  rw [M.Hpi_apply]
  simp only [M.extVal_Vstar]
  have h1 : ∑ s', M.P s (π s) s' * M.Vstar s' = M.Qstar s (π s) :=
    M.Qsem_eq_Qstar hw s (π s) hs (hmem s)
  rw [h1, hopt s hs, ← M.Vstar_eq_vmax_Qstar hw s hs]

/-- **Any policy that is everywhere greedy for `Q*` is optimal**: `V^π = V*`.

This is the general form of `Vpi_greedy_Qstar`: all that is used of `π` is that
`π s` attains `max_{a ∈ A(s)} Q*(s,a)` at every non-terminal `s` — *which*
maximiser is irrelevant.  That generality is what makes the tie-breaking
oscillation of a learnt greedy policy harmless in `tendsto_Vpi_greedy`. -/
theorem Vpi_eq_Vstar (hw : HittingWeight M) {π : S → A} (hmem : ∀ s, π s ∈ M.enabled s)
    (hopt : ∀ s, M.isTerm s = false → M.Qstar s (π s) = M.vmax M.Qstar s) (s : S) :
    M.Vpi π s = M.Vstar s := by
  by_cases ht : M.isTerm s = true
  · by_cases htg : M.isTarget s = true
    · rw [M.Vpi_target π htg, M.Vstar_target htg]
    · have htg' : M.isTarget s = false := by simpa using htg
      rw [M.Vpi_nontarget π ht htg', M.Vstar_nontarget ht htg']
  · exact M.eq_of_Hpi_fixed hw hmem (fun s' hs' => M.Hpi_Vpi π hs')
      (fun s' hs' => M.Hpi_Vstar hw hmem hopt hs') (by simpa using ht)

/-! ## The greedy policy of a table -/

/-- **`greedyOf M Q`** — a stationary deterministic policy choosing, at each
state, some `argmax_{a ∈ A(s)} Q(s,a)`.  Ties are broken by `Classical.choose`;
nothing below depends on how. -/
noncomputable def greedyOf (M : MDP S A) (Q : S → A → ℝ) (s : S) : A :=
  Classical.choose ((M.enabled s).exists_max_image (fun a => Q s a) (M.enabled_nonempty s))

theorem greedyOf_mem (Q : S → A → ℝ) (s : S) : greedyOf M Q s ∈ M.enabled s :=
  (Classical.choose_spec
    ((M.enabled s).exists_max_image (fun a => Q s a) (M.enabled_nonempty s))).1

theorem le_greedyOf (Q : S → A → ℝ) {s : S} {a : A} (ha : a ∈ M.enabled s) :
    Q s a ≤ Q s (greedyOf M Q s) :=
  (Classical.choose_spec
    ((M.enabled s).exists_max_image (fun a => Q s a) (M.enabled_nonempty s))).2 a ha

/-- The greedy action attains the greedy value. -/
theorem greedyOf_eq_vmax (Q : S → A → ℝ) (s : S) :
    Q s (greedyOf M Q s) = M.vmax Q s :=
  le_antisymm (M.le_vmax (M.greedyOf_mem Q s)) (M.vmax_le fun _ ha => M.le_greedyOf Q ha)

/-- **`V^{greedy(Q*)} = V*`** — the greedy policy of `Q*` is an optimal policy,
and its value is the optimal reachability value.  Special case of
`Vpi_eq_Vstar`. -/
theorem Vpi_greedy_Qstar (hw : HittingWeight M) (s : S) :
    Vpi M (greedyOf M M.Qstar) s = M.Vstar s :=
  M.Vpi_eq_Vstar hw (M.greedyOf_mem M.Qstar)
    (fun s' _ => M.greedyOf_eq_vmax M.Qstar s') s

/-! ## Ties are eventually resolved -/

/-- **The optimality gap at a state.**  `S` and `A` are finite, so either every
enabled action attains `max_{a ∈ A(s)} Q(s,a)`, or there is a strictly positive
gap `δ` below the maximum containing no value of `Q(s,·)` at all.  Either way,
any enabled action whose value is within `δ` of the maximum *is* a maximiser. -/
theorem exists_gap (Q : S → A → ℝ) (s : S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ M.enabled s, M.vmax Q s - δ < Q s a → Q s a = M.vmax Q s := by
  classical
  set F := (M.enabled s).filter (fun a => Q s a ≠ M.vmax Q s) with hF
  by_cases hne : F.Nonempty
  · have hlt : F.sup' hne (fun a => Q s a) < M.vmax Q s := by
      rw [Finset.sup'_lt_iff]
      intro a ha
      rw [hF, Finset.mem_filter] at ha
      exact lt_of_le_of_ne (M.le_vmax ha.1) ha.2
    refine ⟨M.vmax Q s - F.sup' hne (fun a => Q s a), by linarith, ?_⟩
    intro a ha hgt
    by_contra hcon
    have haF : a ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨ha, hcon⟩
    have hle : Q s a ≤ F.sup' hne (fun a => Q s a) := Finset.le_sup' _ haF
    rw [sub_sub_cancel] at hgt
    linarith
  · refine ⟨1, one_pos, fun a ha _ => ?_⟩
    by_contra hcon
    exact hne ⟨a, by rw [hF, Finset.mem_filter]; exact ⟨ha, hcon⟩⟩

-- `hw` is carried for uniformity with the rest of the section; the gap argument
-- below is pure finiteness and does not consume it.
set_option linter.unusedVariables false in
/-- **Eventually, every greedy action of `Q_t` maximises `Q*`.**

The greedy policy induced by `Q_t` need not converge — with ties among optimal
actions it may oscillate forever — but the *set* it oscillates in stabilises:
once `Q_t` is within half the optimality gap of `Q*` at every enabled pair, an
action maximising `Q_t(s,·)` is necessarily a maximiser of `Q*(s,·)`.  This is
the finiteness of `S` and `A` doing the work, and it is the crux of
the asymptotic guarantee. -/
theorem greedy_eventually_optimal (hw : HittingWeight M) {Q : ℕ → S → A → ℝ}
    (h : ∀ s a, M.isTerm s = false → a ∈ M.enabled s →
      Filter.Tendsto (fun t => Q t s a) Filter.atTop (nhds (M.Qstar s a))) :
    ∀ᶠ t in Filter.atTop, ∀ s, M.isTerm s = false →
      M.Qstar s (greedyOf M (Q t) s) = M.vmax M.Qstar s := by
  rw [Filter.eventually_all]
  intro s
  by_cases hs : M.isTerm s = false
  · obtain ⟨δ, hδ, hgap⟩ := M.exists_gap M.Qstar s
    have hev : ∀ a ∈ M.enabled s, ∀ᶠ t in atTop, |Q t s a - M.Qstar s a| < δ / 2 := by
      intro a ha
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h s a hs ha) (δ / 2) (by linarith)
      exact eventually_atTop.2 ⟨N, fun t ht => by simpa [Real.dist_eq] using hN t ht⟩
    filter_upwards [(Filter.eventually_all_finset (M.enabled s)).2 hev] with t ht _
    -- the greedy action of `Q t`, and a genuine maximiser of `Q*`
    have hg : greedyOf M (Q t) s ∈ M.enabled s := M.greedyOf_mem (Q t) s
    have ha : greedyOf M M.Qstar s ∈ M.enabled s := M.greedyOf_mem M.Qstar s
    have h1 : Q t s (greedyOf M M.Qstar s) ≤ Q t s (greedyOf M (Q t) s) :=
      M.le_greedyOf (Q t) ha
    have h2 := abs_lt.1 (ht _ hg)
    have h3 := abs_lt.1 (ht _ ha)
    have h4 : M.Qstar s (greedyOf M M.Qstar s) = M.vmax M.Qstar s :=
      M.greedyOf_eq_vmax M.Qstar s
    refine hgap _ hg ?_
    -- `Q*(s,g) > Q_t(s,g) − δ/2 ≥ Q_t(s,a*) − δ/2 > Q*(s,a*) − δ = max − δ`
    rw [← h4]
    linarith [h1, h2.1, h2.2, h3.1, h3.2]
  · exact Filter.Eventually.of_forall fun t hcon => absurd hcon hs

-- `hinit` is the standing assumption that `s₀` is non-terminal; the
-- proof does not need it, since `Vpi_eq_Vstar` also holds at terminal states.
set_option linter.unusedVariables false in
/-- **the asymptotic guarantee, on the nose.**  If the estimates converge to `Q*` at
every non-terminal enabled pair, then the value of the **induced greedy policy**
converges to the optimal value at the initial state: `V^{π_t}(s₀) → V*(s₀)`.

The conclusion proved is in fact stronger than the standard: by
`greedy_eventually_optimal` the sequence is *eventually equal* to `V*(s₀)`, not
merely convergent to it — even though the induced policies `π_t` themselves may
never stabilise, oscillating among tied optimal actions forever. -/
theorem tendsto_Vpi_greedy (hw : HittingWeight M) {Q : ℕ → S → A → ℝ}
    (h : ∀ s a, M.isTerm s = false → a ∈ M.enabled s →
      Filter.Tendsto (fun t => Q t s a) Filter.atTop (nhds (M.Qstar s a)))
    (hinit : M.isTerm M.init = false) :
    Filter.Tendsto (fun t => Vpi M (greedyOf M (Q t)) M.init) Filter.atTop
      (nhds (M.Vstar M.init)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [M.greedy_eventually_optimal hw h] with t ht
  exact (M.Vpi_eq_Vstar hw (M.greedyOf_mem (Q t)) (fun s hs => ht s hs) M.init).symm

end MDP

end Arlib

