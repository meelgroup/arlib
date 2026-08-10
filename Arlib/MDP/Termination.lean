/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Almost-sure termination: no end component gives a finite hitting time

    **Almost-sure termination.**  Under the no-end-component assumption, for
    every policy `π` and initial state `s` the hitting time satisfies `T < ∞`
    almost surely; moreover `1 ≤ T_s ≤ |Sₙₜ|/p < ∞` for some `p > 0`.

This file discharges the `HittingWeight` interface of `Arlib.MDP.HittingWeight`
from the no-EC assumption, which is the *only* place the no-end-component assumption is
used in the whole development.  Two stages, mirroring the appendix proof:

1. **Graph stage** (`exists_escapeBound_of_noEC`).  No-EC forces a uniform
   escape probability: there are `n` and `p > 0` such that from every
   non-terminal state, *no* policy can avoid `S_term` for `n` steps with
   probability more than `1 − p`.  This is the appendix's "the induced Markov
   chain is confined to `Sₙₜ`, hence contains a closed recurrent class `D`,
   whose pairs `{(x, π(x)) : x ∈ D}` form an end component" — plus the
   pigeonhole bound on the path length.

2. **Analysis stage** (`exists_hittingWeight_of_escapeBound`).  The geometric
   tail `P^π{T ≥ k·n} ≤ (1−p)^k` bounds the value iteration of the
   *maximal-expected-time* operator uniformly by `n/p`; the iteration is
   monotone, so it converges, and its limit `T` satisfies exactly the three
   fields of `HittingWeight`.
-/
import Arlib.MDP.EndComponent
import Arlib.MDP.HittingWeight

namespace Arlib

open scoped BigOperators
open Finset
open Arlib.Combinatorics

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

-- `maxOver_lt`, the strict companion of `maxOver_le` that the `Good`-set
-- argument below runs on, lives in `Arlib.Combinatorics.FoldMax`.

namespace MDP

variable (M : MDP S A)

/-- **The `k`-step survival value**: the largest probability, over all policies,
of staying inside `Sₙₜ` for `k` more steps starting from `s`.  Defined by the
obvious dynamic program, so that no trajectory space is needed. -/
noncomputable def surviveVal (M : MDP S A) : ℕ → S → ℝ
  | 0, s => if M.isTerm s = true then 0 else 1
  | (k + 1), s =>
      if M.isTerm s = true then 0
      else (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * surviveVal M k s'

/-! ### Elementary properties of `surviveVal` -/

/-- `surviveVal` vanishes on terminal states: the process has already left
`Sₙₜ`. -/
theorem surviveVal_term (k : ℕ) {s : S} (hs : M.isTerm s = true) :
    M.surviveVal k s = 0 := by
  cases k <;> simp [surviveVal, hs]

theorem surviveVal_nonneg (k : ℕ) (s : S) : 0 ≤ M.surviveVal k s := by
  induction k generalizing s with
  | zero => rw [surviveVal]; split <;> norm_num
  | succ k ih =>
      rw [surviveVal]
      split
      · exact le_rfl
      · obtain ⟨a₀, ha₀⟩ := M.enabled_nonempty s
        refine le_trans ?_
          (Finset.le_sup' (f := fun a => ∑ s', M.P s a s' * M.surviveVal k s') ha₀)
        exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg _ _ _) (ih s')

theorem surviveVal_le_one (k : ℕ) (s : S) : M.surviveVal k s ≤ 1 := by
  induction k generalizing s with
  | zero => rw [surviveVal]; split <;> norm_num
  | succ k ih =>
      rw [surviveVal]
      split
      · norm_num
      · refine Finset.sup'_le _ _ fun a _ => ?_
        calc ∑ s', M.P s a s' * M.surviveVal k s'
            ≤ ∑ s', M.P s a s' * 1 :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg _ _ _)
          _ = 1 := by simpa using M.P_sum_one s a

/-- The dynamic-programming inequality defining `surviveVal`: at a non-terminal
state every enabled action is dominated by the `sup'`. -/
theorem sum_P_mul_surviveVal_le (k : ℕ) {s : S} (hs : M.isTerm s = false) {a : A}
    (ha : a ∈ M.enabled s) :
    (∑ s', M.P s a s' * M.surviveVal k s') ≤ M.surviveVal (k + 1) s := by
  rw [surviveVal, if_neg (by simp [hs])]
  exact Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.surviveVal k s') ha

theorem surviveVal_succ (k : ℕ) (s : S) :
    M.surviveVal (k + 1) s =
      if M.isTerm s = true then 0
      else (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * M.surviveVal k s' := rfl

/-- The survival value is antitone in the horizon. -/
theorem surviveVal_succ_le : ∀ (k : ℕ) (s : S),
    M.surviveVal (k + 1) s ≤ M.surviveVal k s := by
  intro k
  induction k with
  | zero =>
      intro s
      by_cases hs : M.isTerm s = true
      · rw [M.surviveVal_term _ hs, M.surviveVal_term _ hs]
      · have h0 : M.surviveVal 0 s = 1 := by rw [surviveVal, if_neg hs]
        rw [h0]; exact M.surviveVal_le_one 1 s
  | succ k ih =>
      intro s
      rw [surviveVal_succ, surviveVal_succ]
      split_ifs with hs
      · exact le_rfl
      · refine Finset.sup'_le _ _ fun a ha => ?_
        refine le_trans (Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s a s')) ?_
        exact Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.surviveVal k s') ha

/-! ### The "certainly-surviving" sets `Good k`

`Good M k` collects the states from which some policy survives `k` steps with
probability exactly `1`.  Its recursion is purely combinatorial, and an escape
bound is exactly the statement that `Good M n` is empty for some `n`. -/

/-- The states surviving `k` steps with probability `1`. -/
noncomputable def Good (M : MDP S A) (k : ℕ) : Finset S :=
  @Finset.filter S (fun s => M.surviveVal k s = 1) (Classical.decPred _) Finset.univ

theorem mem_Good {k : ℕ} {s : S} : s ∈ M.Good k ↔ M.surviveVal k s = 1 := by
  simp [Good]

theorem Good_isTerm {k : ℕ} {s : S} (hs : s ∈ M.Good k) : M.isTerm s = false := by
  by_contra hc
  have hT : M.isTerm s = true := by simpa using hc
  have h1 := M.mem_Good.1 hs
  rw [M.surviveVal_term k hT] at h1
  norm_num at h1

theorem Good_antitone (k : ℕ) : M.Good (k + 1) ⊆ M.Good k := by
  intro s hs
  have h1 := M.mem_Good.1 hs
  have h2 := M.surviveVal_succ_le k s
  have h3 := M.surviveVal_le_one k s
  exact M.mem_Good.2 (le_antisymm h3 (by linarith))

/-- **The recursion for `Good`.**  A state that survives `k+1` steps surely is
non-terminal and has an enabled action all of whose positive-probability
successors again survive `k` steps surely. -/
theorem Good_succ_spec {k : ℕ} {s : S} (hs : s ∈ M.Good (k + 1)) :
    ∃ a ∈ M.enabled s, ∀ s', 0 < M.P s a s' → s' ∈ M.Good k := by
  have hnt : M.isTerm s = false := M.Good_isTerm hs
  have h1 : M.surviveVal (k + 1) s = 1 := M.mem_Good.1 hs
  rw [surviveVal_succ, if_neg (by simp [hnt])] at h1
  obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.enabled_nonempty s)
    (fun a => ∑ s', M.P s a s' * M.surviveVal k s')
  refine ⟨a, ha, ?_⟩
  have hsum : (∑ s', M.P s a s' * M.surviveVal k s') = 1 := by rw [← hae]; exact h1
  have h2 : (∑ s', M.P s a s' * (1 - M.surviveVal k s')) = 0 := by
    have hP := M.P_sum_one s a
    calc (∑ s', M.P s a s' * (1 - M.surviveVal k s'))
        = (∑ s', M.P s a s') - ∑ s', M.P s a s' * M.surviveVal k s' := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro s' _; ring
      _ = 0 := by rw [hP, hsum]; ring
  have h3 : ∀ s' ∈ (Finset.univ : Finset S), M.P s a s' * (1 - M.surviveVal k s') = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 h2
    intro s' _
    exact mul_nonneg (M.P_nonneg _ _ _) (by linarith [M.surviveVal_le_one k s'])
  intro s' hps'
  have h4 := h3 s' (Finset.mem_univ s')
  have h5 : 1 - M.surviveVal k s' = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (ne_of_gt hps')
    · exact h
  exact M.mem_Good.2 (by linarith)

/-! ### Reachability under a deterministic policy -/

/-- `ReachPi M π x y`: `y` is reachable from `x` by positive-probability steps
of the deterministic policy `π`. -/
inductive ReachPi (π : S → A) : S → S → Prop
  | refl (s : S) : ReachPi π s s
  | step {s s' t : S} : 0 < M.P s (π s) s' → ReachPi π s' t → ReachPi π s t

theorem ReachPi.trans' {M : MDP S A} {π : S → A} {x y z : S}
    (h₁ : M.ReachPi π x y) (h₂ : M.ReachPi π y z) : M.ReachPi π x z := by
  induction h₁ with
  | refl _ => exact h₂
  | step hp _ ih => exact ReachPi.step hp (ih h₂)

/-- The `π`-reachable set of `x`, as a `Finset`. -/
noncomputable def reachSet (M : MDP S A) (π : S → A) (x : S) : Finset S :=
  @Finset.filter S (fun y => M.ReachPi π x y) (Classical.decPred _) Finset.univ

theorem mem_reachSet {π : S → A} {x y : S} :
    y ∈ M.reachSet π x ↔ M.ReachPi π x y := by
  simp [reachSet]

/-- **A closed, non-terminal, policy-invariant set contradicts `NoEC`.**  This
is the graph half of the almost-sure termination property: minimise the reachable set inside `D`
to obtain a strongly connected closed sub-class, whose graph under `π` is an end
component made of non-terminal states. -/
theorem noEC_absurd (h : M.NoEC) (π : S → A) (hπ : ∀ s, π s ∈ M.enabled s)
    (D : Finset S) (hDne : D.Nonempty) (hDnt : ∀ s ∈ D, M.isTerm s = false)
    (hDcl : ∀ s ∈ D, ∀ s', 0 < M.P s (π s) s' → s' ∈ D) : False := by
  classical
  -- `D` is invariant under `π`-reachability.
  have hRD : ∀ (x y : S), M.ReachPi π x y → x ∈ D → y ∈ D := by
    intro x y hxy
    induction hxy with
    | refl _ => exact id
    | step hp _ ih => exact fun hx => ih (hDcl _ hx _ hp)
  -- Pick a state of `D` with a reachable set of minimal cardinality.
  obtain ⟨x, hxD, hxmin⟩ :=
    Finset.exists_min_image D (fun z => (M.reachSet π z).card) hDne
  have hxx : x ∈ M.reachSet π x := M.mem_reachSet.2 (ReachPi.refl x)
  have hsub : ∀ y ∈ M.reachSet π x, M.reachSet π y ⊆ M.reachSet π x := by
    intro y hy z hz
    exact M.mem_reachSet.2 ((M.mem_reachSet.1 hy).trans' (M.mem_reachSet.1 hz))
  have hxDsub : ∀ y ∈ M.reachSet π x, y ∈ D := fun y hy => hRD x y (M.mem_reachSet.1 hy) hxD
  have hEq : ∀ y ∈ M.reachSet π x, M.reachSet π y = M.reachSet π x := by
    intro y hy
    exact Finset.eq_of_subset_of_card_le (hsub y hy) (hxmin y (hxDsub y hy))
  -- The graph of `π` over the minimal reachable set is an end component.
  set C : Finset (S × A) := (M.reachSet π x).image (fun y => (y, π y)) with hC
  have hmemC : ∀ y ∈ M.reachSet π x, (y, π y) ∈ C := by
    intro y hy; exact Finset.mem_image.2 ⟨y, hy, rfl⟩
  have hCmem : ∀ p ∈ C, p.1 ∈ M.reachSet π x ∧ p.2 = π p.1 := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨hy, rfl⟩
  -- reachability inside `C` follows the `π`-steps
  have hconv : ∀ (y z : S), M.ReachPi π y z → y ∈ M.reachSet π x → M.ReachIn C y z := by
    intro y z hyz
    induction hyz with
    | refl s => exact fun _ => MDP.ReachIn.refl s
    | step hp _ ih =>
        intro hy
        refine MDP.ReachIn.step (hmemC _ hy) hp (ih ?_)
        exact M.mem_reachSet.2
          ((M.mem_reachSet.1 hy).trans' (ReachPi.step hp (ReachPi.refl _)))
  have hEC : M.IsEC C := by
    refine ⟨⟨(x, π x), hmemC x hxx⟩, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨_, h2⟩ := hCmem p hp
      rw [h2]; exact hπ p.1
    · intro p hp s' hs'
      obtain ⟨h1, h2⟩ := hCmem p hp
      rw [h2] at hs'
      have : s' ∈ M.reachSet π x :=
        M.mem_reachSet.2 ((M.mem_reachSet.1 h1).trans'
          (ReachPi.step hs' (ReachPi.refl _)))
      exact ⟨π s', hmemC s' this⟩
    · intro p hp q hq
      obtain ⟨h1, _⟩ := hCmem p hp
      obtain ⟨h2, _⟩ := hCmem q hq
      refine hconv p.1 q.1 ?_ h1
      have := hEq p.1 h1
      exact M.mem_reachSet.1 (by rw [this]; exact h2)
  -- but `x` is non-terminal, contradicting `NoEC`.
  have := h C hEC (x, π x) (hmemC x hxx)
  simp only at this
  rw [hDnt x hxD] at this
  exact Bool.false_ne_true this

/-- **A uniform escape bound.**  After `n` steps, every policy has failed to
keep the process inside `Sₙₜ` with probability at least `p > 0`, from every
non-terminal start. -/
structure EscapeBound (M : MDP S A) where
  /-- The horizon (the appendix takes `|Sₙₜ|`). -/
  n : ℕ
  /-- The escape probability. -/
  p : ℝ
  p_pos : 0 < p
  p_le_one : p ≤ 1
  /-- `max_π P^π(survive `n` steps ∣ s) ≤ 1 − p` for non-terminal `s`. -/
  escape : ∀ s, M.isTerm s = false → M.surviveVal n s ≤ 1 - p

namespace EscapeBound

variable {M} (e : EscapeBound M)

theorem one_sub_p_nonneg : (0:ℝ) ≤ 1 - e.p := by have := e.p_le_one; linarith

/-- **Composition.**  Surviving `n` extra steps costs a factor `1 − p`,
uniformly in the remaining horizon: `q_{n+k}(s) ≤ (1−p)·q_k(s)`.  This is the
only place `escape` is used. -/
theorem surviveVal_add_le : ∀ (k : ℕ) (s : S),
    M.surviveVal (e.n + k) s ≤ (1 - e.p) * M.surviveVal k s := by
  intro k
  induction k with
  | zero =>
      intro s
      by_cases hs : M.isTerm s = true
      · rw [M.surviveVal_term _ hs, M.surviveVal_term _ hs]; norm_num
      · have hs' : M.isTerm s = false := by simpa using hs
        have h0 : M.surviveVal 0 s = 1 := by rw [surviveVal, if_neg hs]
        simpa [h0] using e.escape s hs'
  | succ k ih =>
      intro s
      have harr : e.n + (k + 1) = (e.n + k) + 1 := by omega
      rw [harr, surviveVal, surviveVal]
      split_ifs with hs
      · norm_num
      · refine Finset.sup'_le _ _ fun a _ => ?_
        have h₁ : (∑ s', M.P s a s' * M.surviveVal (e.n + k) s')
            ≤ ∑ s', (1 - e.p) * (M.P s a s' * M.surviveVal k s') := by
          refine Finset.sum_le_sum fun s' _ => ?_
          have := mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s a s')
          calc M.P s a s' * M.surviveVal (e.n + k) s'
              ≤ M.P s a s' * ((1 - e.p) * M.surviveVal k s') := this
            _ = (1 - e.p) * (M.P s a s' * M.surviveVal k s') := by ring
        refine h₁.trans ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ e.one_sub_p_nonneg
        exact Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.surviveVal k s') ‹a ∈ _›

/-- **The uniform bound `∑_{j<k} q_j(s) ≤ n/p`.**  Comparing `∑_{j<n+k}` with
`∑_{j<k}` two ways: it is at least the latter (all terms are non-negative) and
at most `n + (1−p)·∑_{j<k}` (the first `n` terms are `≤ 1`, the rest compose). -/
theorem sum_surviveVal_le (k : ℕ) (s : S) :
    (∑ j ∈ Finset.range k, M.surviveVal j s) ≤ (e.n : ℝ) / e.p := by
  set F := ∑ j ∈ Finset.range k, M.surviveVal j s with hF
  have h1 : F ≤ ∑ j ∈ Finset.range (e.n + k), M.surviveVal j s := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.2 (Nat.le_add_left _ _)) fun i _ _ => M.surviveVal_nonneg i s
  have h2 : (∑ j ∈ Finset.range (e.n + k), M.surviveVal j s)
      = (∑ j ∈ Finset.range e.n, M.surviveVal j s)
        + ∑ j ∈ Finset.range k, M.surviveVal (e.n + j) s :=
    Finset.sum_range_add _ _ _
  have h3 : (∑ j ∈ Finset.range e.n, M.surviveVal j s) ≤ (e.n : ℝ) := by
    calc (∑ j ∈ Finset.range e.n, M.surviveVal j s)
        ≤ ∑ _j ∈ Finset.range e.n, (1:ℝ) :=
          Finset.sum_le_sum fun j _ => M.surviveVal_le_one j s
      _ = (e.n : ℝ) := by simp
  have h4 : (∑ j ∈ Finset.range k, M.surviveVal (e.n + j) s) ≤ (1 - e.p) * F := by
    rw [hF, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => e.surviveVal_add_le j s
  rw [le_div_iff₀ e.p_pos]
  nlinarith [h1, h3, h4]

end EscapeBound

/-! ### Value iteration of the maximal-expected-time operator -/

/-- **`timeVal M k s`** — the largest, over all policies, expected number of
steps spent inside `Sₙₜ` during the next `k` steps starting from `s`.  This is
the `k`-th iterate of the maximal-expected-time operator applied to `0`. -/
noncomputable def timeVal (M : MDP S A) : ℕ → S → ℝ
  | 0, _ => 0
  | (k + 1), s =>
      if M.isTerm s = true then 0
      else 1 + (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * timeVal M k s'

theorem timeVal_succ (k : ℕ) (s : S) :
    M.timeVal (k + 1) s =
      if M.isTerm s = true then 0
      else 1 + (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * M.timeVal k s' := rfl

theorem timeVal_term (k : ℕ) {s : S} (hs : M.isTerm s = true) : M.timeVal k s = 0 := by
  cases k <;> simp [timeVal, hs]

theorem timeVal_nonneg (k : ℕ) (s : S) : 0 ≤ M.timeVal k s := by
  induction k generalizing s with
  | zero => simp [timeVal]
  | succ k ih =>
      rw [timeVal_succ]
      split
      · exact le_rfl
      · obtain ⟨a₀, ha₀⟩ := M.enabled_nonempty s
        have h1 : (0:ℝ) ≤ ∑ s', M.P s a₀ s' * M.timeVal k s' :=
          Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg _ _ _) (ih s')
        have h2 := Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.timeVal k s') ha₀
        linarith

/-- The iteration is monotone in the horizon. -/
theorem timeVal_le_succ : ∀ (k : ℕ) (s : S), M.timeVal k s ≤ M.timeVal (k + 1) s := by
  intro k
  induction k with
  | zero => intro s; simpa [timeVal] using M.timeVal_nonneg 1 s
  | succ k ih =>
      intro s
      rw [timeVal_succ, timeVal_succ]
      split_ifs with hs
      · exact le_rfl
      · refine add_le_add_left ?_ 1
        refine Finset.sup'_le _ _ fun a ha => ?_
        refine le_trans (Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg s a s')) ?_
        exact Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.timeVal (k + 1) s') ha

theorem timeVal_monotone (s : S) : Monotone fun k => M.timeVal k s :=
  monotone_nat_of_le_succ fun k => M.timeVal_le_succ k s

/-- **The comparison with the survival values**: the expected time spent in
`Sₙₜ` over `k` steps is the sum of the survival probabilities. -/
theorem timeVal_le_sum_surviveVal : ∀ (k : ℕ) (s : S),
    M.timeVal k s ≤ ∑ j ∈ Finset.range k, M.surviveVal j s := by
  intro k
  induction k with
  | zero => intro s; simp [timeVal]
  | succ k ih =>
      intro s
      rw [timeVal_succ]
      split_ifs with hs
      · exact Finset.sum_nonneg fun j _ => M.surviveVal_nonneg j s
      · have hs' : M.isTerm s = false := by simpa using hs
        have hq0 : M.surviveVal 0 s = 1 := by rw [surviveVal, if_neg hs]
        have key : ((M.enabled s).sup' (M.enabled_nonempty s)
            fun a => ∑ s', M.P s a s' * M.timeVal k s')
            ≤ ∑ j ∈ Finset.range k, M.surviveVal (j + 1) s := by
          refine Finset.sup'_le _ _ fun a ha => ?_
          calc (∑ s', M.P s a s' * M.timeVal k s')
              ≤ ∑ s', M.P s a s' * (∑ j ∈ Finset.range k, M.surviveVal j s') :=
                Finset.sum_le_sum fun s' _ =>
                  mul_le_mul_of_nonneg_left (ih s') (M.P_nonneg _ _ _)
            _ = ∑ j ∈ Finset.range k, ∑ s', M.P s a s' * M.surviveVal j s' := by
                simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
            _ ≤ ∑ j ∈ Finset.range k, M.surviveVal (j + 1) s :=
                Finset.sum_le_sum fun j _ => M.sum_P_mul_surviveVal_le j hs' ha
        rw [Finset.sum_range_succ', hq0]
        linarith

theorem timeVal_le_bound (e : EscapeBound M) (k : ℕ) (s : S) :
    M.timeVal k s ≤ (e.n : ℝ) / e.p :=
  (M.timeVal_le_sum_surviveVal k s).trans (e.sum_surviveVal_le k s)

theorem bddAbove_timeVal (e : EscapeBound M) (s : S) :
    BddAbove (Set.range fun k => M.timeVal k s) := by
  refine ⟨(e.n : ℝ) / e.p, ?_⟩
  rintro x ⟨k, rfl⟩
  exact M.timeVal_le_bound e k s

/-- **`T_s`** — the limit of the monotone, bounded value iteration; the
worst-case expected hitting time of `S_term`. -/
noncomputable def timeSup (M : MDP S A) (s : S) : ℝ := ⨆ k, M.timeVal k s

theorem timeVal_le_timeSup (e : EscapeBound M) (k : ℕ) (s : S) :
    M.timeVal k s ≤ M.timeSup s :=
  le_ciSup (M.bddAbove_timeVal e s) k

theorem tendsto_timeVal (e : EscapeBound M) (s : S) :
    Filter.Tendsto (fun k => M.timeVal k s) Filter.atTop (nhds (M.timeSup s)) :=
  tendsto_atTop_ciSup (M.timeVal_monotone s) (M.bddAbove_timeVal e s)


/-- **Stage 1 — the graph argument.**  The no-EC assumption yields a uniform
escape bound.  (the almost-sure termination property, first two paragraphs of the appendix
proof.) -/
theorem exists_escapeBound_of_noEC {M : MDP S A} (h : M.NoEC) :
    Nonempty (MDP.EscapeBound M) := by
  classical
  -- The antitone chain `Good 0 ⊇ Good 1 ⊇ …` of finite sets must stabilise.
  have hstab : ∃ j, M.Good j = M.Good (j + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ j, (M.Good (j + 1)).card < (M.Good j).card := fun j =>
      Finset.card_lt_card (lt_of_le_of_ne (M.Good_antitone j) fun heq => hcon j heq.symm)
    have hbd : ∀ j, (M.Good j).card + j ≤ (M.Good 0).card := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => have := hlt j; omega
    have := hbd ((M.Good 0).card + 1)
    omega
  obtain ⟨j, hj⟩ := hstab
  -- A stable stage is empty: otherwise it carries an end component of
  -- non-terminal states, contradicting `NoEC`.
  have hempty : M.Good j = ∅ := by
    by_contra hne
    obtain ⟨s₀, hs₀⟩ := Finset.nonempty_of_ne_empty hne
    have hact : ∀ s : S, ∃ a, a ∈ M.enabled s ∧
        (s ∈ M.Good j → ∀ s', 0 < M.P s a s' → s' ∈ M.Good j) := by
      intro s
      by_cases hs : s ∈ M.Good j
      · rw [hj] at hs
        obtain ⟨a, ha, hcl⟩ := M.Good_succ_spec hs
        exact ⟨a, ha, fun _ => hcl⟩
      · obtain ⟨a, ha⟩ := M.enabled_nonempty s
        exact ⟨a, ha, fun hc => absurd hc hs⟩
    choose π hπ hπcl using hact
    exact M.noEC_absurd h π hπ (M.Good j) ⟨s₀, hs₀⟩
      (fun s hs => M.Good_isTerm hs) (fun s hs => hπcl s hs)
  -- Hence every state survives `j` steps with probability `< 1`.
  have hlt1 : ∀ s, M.surviveVal j s < 1 := by
    intro s
    have hns : s ∉ M.Good j := by rw [hempty]; exact Finset.not_mem_empty s
    exact lt_of_le_of_ne (M.surviveVal_le_one j s) fun hc => hns (M.mem_Good.2 hc)
  have hmax : maxOver M.nontermSet 0 (M.surviveVal j) < 1 :=
    maxOver_lt one_pos fun s _ => hlt1 s
  have hmax0 : (0:ℝ) ≤ maxOver M.nontermSet 0 (M.surviveVal j) := base_le_maxOver _ _ _
  refine ⟨{ n := j
            p := 1 - maxOver M.nontermSet 0 (M.surviveVal j)
            p_pos := by linarith
            p_le_one := by linarith
            escape := ?_ }⟩
  intro s hs
  have := le_maxOver_of_mem (b := (0:ℝ)) (f := M.surviveVal j) ((M.mem_nontermSet).2 hs)
  linarith

/-- **Stage 2 — the analysis argument.**  A uniform escape bound yields a
hitting-time weight, i.e. a finite `T` obeying `T_s = 0` on terminals,
`1 ≤ T_s` off them, and the one-step inequality the hitting-time Bellman inequality. -/
theorem exists_hittingWeight_of_escapeBound {M : MDP S A} (e : MDP.EscapeBound M) :
    Nonempty (HittingWeight M) := by
  refine ⟨⟨M.timeSup, ?_, ?_, ?_⟩⟩
  · -- `T_s = 0` on terminal states: every iterate is `0` there.
    intro s hs
    have h : (fun k => M.timeVal k s) = fun _ : ℕ => (0:ℝ) :=
      funext fun k => M.timeVal_term k hs
    rw [MDP.timeSup, h, ciSup_const]
  · -- `1 ≤ T_s` off the terminal states: already `timeVal 1 s = 1`.
    intro s hs
    have h1 : M.timeVal 1 s = 1 := by
      rw [MDP.timeVal_succ, if_neg (by simp [hs])]
      simp [MDP.timeVal]
    calc (1:ℝ) = M.timeVal 1 s := h1.symm
      _ ≤ M.timeSup s := M.timeVal_le_timeSup e 1 s
  · -- the one-step inequality, obtained in the limit.
    intro s a hs ha
    have htend : Filter.Tendsto
        (fun k => (∑ s', M.P s a s' * M.timeVal k s') + 1) Filter.atTop
        (nhds ((∑ s', M.P s a s' * M.timeSup s') + 1)) := by
      refine Filter.Tendsto.add_const 1 ?_
      exact tendsto_finset_sum _ fun s' _ => (M.tendsto_timeVal e s').const_mul _
    refine le_of_tendsto htend ?_
    filter_upwards with k
    have hstep : (∑ s', M.P s a s' * M.timeVal k s') + 1 ≤ M.timeVal (k + 1) s := by
      rw [MDP.timeVal_succ, if_neg (by simp [hs])]
      have := Finset.le_sup' (fun a => ∑ s', M.P s a s' * M.timeVal k s') ha
      linarith
    exact hstep.trans (M.timeVal_le_timeSup e (k + 1) s)

/-- **the almost-sure termination property.**  Under the no-end-component assumption the hitting-time weight
`T` exists — the single hypothesis every later result depends on. -/
theorem exists_hittingWeight_of_noEC {M : MDP S A} (h : M.NoEC) :
    Nonempty (HittingWeight M) :=
  let ⟨e⟩ := exists_escapeBound_of_noEC h
  exists_hittingWeight_of_escapeBound e

end MDP
end Arlib
