/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Trajectories, policies, and the probabilistic meaning of `reachVal`

`Arlib/MDP/Reachability.lean` **defines** `reachVal` by backward induction and
its docstring asserts that it is "the largest probability, over all policies, of
reaching a target state within `k` steps".  This file turns that assertion into
a theorem: it builds the trajectory distribution `P^π` as an honest product of
kernel entries over finite paths, defines

    reachProbSem M π k s = P^π(τ ⊨ S_T within k steps ∣ s₀ = s)

— literally the optimal reachability value at a finite horizon — and proves

* `reachProbSem_le_reachVal` (soundness: no policy beats the dynamic program),
* `exists_policy_reachProbSem_eq` (attainment: some valid policy meets it),
* `isGreatest_reachProbSem` / `reachVal_eq_iSup_reachProbSem` (the headline: the
  dynamic program *is* the maximum, over valid policies, of a real probability),
* `Vstar_isLUB_reachProbSem` / `Vstar_eq_iSup_reachProbSem` (the payoff: `V*` is
  the supremum over horizons and policies of a real probability).

Everything is finite-horizon, so no measure theory is needed: `P^π` on paths of
length `k` is a finite product measure on `Fin k → S`, and every "probability"
below is a finite sum over a `Fintype`.
-/
import Arlib.MDP.Reachability

namespace Arlib

open scoped BigOperators Topology
open Finset Filter

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A)

/-! ## Policies -/

/-- **A deterministic, time-dependent policy** `π t s`: the action taken at time
`t` in state `s`.

The standard `π : S → A` is the *stationary* special case `fun _ s => π s`.  We
allow time dependence because that is the natural class for a finite horizon —
and it only makes the soundness half of the main theorem *stronger*: even
time-dependent policies cannot beat `reachVal`.  (Randomised policies are not
needed either: `isGreatest_reachProbSem` shows the maximum is already attained
by a deterministic one, and a randomised policy is a convex combination of
deterministic ones.) -/
abbrev Policy (_M : MDP S A) : Type _ := ℕ → S → A

/-- Validity of a policy: it only ever picks *enabled* actions, `π(s) ∈ A(s)`. -/
def IsPolicy (M : MDP S A) (π : ℕ → S → A) : Prop := ∀ t s, π t s ∈ M.enabled s

/-- The standard stationary policy `π : S → A`, read as a time-dependent one. -/
def stationary (π : S → A) : ℕ → S → A := fun _ => π

theorem isPolicy_stationary {π : S → A} (h : ∀ s, π s ∈ M.enabled s) :
    M.IsPolicy (MDP.stationary π) := fun _ s => h s

/-- The policy `π` seen from time `1` onwards — the residual policy after the
first step. -/
def shift (π : ℕ → S → A) : ℕ → S → A := fun t => π (t + 1)

theorem IsPolicy.shift {π : ℕ → S → A} (h : M.IsPolicy π) : M.IsPolicy (MDP.shift π) :=
  fun t s => h (t + 1) s

/-! ## The trajectory distribution `P^π` on finite paths -/

/-- **`pathProb M π s k ω`** — the probability, under `P^π` started at `s`, of
the concrete length-`k` continuation `ω : Fin k → S`, i.e. of the trajectory
prefix `(s, ω 0, ω 1, …, ω (k-1))`.

This is the standard `P^π((s₀,…,s_t)) = ∏_k P(s_{k+1} ∣ s_k, π(s_k))`: an actual
product of kernel entries (see `pathProb_eq_prod`), *not* a dynamic program. -/
noncomputable def pathProb (M : MDP S A) :
    (π : ℕ → S → A) → (s : S) → (k : ℕ) → (Fin k → S) → ℝ
  | _, _, 0, _ => 1
  | π, s, (k + 1), ω =>
      M.P s (π 0 s) (ω 0) * M.pathProb (MDP.shift π) (ω 0) k (Fin.tail ω)

@[simp] theorem pathProb_zero (π : ℕ → S → A) (s : S) (ω : Fin 0 → S) :
    M.pathProb π s 0 ω = 1 := rfl

theorem pathProb_succ (π : ℕ → S → A) (s : S) (k : ℕ) (ω : Fin (k + 1) → S) :
    M.pathProb π s (k + 1) ω =
      M.P s (π 0 s) (ω 0) * M.pathProb (MDP.shift π) (ω 0) k (Fin.tail ω) := rfl

@[simp] theorem pathProb_cons (π : ℕ → S → A) (s s' : S) (k : ℕ) (ω : Fin k → S) :
    M.pathProb π s (k + 1) (Fin.cons s' ω) =
      M.P s (π 0 s) s' * M.pathProb (MDP.shift π) s' k ω := by
  rw [M.pathProb_succ]
  simp

theorem pathProb_nonneg (π : ℕ → S → A) (s : S) (k : ℕ) (ω : Fin k → S) :
    0 ≤ M.pathProb π s k ω := by
  induction k generalizing π s with
  | zero => simp
  | succ k ih =>
      rw [M.pathProb_succ]
      exact mul_nonneg (M.P_nonneg _ _ _) (ih _ _ _)

omit [DecidableEq S] in
/-- Splitting a length-`(k+1)` tuple into its head and tail: the reindexing every
"condition on the first transition" argument below runs on. -/
theorem sum_pi_fin_succ {k : ℕ} (f : (Fin (k + 1) → S) → ℝ) :
    ∑ ω : Fin (k + 1) → S, f ω = ∑ s' : S, ∑ ω' : Fin k → S, f (Fin.cons s' ω') := by
  have h : ∑ p : S × (Fin k → S), f (Fin.cons p.1 p.2) = ∑ ω : Fin (k + 1) → S, f ω :=
    Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (k + 1) => S) _ _ fun _ => rfl
  rw [← h, Fintype.sum_prod_type]

/-- **`P^π` is a probability distribution on length-`k` paths.** -/
theorem pathProb_sum_one (π : ℕ → S → A) (s : S) (k : ℕ) :
    ∑ ω : Fin k → S, M.pathProb π s k ω = 1 := by
  induction k generalizing π s with
  | zero => simp
  | succ k ih =>
      rw [sum_pi_fin_succ (fun ω => M.pathProb π s (k + 1) ω)]
      calc ∑ s' : S, ∑ ω' : Fin k → S, M.pathProb π s (k + 1) (Fin.cons s' ω')
          = ∑ s' : S, M.P s (π 0 s) s' := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            simp only [M.pathProb_cons, ← Finset.mul_sum, ih]
            rw [mul_one]
        _ = 1 := M.P_sum_one _ _

theorem pathProb_le_one (π : ℕ → S → A) (s : S) (k : ℕ) (ω : Fin k → S) :
    M.pathProb π s k ω ≤ 1 := by
  refine le_trans ?_ (le_of_eq (M.pathProb_sum_one π s k))
  exact Finset.single_le_sum (f := fun ω => M.pathProb π s k ω)
    (fun ω _ => M.pathProb_nonneg π s k ω) (Finset.mem_univ ω)

/-- `pathProb` is literally the standard product `∏_{i<k} P(s_{i+1} ∣ s_i, π_i(s_i))`,
where `Fin.cons s ω` is the full trajectory `(s, ω 0, …, ω (k-1))` and
`i.castSucc` picks out the `i`-th state of it. -/
theorem pathProb_eq_prod (π : ℕ → S → A) (s : S) (k : ℕ) (ω : Fin k → S) :
    M.pathProb π s k ω =
      ∏ i : Fin k, M.P ((Fin.cons s ω : Fin (k + 1) → S) i.castSucc)
        (π i ((Fin.cons s ω : Fin (k + 1) → S) i.castSucc)) (ω i) := by
  induction k generalizing π s with
  | zero => simp
  | succ k ih =>
      rw [M.pathProb_succ, ih, Fin.cons_self_tail, Fin.prod_univ_succ]
      refine congrArg₂ _ (by simp) (Finset.prod_congr rfl fun x _ => ?_)
      rw [← Fin.succ_castSucc]
      simp [MDP.shift, Fin.tail]

/-! ## Absorption at terminal states -/

/-- Terminal states are absorbing, so the walk leaves them with probability `0`. -/
theorem P_eq_zero_of_isTerm {s : S} (a : A) (h : M.isTerm s = true) {s' : S} (hne : s' ≠ s) :
    M.P s a s' = 0 := by
  have hsum : ∑ x : S, M.P s a x = 1 := M.P_sum_one s a
  have habs : M.P s a s = 1 := M.absorbing s a h
  have hsplit : M.P s a s + ∑ x ∈ univ.erase s, M.P s a x = ∑ x : S, M.P s a x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ s)
  rw [habs, hsum] at hsplit
  have hzero : ∑ x ∈ univ.erase s, M.P s a x = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => M.P_nonneg s a x).1 hzero s'
    (Finset.mem_erase.2 ⟨hne, Finset.mem_univ s'⟩)

/-- The one-step expectation at a terminal state is the identity: the walk stays
put.  This is what pins the value at `0` on `S_N`. -/
theorem sum_absorbing (a : A) {s : S} (h : M.isTerm s = true) (f : S → ℝ) :
    ∑ s', M.P s a s' * f s' = f s := by
  have habs : M.P s a s = 1 := M.absorbing s a h
  rw [Finset.sum_eq_single s
    (fun b _ hb => by rw [M.P_eq_zero_of_isTerm a h hb, zero_mul])
    (fun hc => absurd (Finset.mem_univ s) hc), habs, one_mul]

/-! ## The reachability event and the semantic value -/

/-- **`τ ⊨ S_T` within `k` steps** — the start state `s` or one of the states
`ω 0, …, ω (k-1)` along the path is a target. -/
def HitsTarget (M : MDP S A) (s : S) {k : ℕ} (ω : Fin k → S) : Prop :=
  M.isTarget s = true ∨ ∃ i, M.isTarget (ω i) = true

instance decidableHitsTarget (s : S) {k : ℕ} (ω : Fin k → S) :
    Decidable (M.HitsTarget s ω) := by
  unfold HitsTarget; infer_instance

theorem hitsTarget_cons (s s' : S) {k : ℕ} (ω : Fin k → S) :
    M.HitsTarget s (Fin.cons s' ω) ↔ (M.isTarget s = true ∨ M.HitsTarget s' ω) := by
  simp only [HitsTarget, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

/-- **`reachProbSem M π k s = P^π(τ ⊨ S_T within k steps ∣ s₀ = s)`** — the
source paper's optimal reachability value at a finite horizon: the
`P^π`-probability of the set of
length-`k` paths from `s` that visit a target state.  Nothing here is a dynamic
program: it is a sum of products of kernel entries over an explicit event. -/
noncomputable def reachProbSem (M : MDP S A) (π : ℕ → S → A) (k : ℕ) (s : S) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → S => M.HitsTarget s ω), M.pathProb π s k ω

theorem reachProbSem_nonneg (π : ℕ → S → A) (k : ℕ) (s : S) :
    0 ≤ M.reachProbSem π k s :=
  Finset.sum_nonneg fun ω _ => M.pathProb_nonneg π s k ω

theorem reachProbSem_le_one (π : ℕ → S → A) (k : ℕ) (s : S) :
    M.reachProbSem π k s ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun ω _ _ => M.pathProb_nonneg π s k ω) ?_
  exact le_of_eq (M.pathProb_sum_one π s k)

/-- At horizon `0` only the start state can be a target. -/
theorem reachProbSem_zero (π : ℕ → S → A) (s : S) :
    M.reachProbSem π 0 s = if M.isTarget s = true then 1 else 0 := by
  by_cases h : M.isTarget s = true
  · have hf : (univ.filter fun ω : Fin 0 → S => M.HitsTarget s ω) = univ := by
      ext ω; simp [HitsTarget, h]
    rw [if_pos h, reachProbSem, hf]
    exact M.pathProb_sum_one π s 0
  · have hf : (univ.filter fun ω : Fin 0 → S => M.HitsTarget s ω) = ∅ := by
      ext ω; simp [HitsTarget, h]
    rw [if_neg h, reachProbSem, hf, Finset.sum_empty]

/-- **The crux: conditioning on the first transition.**  Either `s` is already a
target — and then the event is everything, of probability `1` — or the path must
hit a target from its first successor onwards, and `P^π` factors through the
kernel row `P(· ∣ s, π₀(s))`. -/
theorem reachProbSem_succ (π : ℕ → S → A) (k : ℕ) (s : S) :
    M.reachProbSem π (k + 1) s =
      if M.isTarget s = true then 1
      else ∑ s', M.P s (π 0 s) s' * M.reachProbSem (MDP.shift π) k s' := by
  by_cases h : M.isTarget s = true
  · have hf : (univ.filter fun ω : Fin (k + 1) → S => M.HitsTarget s ω) = univ := by
      ext ω; simp [HitsTarget, h]
    rw [if_pos h, reachProbSem, hf]
    exact M.pathProb_sum_one π s (k + 1)
  · rw [if_neg h, reachProbSem, Finset.sum_filter,
      sum_pi_fin_succ (fun ω : Fin (k + 1) → S =>
        if M.HitsTarget s ω then M.pathProb π s (k + 1) ω else 0)]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [reachProbSem, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    have hiff : M.HitsTarget s (Fin.cons s' ω') ↔ M.HitsTarget s' ω' := by
      rw [M.hitsTarget_cons]; simp [h]
    by_cases hh : M.HitsTarget s' ω'
    · rw [if_pos (hiff.2 hh), if_pos hh, M.pathProb_cons]
    · rw [if_neg fun hc => hh (hiff.1 hc), if_neg hh, mul_zero]

/-- A sanity check on the semantics: at horizon `1` from a non-target state the
probability is exactly the kernel mass the chosen action puts on `S_T`. -/
theorem reachProbSem_one (π : ℕ → S → A) {s : S} (h : M.isTarget s = false) :
    M.reachProbSem π 1 s = ∑ s' ∈ M.targetSet, M.P s (π 0 s) s' := by
  rw [M.reachProbSem_succ, if_neg (by simp [h]), targetSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [M.reachProbSem_zero]
  split <;> simp

/-- On a terminal state the horizon and the policy are both irrelevant: from a
target the event has already happened, and from a non-target terminal the walk
stays put forever, so it never hits a target. -/
theorem reachProbSem_term (π : ℕ → S → A) (k : ℕ) {s : S} (h : M.isTerm s = true) :
    M.reachProbSem π k s = if M.isTarget s = true then 1 else 0 := by
  induction k generalizing π s with
  | zero => exact M.reachProbSem_zero π s
  | succ k ih =>
      rw [M.reachProbSem_succ]
      by_cases htg : M.isTarget s = true
      · rw [if_pos htg, if_pos htg]
      · rw [if_neg htg, if_neg htg, M.sum_absorbing _ h, ih _ h, if_neg htg]

/-- The unrolling in the same three-branch shape as `reachVal_succ`, which is what
makes the two inductions below line up branch for branch.  (The `S_N` branch is
*derived*, not imposed: it is absorption.) -/
theorem reachProbSem_succ' (π : ℕ → S → A) (k : ℕ) (s : S) :
    M.reachProbSem π (k + 1) s =
      if M.isTarget s = true then 1
      else if M.isTerm s = true then 0
      else ∑ s', M.P s (π 0 s) s' * M.reachProbSem (MDP.shift π) k s' := by
  rw [M.reachProbSem_succ]
  by_cases htg : M.isTarget s = true
  · rw [if_pos htg, if_pos htg]
  · rw [if_neg htg, if_neg htg]
    by_cases ht : M.isTerm s = true
    · rw [if_pos ht, M.sum_absorbing _ ht, M.reachProbSem_term _ k ht, if_neg htg]
    · rw [if_neg ht]

/-! ## Soundness: no policy beats the dynamic program -/

/-- Soundness, in the shape the induction wants it (all of `π`, `s` generalised). -/
theorem reachProbSem_le_reachVal_aux :
    ∀ (k : ℕ) (π : ℕ → S → A), M.IsPolicy π → ∀ s : S,
      M.reachProbSem π k s ≤ M.reachVal k s := by
  intro k
  induction k with
  | zero => intro π _ s; rw [M.reachProbSem_zero, M.reachVal_zero]
  | succ k ih =>
      intro π hπ s
      by_cases htg : M.isTarget s = true
      · rw [M.reachProbSem_succ, if_pos htg,
          M.reachVal_term (k + 1) (M.target_isTerm s htg), if_pos htg]
      · rw [M.reachProbSem_succ, if_neg htg]
        refine le_trans (Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (ih _ hπ.shift _) (M.P_nonneg s (π 0 s) s')) ?_
        by_cases ht : M.isTerm s = true
        · rw [M.sum_absorbing _ ht]
          exact M.reachVal_mono k s
        · rw [M.reachVal_succ_nonterm k (by simpa using ht)]
          exact Finset.le_sup'
            (f := fun a => ∑ s', M.P s a s' * M.reachVal k s') (hπ 0 s)

/-- **Soundness.**  For every *valid* policy, the genuine probability of reaching
`S_T` within `k` steps from `s` is at most `reachVal k s`: the dynamic program is
an upper bound on what any policy — even a time-dependent one — can achieve. -/
theorem reachProbSem_le_reachVal {π : ℕ → S → A} (hπ : M.IsPolicy π) (k : ℕ) (s : S) :
    M.reachProbSem π k s ≤ M.reachVal k s :=
  M.reachProbSem_le_reachVal_aux k π hπ s

/-! ## Attainment: the greedy policy meets the dynamic program -/

/-- An action attaining `max_{a ∈ A(s)} ∑_{s'} P(s' ∣ s,a) · reachVal j s'` — the
greedy action for a *remaining* horizon of `j + 1`. -/
noncomputable def greedyAct (M : MDP S A) (j : ℕ) (s : S) : A :=
  Classical.choose (Finset.exists_mem_eq_sup' (M.enabled_nonempty s)
    (fun a => ∑ s', M.P s a s' * M.reachVal j s'))

theorem greedyAct_mem (j : ℕ) (s : S) : M.greedyAct j s ∈ M.enabled s :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (M.enabled_nonempty s)
    (fun a => ∑ s', M.P s a s' * M.reachVal j s'))).1

theorem sum_greedyAct (j : ℕ) (s : S) :
    ∑ s', M.P s (M.greedyAct j s) s' * M.reachVal j s' =
      (M.enabled s).sup' (M.enabled_nonempty s)
        fun a => ∑ s', M.P s a s' * M.reachVal j s' :=
  ((Classical.choose_spec (Finset.exists_mem_eq_sup' (M.enabled_nonempty s)
    (fun a => ∑ s', M.P s a s' * M.reachVal j s'))).2).symm

/-- **The horizon-`k` optimal policy**: at time `t` there are `k - t` steps left,
so act greedily for the remaining horizon. -/
noncomputable def optPolicy (M : MDP S A) (k : ℕ) : ℕ → S → A :=
  fun t s => M.greedyAct (k - t - 1) s

theorem isPolicy_optPolicy (k : ℕ) : M.IsPolicy (M.optPolicy k) :=
  fun _ s => M.greedyAct_mem _ s

theorem shift_optPolicy (k : ℕ) : MDP.shift (M.optPolicy (k + 1)) = M.optPolicy k := by
  funext t s
  simp only [MDP.shift, optPolicy, Nat.succ_sub_succ]

/-- **Attainment.**  The greedy policy's genuine reachability probability *equals*
the dynamic program. -/
theorem reachProbSem_optPolicy (k : ℕ) (s : S) :
    M.reachProbSem (M.optPolicy k) k s = M.reachVal k s := by
  induction k generalizing s with
  | zero => rw [M.reachProbSem_zero, M.reachVal_zero]
  | succ k ih =>
      rw [M.reachProbSem_succ, M.shift_optPolicy k]
      by_cases htg : M.isTarget s = true
      · rw [if_pos htg, M.reachVal_term (k + 1) (M.target_isTerm s htg), if_pos htg]
      · rw [if_neg htg]
        have hsum : ∑ s', M.P s (M.optPolicy (k + 1) 0 s) s' * M.reachProbSem (M.optPolicy k) k s'
            = ∑ s', M.P s (M.greedyAct k s) s' * M.reachVal k s' := by
          have hact : M.optPolicy (k + 1) 0 s = M.greedyAct k s := by
            simp [optPolicy]
          rw [hact]
          exact Finset.sum_congr rfl fun s' _ => by rw [ih s']
        rw [hsum]
        by_cases ht : M.isTerm s = true
        · rw [M.sum_absorbing _ ht, M.reachVal_term k ht, M.reachVal_term (k + 1) ht]
        · rw [M.sum_greedyAct k s, M.reachVal_succ_nonterm k (by simpa using ht)]

/-! ## The headline: `reachVal` **is** the optimal reachability probability -/

/-- The set of finite-horizon reachability probabilities achievable at `s` with a
valid policy. -/
def reachProbSet (M : MDP S A) (k : ℕ) (s : S) : Set ℝ :=
  {x : ℝ | ∃ π : ℕ → S → A, M.IsPolicy π ∧ M.reachProbSem π k s = x}

/-- **`reachVal k s` is the *maximum*, over valid policies, of the genuine
probability of reaching `S_T` within `k` steps from `s`.**

This is exactly the reading the docstring of `MDP.reachVal` asserts, and it is
the optimal reachability value at a finite horizon.  `IsGreatest` says both
halves at once: `reachVal` is an upper bound (soundness — no policy does better) and it
is attained (by `optPolicy k`). -/
theorem isGreatest_reachProbSem (k : ℕ) (s : S) :
    IsGreatest (M.reachProbSet k s) (M.reachVal k s) :=
  ⟨⟨M.optPolicy k, M.isPolicy_optPolicy k, M.reachProbSem_optPolicy k s⟩, by
    rintro x ⟨π, hπ, rfl⟩
    exact M.reachProbSem_le_reachVal hπ k s⟩

theorem reachVal_eq_sSup_reachProbSem (k : ℕ) (s : S) :
    M.reachVal k s = sSup (M.reachProbSet k s) :=
  (M.isGreatest_reachProbSem k s).csSup_eq.symm

instance nonempty_policySubtype : Nonempty {π : ℕ → S → A // M.IsPolicy π} :=
  ⟨⟨M.optPolicy 0, M.isPolicy_optPolicy 0⟩⟩

/-- The same statement in `⨆` form, over the subtype of valid policies. -/
theorem reachVal_eq_iSup_reachProbSem (k : ℕ) (s : S) :
    M.reachVal k s = ⨆ π : {π : ℕ → S → A // M.IsPolicy π}, M.reachProbSem π.1 k s := by
  refine le_antisymm ?_ (ciSup_le fun π => M.reachProbSem_le_reachVal π.2 k s)
  refine le_ciSup_of_le ⟨M.reachVal k s, ?_⟩ ⟨M.optPolicy k, M.isPolicy_optPolicy k⟩
    (le_of_eq (M.reachProbSem_optPolicy k s).symm)
  rintro x ⟨π, rfl⟩
  exact M.reachProbSem_le_reachVal π.2 k s

/-! ## The payoff for `V*` -/

/-- The greedy policies' probabilities converge to `V*`: the `k`-step optimal
policy reaches `S_T` within `k` steps with probability tending to `V* s`. -/
theorem tendsto_reachProbSem_optPolicy (s : S) :
    Tendsto (fun k => M.reachProbSem (M.optPolicy k) k s) atTop (𝓝 (M.Vstar s)) := by
  simpa only [M.reachProbSem_optPolicy] using M.tendsto_reachVal s

/-- The set of reachability probabilities achievable at `s` over *all* horizons
and *all* valid policies. -/
def reachProbSetAll (M : MDP S A) (s : S) : Set ℝ :=
  {x : ℝ | ∃ (k : ℕ) (π : ℕ → S → A), M.IsPolicy π ∧ M.reachProbSem π k s = x}

/-- **`V*(s)` is the supremum, over valid policies and horizons, of the genuine
probability of reaching `S_T`** — the standard `V*(s) = sup_π V^π(s)` with
`V^π(s) = P^π(τ ⊨ S_T ∣ s₀ = s)` (the optimal reachability value), read at finite horizons and
passed to the limit.  Together with `Qsem_eq_Qstar` this makes the headline
theorem a statement about the real object. -/
theorem Vstar_isLUB_reachProbSem (s : S) : IsLUB (M.reachProbSetAll s) (M.Vstar s) := by
  constructor
  · rintro x ⟨k, π, hπ, rfl⟩
    exact le_trans (M.reachProbSem_le_reachVal hπ k s) (M.reachVal_le_Vstar k s)
  · intro b hb
    rw [M.Vstar_def]
    refine ciSup_le fun k => ?_
    exact (M.reachProbSem_optPolicy k s) ▸
      hb ⟨k, M.optPolicy k, M.isPolicy_optPolicy k, rfl⟩

theorem Vstar_eq_sSup_reachProbSem (s : S) : M.Vstar s = sSup (M.reachProbSetAll s) :=
  ((M.Vstar_isLUB_reachProbSem s).csSup_eq
    ⟨M.reachProbSem (M.optPolicy 0) 0 s, 0, M.optPolicy 0, M.isPolicy_optPolicy 0, rfl⟩).symm

end MDP

end Arlib
