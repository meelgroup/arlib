/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Ranking supermartingales: soundness and completeness

A **ranking supermartingale** (RSM) for a target set `T`, with slack `ε > 0`, is
a nonnegative function `V` on the state space that drops by at least `ε` in
expectation at every state outside `T`:

  `V ≥ 0`  and  `(K V)(x) + ε ≤ V(x)` for `x ∉ T`.

It is the standard certificate for almost-sure reachability.  This module proves
that it is **sound** and **complete** for a finite chain, and it does so without
any measure theory: the whole argument is the single crux inequality

  `ε · ∑_{k < n} Pr_x[H_T > k] ≤ V(x)`  for every `n`  (`sum_survive_le_of_isRSM`),

obtained by iterating the drift condition through the killed operator of
`HittingTime`.  Everything else is a corollary of it:

* `summable_survive_of_isRSM`, `EHT_le_of_isRSM` — the tail sums are bounded, so
  the expected hitting time is finite and at most `V(x) / ε`.  This is *stronger*
  than almost-sure reachability, and it comes out of the same one-line bound.
* `almostSureReach_of_isRSM` — **soundness**: an RSM forces `Pr_x[H_T > n] → 0`
  from every state.
* `isRSM_EHT` — **completeness**: when the expected hitting time is finite
  everywhere it is itself a `1`-RSM, by the recursion `EHT_recursion`.
* `exists_isRSM_iff` — the two directions assembled: an RSM exists **iff** `T` is
  reached almost surely *from every state*.

The quantifier in the last statement is load-bearing and is worth spelling out,
because the literature routinely states the equivalence with reachability from a
single initial state `x₀`.  That version is **false**: `not_isRSM_of_unreachable`
exhibits a two-state chain in which `T` is reached almost surely from `x₀` and
yet no RSM exists, because the defining inequality is imposed at *every* state
outside `T`, including states that `x₀` can never reach.  Restricting `V` to the
reachable part and extending it by `0` — the usual repair — does not work: the
extension violates the drift condition at exactly those states.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.HittingTime

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The certificate -/

/-- `IsRSM K T ε V`: `V` is an **`ε`-ranking supermartingale** for the chain `K`
with respect to the target set `T`. -/
structure IsRSM (K : FinChain Ω) (T : Finset Ω) (ε : ℝ) (V : Ω → ℝ) : Prop where
  /-- The slack is strictly positive; this is what forces *progress*. -/
  eps_pos : 0 < ε
  /-- The rank is nonnegative: progress cannot continue for ever. -/
  nonneg : ∀ x, 0 ≤ V x
  /-- Off the target, one step of the chain decreases the rank by at least `ε`
  in expectation. -/
  decrease : ∀ x ∉ T, act K V x + ε ≤ V x

/-! ## Linearity of the killed operator

Three small facts about `killed` that the induction below uses repeatedly:
it is additive, homogeneous, and preserves nonnegativity along iterates. -/

/-- The killed operator is additive (stated for a difference, the form needed). -/
theorem killed_sub (K : FinChain Ω) (T : Finset Ω) (f g : Ω → ℝ) (x : Ω) :
    killed K T (fun y => f y - g y) x = killed K T f x - killed K T g x := by
  by_cases hx : x ∈ T
  · simp [killed, hx]
  · rw [killed_apply, if_neg hx, killed_apply, if_neg hx, killed_apply, if_neg hx]
    exact congrFun (act_sub K f g) x

/-- Pointwise form of `killed_smul`. -/
theorem killed_smul_apply (K : FinChain Ω) (T : Finset Ω) (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    killed K T (fun y => c * f y) x = c * killed K T f x :=
  congrFun (killed_smul K T c f) x

/-- The killed operator commutes with a finite sum of survival probabilities and
shifts the horizon by one. -/
theorem killed_sum_survive (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    killed K T (fun y => ∑ k ∈ Finset.range n, survive K T k y) x
      = ∑ k ∈ Finset.range n, survive K T (k + 1) x := by
  by_cases hx : x ∈ T
  · rw [killed_apply, if_pos hx]
    exact (Finset.sum_eq_zero fun k _ => survive_eq_zero_of_mem K T (k + 1) hx).symm
  · rw [killed_apply, if_neg hx, act_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by
      rw [survive_succ_apply, if_neg hx]

/-- Iterating the killed operator preserves nonnegativity. -/
theorem killed_iterate_nonneg (K : FinChain Ω) (T : Finset Ω) (n : ℕ) {f : Ω → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : Ω) : 0 ≤ (killed K T)^[n] f x := by
  induction n generalizing f with
  | zero => simpa using hf x
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (killed_nonneg K T hf)

/-! ## The crux inequality -/

/-- The killed rank: `V` outside `T`, `0` on `T`.  Nonnegativity of `V` makes it
a lower bound for `V`, and the drift condition passes to it. -/
theorem killed_offTarget_mul_le (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) :
    killed K T (fun y => offTarget T y * V y) x
      ≤ offTarget T x * V x - ε * offTarget T x := by
  by_cases hx : x ∈ T
  · rw [killed_apply, if_pos hx]
    simp [offTarget, hx]
  · rw [killed_apply, if_neg hx]
    have hpt : ∀ y, offTarget T y * V y ≤ V y := fun y =>
      mul_le_of_le_one_left (h.nonneg y) (offTarget_le_one T y)
    have h1 : act K (fun y => offTarget T y * V y) x ≤ act K V x := act_mono K hpt x
    have h2 := h.decrease x hx
    have ho : offTarget T x = 1 := by simp [offTarget, hx]
    rw [ho]
    linarith

/-- The induction behind the crux inequality: iterating the killed operator on
the killed rank subtracts `ε` times the accumulated survival probabilities. -/
theorem killed_iterate_offTarget_mul_le (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (n : ℕ) (x : Ω) :
    (killed K T)^[n] (fun y => offTarget T y * V y) x
      ≤ offTarget T x * V x - ε * ∑ k ∈ Finset.range n, survive K T k x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have step1 : killed K T ((killed K T)^[n] (fun y => offTarget T y * V y)) x
        ≤ killed K T (fun y => offTarget T y * V y
            - ε * ∑ k ∈ Finset.range n, survive K T k y) x :=
      killed_mono K T ih x
    have step2 : killed K T (fun y => offTarget T y * V y
            - ε * ∑ k ∈ Finset.range n, survive K T k y) x
        = killed K T (fun y => offTarget T y * V y) x
          - ε * ∑ k ∈ Finset.range n, survive K T (k + 1) x := by
      rw [killed_sub, killed_smul_apply, killed_sum_survive]
    have step3 := killed_offTarget_mul_le K T h x
    have step4 : ∑ k ∈ Finset.range (n + 1), survive K T k x
        = (∑ k ∈ Finset.range n, survive K T (k + 1) x) + offTarget T x := by
      rw [Finset.sum_range_succ']
      simp
    rw [step4]
    linarith

/-- **The crux inequality.**  For an `ε`-RSM, the first `n` tail probabilities of
the hitting time sum to at most `V(x) / ε`:

  `ε · ∑_{k < n} Pr_x[H_T > k] ≤ V(x)`.

Everything in this module is a corollary.  The proof is an induction on `n`
inside the killed operator: `killed^n (1_{Tᶜ}·V) ≤ 1_{Tᶜ}·V - ε ∑_{k<n} survive k`,
and the left-hand side is nonnegative. -/
theorem sum_survive_le_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) (n : ℕ) :
    ε * ∑ k ∈ Finset.range n, survive K T k x ≤ V x := by
  have h1 := killed_iterate_offTarget_mul_le K T h n x
  have h2 : 0 ≤ (killed K T)^[n] (fun y => offTarget T y * V y) x :=
    killed_iterate_nonneg K T n
      (fun y => mul_nonneg (offTarget_nonneg T y) (h.nonneg y)) x
  have h3 : offTarget T x * V x ≤ V x :=
    mul_le_of_le_one_left (h.nonneg x) (offTarget_le_one T x)
  linarith

/-! ## Soundness -/

/-- **The maximal-inequality step, elementary.**  For an `ε`-RSM,

  `Pr_x[H_T > n] ≤ V(x) / (ε · n)`.

This is the quantitative heart of the classical argument — a nonnegative
supermartingale `Y_k = V(X_{k∧τ}) + ε·(k∧τ)` starting at `V(x)` satisfies
`Pr[sup_k Y_k ≥ λ] ≤ V(x)/λ`, applied at `λ = ε·n` — obtained here directly from
the crux inequality, since the survival probabilities are antitone: `n` terms of
the sum are each at least `survive n`. -/
theorem survive_le_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) {n : ℕ} (hn : 1 ≤ n) :
    survive K T n x ≤ V x / (ε * n) := by
  have hsum : (n : ℝ) * survive K T n x ≤ ∑ k ∈ Finset.range n, survive K T k x := by
    have hcard := Finset.card_nsmul_le_sum (Finset.range n) (fun k => survive K T k x)
      (survive K T n x) (fun k hk =>
        survive_antitone K T (le_of_lt (Finset.mem_range.mp hk)) x)
    simpa [nsmul_eq_mul] using hcard
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hεn : 0 < ε * n := mul_pos h.eps_pos hn0
  have h5 : ε * ((n : ℝ) * survive K T n x)
      ≤ ε * ∑ k ∈ Finset.range n, survive K T k x :=
    mul_le_mul_of_nonneg_left hsum (le_of_lt h.eps_pos)
  have h6 := sum_survive_le_of_isRSM K T h x n
  rw [le_div_iff₀ hεn]
  calc survive K T n x * (ε * n) = ε * ((n : ℝ) * survive K T n x) := by ring
    _ ≤ ε * ∑ k ∈ Finset.range n, survive K T k x := h5
    _ ≤ V x := h6

/-- The tail series of the survival probabilities is bounded by `V x / ε`, hence
summable. -/
theorem hittingSummable_and_EHT_le_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ}
    {V : Ω → ℝ} (h : IsRSM K T ε V) (x : Ω) :
    HittingSummable K T x ∧ EHT K T x ≤ V x / ε := by
  refine hittingSummable_of_partial_le K T x (C := V x / ε) ?_
  intro n
  rw [le_div_iff₀ h.eps_pos]
  have := sum_survive_le_of_isRSM K T h x n
  linarith

theorem hittingSummable_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) : HittingSummable K T x :=
  (hittingSummable_and_EHT_le_of_isRSM K T h x).1

/-- The expected hitting time is bounded by the rank divided by the slack. -/
theorem EHT_le_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) : EHT K T x ≤ V x / ε :=
  (hittingSummable_and_EHT_le_of_isRSM K T h x).2

/-- **Soundness of the certificate.**  If an `ε`-RSM exists then the target is
reached almost surely, from *every* state. -/
theorem almostSureReach_of_isRSM (K : FinChain Ω) (T : Finset Ω) {ε : ℝ} {V : Ω → ℝ}
    (h : IsRSM K T ε V) (x : Ω) : AlmostSureReach K T x :=
  almostSureReach_of_hittingSummable K T (hittingSummable_of_isRSM K T h x)

/-! ## Completeness -/

/-- **Completeness of the certificate.**  When the expected hitting time is
finite from every state, it is itself a `1`-RSM: the `+1` of the hitting-time
recursion is exactly the unit of expected progress. -/
theorem isRSM_EHT (K : FinChain Ω) (T : Finset Ω) (hs : ∀ y, HittingSummable K T y) :
    IsRSM K T 1 (EHT K T) where
  eps_pos := one_pos
  nonneg := EHT_nonneg K T
  decrease := by
    intro x hx
    have hrec := EHT_recursion K T hs hx
    rw [act_apply]
    linarith

/-- Almost-sure reachability from every state of a *finite* chain upgrades
automatically to a finite expected hitting time: the survival probabilities are
uniformly `≤ c < 1` after some common horizon, and `survive_add_le` turns that
into geometric decay. -/
theorem hittingSummable_of_almostSureReach (K : FinChain Ω) (T : Finset Ω)
    (h : ∀ x, AlmostSureReach K T x) (x : Ω) : HittingSummable K T x := by
  choose N hN using fun y => (almostSureReach_iff K T y).mp (h y) (1 / 2) (by norm_num)
  have key : ∀ y, survive K T (Finset.univ.sup N + 1) y ≤ (1 / 2 : ℝ) * offTarget T y := by
    intro y
    by_cases hy : y ∈ T
    · rw [survive_eq_zero_of_mem K T _ hy]
      simp [offTarget, hy]
    · have h1 : survive K T (Finset.univ.sup N + 1) y ≤ survive K T (N y) y :=
        survive_antitone K T
          (le_trans (Finset.le_sup (Finset.mem_univ y)) (Nat.le_succ _)) y
      have h2 := hN y
      have ho : offTarget T y = 1 := by simp [offTarget, hy]
      rw [ho]
      linarith
  exact (hittingSummable_of_survive_le K T (by norm_num) (by norm_num)
    (Nat.le_add_left 1 _) key x).1

/-- **Soundness and completeness together.**  An RSM exists for `(K, T)` if and
only if `T` is reached almost surely from *every* state.

The quantifier `∀ x` is not a convenience: see `not_isRSM_of_unreachable`. -/
theorem exists_isRSM_iff (K : FinChain Ω) (T : Finset Ω) :
    (∃ ε V, IsRSM K T ε V) ↔ ∀ x, AlmostSureReach K T x := by
  constructor
  · rintro ⟨ε, V, hV⟩ x
    exact almostSureReach_of_isRSM K T hV x
  · intro hreach
    exact ⟨1, EHT K T,
      isRSM_EHT K T fun y => hittingSummable_of_almostSureReach K T hreach y⟩

/-! ## The quantifier is necessary

A single-initial-state version of `exists_isRSM_iff` is false.  The witness is
the two-state chain in which both states are absorbing and the target is the
initial state: reachability from `x₀` is trivial, and yet the RSM condition is
imposed at the *other* state, where no nonnegative function can satisfy it. -/

/-- The two-state chain in which every state is absorbing. -/
def idChain : FinChain Bool where
  P x y := if y = x then 1 else 0
  P_nonneg x y := by split <;> norm_num
  P_sum x := by simp

/-- In `idChain` the target `{true}` is hit immediately from `true`. -/
theorem idChain_almostSureReach_true :
    AlmostSureReach idChain {true} true :=
  almostSureReach_of_mem _ _ (by simp)

/-- …and yet **no** ranking supermartingale exists for `(idChain, {true})`,
because the drift condition is imposed at `false`, which is absorbing.

Hence "an `ε`-RSM exists ⟺ `Pr_{x₀}[Reach T] = 1`" is false as stated; the
correct statement quantifies over all states (`exists_isRSM_iff`). -/
theorem not_exists_isRSM_idChain :
    ¬ ∃ ε V, IsRSM idChain ({true} : Finset Bool) ε V := by
  rintro ⟨ε, V, h⟩
  have hf : (false : Bool) ∉ ({true} : Finset Bool) := by simp
  have h1 := h.decrease false hf
  have h2 : act idChain V false = V false := by
    simp [FinKernel.act, idChain, Fintype.sum_bool]
  rw [h2] at h1
  have h3 := h.eps_pos
  linarith

end Arlib.MarkovChains
