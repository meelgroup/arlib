/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Hitting times of a finite Markov chain, without measure theory

The whole of this module is an elementary, purely algebraic account of the
question *"how long does a finite chain take to hit a set `T`?"*.  No trajectory
space, no σ-algebra and no measure is ever constructed: every statement is about
finite sums and one real series.

The single definition everything rests on is the **killed operator**

  `killed K T f x = 0` if `x ∈ T`, and `∑ y, K x y * f y` otherwise,

i.e. the one-step operator of `PotentialDecay` with the target set turned into a
graveyard.  Iterating it on the indicator of `Tᶜ` gives the **survival
probabilities**

  `survive K T n x = Pr_x[H_T > n]`,

which are the only probabilistic objects in the file.  They satisfy the
recursion that *defines* them, so no theorem is needed to connect them to a
trajectory measure — they are taken as the definition of the hitting-time law,
and every downstream statement is phrased in terms of them.

* `offTarget`, `killed`, `survive` — the three definitions.
* `survive_nonneg`, `survive_le_one`, `survive_eq_zero_of_mem`,
  `survive_antitone` — the basic shape of `n ↦ Pr_x[H_T > n]`.
* `killed_iterate_offTarget` / `survive_add` — `survive` *is* an iterate, which
  is what makes the next lemma available.
* `survive_add_le` — **submultiplicativity**: if `survive K T n ≤ c` off `T`,
  then `survive K T (m + n) ≤ c · survive K T m`.  This is the workhorse: it
  turns "the chain hits `T` with probability `≥ 1 - c` in `n` steps, from
  wherever it is" into geometric decay of the survival probabilities.
* `AlmostSureReach` — the specification: `Pr_x[H_T > n] → 0`.
* `EHT` — the **expected hitting time** `∑' n, Pr_x[H_T > n]`, the tail-sum
  formula taken as the definition, together with `HittingSummable` (the
  hypothesis under which that series means what it says).
* `EHT_recursion` — the one-step recursion `E_x[H_T] = 1 + ∑ y, K x y · E_y[H_T]`
  off the target, which is the form a *certificate* consumes.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.PotentialDecay

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The killed operator and the survival probabilities -/

/-- The indicator of the complement of the target set: `1` off `T`, `0` on `T`.
This is `Pr_x[H_T > 0]`, the starting point of the survival recursion. -/
def offTarget (T : Finset Ω) : Ω → ℝ := fun x => if x ∈ T then 0 else 1

/-- The one-step operator **killed** on `T`: the chain is stopped (sent to a
graveyard of value `0`) as soon as it enters `T`. -/
def killed (K : FinChain Ω) (T : Finset Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => if x ∈ T then 0 else act K f x

/-- `survive K T n x` is `Pr_x[H_T > n]`, the probability that the chain started
at `x` has *not* visited `T` at any of the times `0, 1, …, n`.

This recursion is the definition, not a theorem: `Pr_x[H_T > 0] = 1` iff `x ∉ T`,
and `Pr_x[H_T > n+1] = ∑ y, K x y · Pr_y[H_T > n]` for `x ∉ T`. -/
def survive (K : FinChain Ω) (T : Finset Ω) : ℕ → Ω → ℝ
  | 0 => offTarget T
  | (n + 1) => killed K T (survive K T n)

omit [Fintype Ω] in
@[simp] theorem offTarget_apply (T : Finset Ω) (x : Ω) :
    offTarget T x = if x ∈ T then 0 else 1 := rfl

@[simp] theorem killed_apply (K : FinChain Ω) (T : Finset Ω) (f : Ω → ℝ) (x : Ω) :
    killed K T f x = if x ∈ T then 0 else act K f x := rfl

@[simp] theorem survive_zero (K : FinChain Ω) (T : Finset Ω) :
    survive K T 0 = offTarget T := rfl

@[simp] theorem survive_succ (K : FinChain Ω) (T : Finset Ω) (n : ℕ) :
    survive K T (n + 1) = killed K T (survive K T n) := rfl

theorem survive_succ_apply (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T (n + 1) x = if x ∈ T then 0 else ∑ y, K x y * survive K T n y := rfl

/-! ### Basic shape -/

omit [Fintype Ω] in
theorem offTarget_nonneg (T : Finset Ω) (x : Ω) : 0 ≤ offTarget T x := by
  simp only [offTarget]; split <;> norm_num

omit [Fintype Ω] in
theorem offTarget_le_one (T : Finset Ω) (x : Ω) : offTarget T x ≤ 1 := by
  simp only [offTarget]; split <;> norm_num

theorem killed_mono (K : FinChain Ω) (T : Finset Ω) {f g : Ω → ℝ} (h : ∀ y, f y ≤ g y)
    (x : Ω) : killed K T f x ≤ killed K T g x := by
  simp only [killed]; split
  · exact le_refl _
  · exact act_mono K h x

theorem killed_nonneg (K : FinChain Ω) (T : Finset Ω) {f : Ω → ℝ} (hf : ∀ y, 0 ≤ f y)
    (x : Ω) : 0 ≤ killed K T f x := by
  simp only [killed]; split
  · exact le_refl _
  · exact act_nonneg K f hf x

theorem killed_smul (K : FinChain Ω) (T : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    killed K T (fun y => c * f y) = fun x => c * killed K T f x := by
  funext x
  simp only [killed, act]
  split
  · ring
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring

theorem survive_nonneg (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    0 ≤ survive K T n x := by
  induction n generalizing x with
  | zero => exact offTarget_nonneg T x
  | succ n ih => exact killed_nonneg K T (fun y => ih y) x

theorem survive_le_one (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T n x ≤ 1 := by
  induction n generalizing x with
  | zero => exact offTarget_le_one T x
  | succ n ih =>
      rw [survive_succ, killed_apply]
      split
      · norm_num
      · calc act K (survive K T n) x = ∑ y, K x y * survive K T n y := rfl
          _ ≤ ∑ y, K x y * 1 :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left (ih y) (K.coe_nonneg x y)
          _ = 1 := by rw [← Finset.sum_mul, K.sum_coe x, one_mul]

theorem survive_eq_zero_of_mem (K : FinChain Ω) (T : Finset Ω) (n : ℕ) {x : Ω}
    (hx : x ∈ T) : survive K T n x = 0 := by
  cases n with
  | zero => simp [hx]
  | succ n => simp [hx]

/-- `Pr_x[H_T > n] ≤ 1` off the target and `= 0` on it: the survival
probabilities are dominated by the indicator of `Tᶜ`. -/
theorem survive_le_offTarget (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T n x ≤ offTarget T x := by
  by_cases hx : x ∈ T
  · rw [survive_eq_zero_of_mem K T n hx, offTarget_apply, if_pos hx]
  · rw [offTarget_apply, if_neg hx]; exact survive_le_one K T n x

/-- The survival probabilities are nonincreasing in the horizon: `{H_T > n+1}`
is contained in `{H_T > n}`. -/
theorem survive_succ_le (K : FinChain Ω) (T : Finset Ω) (n : ℕ) (x : Ω) :
    survive K T (n + 1) x ≤ survive K T n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ T
      · simp [hx]
      · rw [survive_succ, survive_zero, killed_apply, if_neg hx, offTarget_apply, if_neg hx]
        calc act K (offTarget T) x = ∑ y, K x y * offTarget T y := rfl
          _ ≤ ∑ y, K x y * 1 :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left (offTarget_le_one T y) (K.coe_nonneg x y)
          _ = 1 := by rw [← Finset.sum_mul, K.sum_coe x, one_mul]
  | succ n ih => exact killed_mono K T (fun y => ih y) x

theorem survive_antitone (K : FinChain Ω) (T : Finset Ω) {m n : ℕ} (h : m ≤ n) (x : Ω) :
    survive K T n x ≤ survive K T m x := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (survive_succ_le K T n x) ih

/-! ### `survive` as an iterate, and submultiplicativity -/

theorem killed_iterate_offTarget (K : FinChain Ω) (T : Finset Ω) (n : ℕ) :
    (killed K T)^[n] (offTarget T) = survive K T n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, survive_succ]

theorem survive_add (K : FinChain Ω) (T : Finset Ω) (m n : ℕ) :
    survive K T (m + n) = (killed K T)^[m] (survive K T n) := by
  induction m with
  | zero => rw [Nat.zero_add, Function.iterate_zero_apply]
  | succ m ih =>
      have hmn : m + 1 + n = (m + n) + 1 := by omega
      rw [hmn, survive_succ, Function.iterate_succ_apply', ih]

theorem killed_iterate_mono (K : FinChain Ω) (T : Finset Ω) (m : ℕ) {f g : Ω → ℝ}
    (h : ∀ y, f y ≤ g y) (x : Ω) :
    (killed K T)^[m] f x ≤ (killed K T)^[m] g x := by
  induction m generalizing x with
  | zero => exact h x
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact killed_mono K T (fun y => ih y) x

theorem killed_iterate_smul (K : FinChain Ω) (T : Finset Ω) (m : ℕ) (c : ℝ) (f : Ω → ℝ) :
    (killed K T)^[m] (fun y => c * f y) = fun x => c * (killed K T)^[m] f x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext x
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact congrFun (killed_smul K T c ((killed K T)^[m] f)) x

set_option linter.unusedVariables false in
/-- **Submultiplicativity of the survival probabilities.**  If from *every*
state the chain hits `T` within `n` steps with probability at least `1 - c`,
then surviving `m + n` steps costs a further factor of `c`.

This is the only structural fact needed to turn a uniform "hit within `n` steps"
bound into geometric decay, and hence into a finite expected hitting time. -/
theorem survive_add_le (K : FinChain Ω) (T : Finset Ω) {c : ℝ} (hc : 0 ≤ c) (m n : ℕ)
    (h : ∀ y, survive K T n y ≤ c * offTarget T y) (x : Ω) :
    survive K T (m + n) x ≤ c * survive K T m x := by
  rw [survive_add]
  calc (killed K T)^[m] (survive K T n) x
      ≤ (killed K T)^[m] (fun y => c * offTarget T y) x := killed_iterate_mono K T m h x
    _ = c * (killed K T)^[m] (offTarget T) x :=
        congrFun (killed_iterate_smul K T m c (offTarget T)) x
    _ = c * survive K T m x := by rw [killed_iterate_offTarget]

/-- Iterating `survive_add_le`: geometric decay along multiples of `n`. -/
theorem survive_mul_le (K : FinChain Ω) (T : Finset Ω) {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (h : ∀ y, survive K T n y ≤ c * offTarget T y) (k : ℕ) (x : Ω) :
    survive K T (k * n) x ≤ c ^ k := by
  induction k with
  | zero =>
      rw [Nat.zero_mul, pow_zero]
      exact survive_le_one K T 0 x
  | succ k ih =>
      have hk : (k + 1) * n = k * n + n := by ring
      rw [hk, pow_succ]
      calc survive K T (k * n + n) x ≤ c * survive K T (k * n) x :=
            survive_add_le K T hc (k * n) n h x
        _ ≤ c * c ^ k := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ k * c := by ring

/-! ## Almost-sure reachability -/

/-- `T` is reached **almost surely** from `x` when the probability of still not
having hit it tends to `0`. -/
def AlmostSureReach (K : FinChain Ω) (T : Finset Ω) (x : Ω) : Prop :=
  Filter.Tendsto (fun n => survive K T n x) Filter.atTop (nhds 0)

theorem almostSureReach_of_mem (K : FinChain Ω) (T : Finset Ω) {x : Ω} (hx : x ∈ T) :
    AlmostSureReach K T x := by
  have hzero : (fun n => survive K T n x) = fun _ => (0 : ℝ) :=
    funext fun n => survive_eq_zero_of_mem K T n hx
  rw [AlmostSureReach, hzero]
  exact tendsto_const_nhds

/-- Almost-sure reachability is exactly a `∀ ε > 0` statement about the survival
probabilities — the survival probabilities being antitone and nonnegative. -/
theorem almostSureReach_iff (K : FinChain Ω) (T : Finset Ω) (x : Ω) :
    AlmostSureReach K T x ↔ ∀ ε > (0 : ℝ), ∃ n, survive K T n x < ε := by
  rw [AlmostSureReach, Metric.tendsto_atTop]
  constructor
  · intro hlim ε hε
    obtain ⟨N, hN⟩ := hlim ε hε
    refine ⟨N, ?_⟩
    have hd := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (survive_nonneg K T N x)] at hd
  · intro hsmall ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    refine ⟨N, fun m hm => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (survive_nonneg K T m x)]
    exact lt_of_le_of_lt (survive_antitone K T hm x) hN

/-! ## The expected hitting time -/

/-- The hypothesis under which `EHT` means what it says: the tail-sum series
converges. -/
def HittingSummable (K : FinChain Ω) (T : Finset Ω) (x : Ω) : Prop :=
  Summable fun n => survive K T n x

/-- The **expected hitting time** `E_x[H_T]`, defined by the tail-sum formula
`E[H] = ∑_{n ≥ 0} Pr[H > n]`.

As always with `tsum`, this is `0` when the series diverges; every statement
below that needs the value to be meaningful carries a `HittingSummable`
hypothesis. -/
noncomputable def EHT (K : FinChain Ω) (T : Finset Ω) (x : Ω) : ℝ :=
  ∑' n, survive K T n x

theorem EHT_nonneg (K : FinChain Ω) (T : Finset Ω) (x : Ω) : 0 ≤ EHT K T x :=
  tsum_nonneg fun n => survive_nonneg K T n x

theorem EHT_eq_zero_of_mem (K : FinChain Ω) (T : Finset Ω) {x : Ω} (hx : x ∈ T) :
    EHT K T x = 0 := by
  have hzero : (fun n => survive K T n x) = fun _ => (0 : ℝ) :=
    funext fun n => survive_eq_zero_of_mem K T n hx
  rw [EHT, hzero, tsum_zero]

/-- A uniform bound on the partial sums gives both summability and the same
bound on the total. -/
theorem hittingSummable_of_partial_le (K : FinChain Ω) (T : Finset Ω) (x : Ω) {C : ℝ}
    (h : ∀ n, ∑ k ∈ Finset.range n, survive K T k x ≤ C) :
    HittingSummable K T x ∧ EHT K T x ≤ C :=
  ⟨summable_of_sum_range_le (fun n => survive_nonneg K T n x) h,
   Real.tsum_le_of_sum_range_le (fun n => survive_nonneg K T n x) h⟩

theorem almostSureReach_of_hittingSummable (K : FinChain Ω) (T : Finset Ω) {x : Ω}
    (h : HittingSummable K T x) : AlmostSureReach K T x :=
  h.tendsto_atTop_zero

/-! ### The block decomposition

A uniform "hit within `n` steps with probability at least `1 - c`" bound turns
into a bound on the whole tail series, by grouping the times into blocks of
length `n`.  This is the one place the geometric series appears, and both
consumers — the completeness half of `RankingSupermartingale` and the
`p_min` bound of `ProgressPath` — go through it. -/

/-- The partial sums of a geometric series of ratio `c ∈ [0, 1)` are bounded by
`1 / (1 - c)`.  Proved from `geom_sum_mul`, so no analysis is involved. -/
private theorem geom_sum_le_inv_one_sub {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, c ^ k ≤ 1 / (1 - c) := by
  have h1 : (0 : ℝ) < 1 - c := by linarith
  have h2 : (∑ k ∈ Finset.range N, c ^ k) * (1 - c) = 1 - c ^ N := by
    rw [← neg_sub c 1, mul_neg, geom_sum_mul]; ring
  rw [le_div_iff₀ h1, h2]
  linarith [pow_nonneg hc0 N]

/-- The block bound behind `sum_range_le_of_survive_le`: the first `N` blocks of
length `n` contribute at most `n · ∑_{k < N} c ^ k`, because every time in the
`k`-th block has survival probability at most `survive K T (k * n) ≤ c ^ k`. -/
private theorem sum_range_mul_le (K : FinChain Ω) (T : Finset Ω) {c : ℝ} (hc0 : 0 ≤ c)
    (n : ℕ) (h : ∀ y, survive K T n y ≤ c * offTarget T y) (x : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range (N * n), survive K T j x
      ≤ (n : ℝ) * ∑ k ∈ Finset.range N, c ^ k := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hle : N * n ≤ (N + 1) * n := Nat.mul_le_mul_right n (Nat.le_succ N)
      have hsplit : ∑ j ∈ Finset.range (N * n), survive K T j x
            + ∑ j ∈ Finset.Ico (N * n) ((N + 1) * n), survive K T j x
          = ∑ j ∈ Finset.range ((N + 1) * n), survive K T j x := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle,
          ← Finset.range_eq_Ico]
      have hcard : (N + 1) * n - N * n = n := by
        rw [Nat.succ_mul, Nat.add_sub_cancel_left]
      have hblock : ∑ j ∈ Finset.Ico (N * n) ((N + 1) * n), survive K T j x
          ≤ (n : ℝ) * c ^ N := by
        calc ∑ j ∈ Finset.Ico (N * n) ((N + 1) * n), survive K T j x
            ≤ ∑ _j ∈ Finset.Ico (N * n) ((N + 1) * n), c ^ N :=
              Finset.sum_le_sum fun j hj =>
                le_trans (survive_antitone K T (Finset.mem_Ico.mp hj).1 x)
                  (survive_mul_le K T hc0 n h N x)
          _ = (n : ℝ) * c ^ N := by
              rw [Finset.sum_const, Nat.card_Ico, hcard, nsmul_eq_mul]
      have hgeom : (n : ℝ) * ∑ k ∈ Finset.range (N + 1), c ^ k
          = (n : ℝ) * ∑ k ∈ Finset.range N, c ^ k + (n : ℝ) * c ^ N := by
        rw [Finset.sum_range_succ]; ring
      rw [← hsplit, hgeom]
      exact add_le_add ih hblock

/-- **The block decomposition.**  If from every state the chain hits `T` within
`n ≥ 1` steps with probability at least `1 - c`, `c < 1`, then every partial sum
of the tail series is at most `n / (1 - c)`. -/
theorem sum_range_le_of_survive_le (K : FinChain Ω) (T : Finset Ω) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ y, survive K T n y ≤ c * offTarget T y) (x : Ω) (m : ℕ) :
    ∑ k ∈ Finset.range m, survive K T k x ≤ (n : ℝ) / (1 - c) := by
  have hmn : m ≤ m * n := by
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * n := Nat.mul_le_mul_left m hn
  have hgrow : ∑ k ∈ Finset.range m, survive K T k x
      ≤ ∑ k ∈ Finset.range (m * n), survive K T k x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
      fun k _ _ => survive_nonneg K T k x
  have hblocks := sum_range_mul_le K T hc0 n h x m
  have hgeom : (n : ℝ) * ∑ k ∈ Finset.range m, c ^ k ≤ (n : ℝ) * (1 / (1 - c)) :=
    mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hc0 hc1 m) (Nat.cast_nonneg n)
  have hfin : (n : ℝ) * (1 / (1 - c)) = (n : ℝ) / (1 - c) := by ring
  linarith

/-- Hence the expected hitting time is finite and at most `n / (1 - c)`. -/
theorem hittingSummable_of_survive_le (K : FinChain Ω) (T : Finset Ω) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ y, survive K T n y ≤ c * offTarget T y) (x : Ω) :
    HittingSummable K T x ∧ EHT K T x ≤ (n : ℝ) / (1 - c) :=
  hittingSummable_of_partial_le K T x (sum_range_le_of_survive_le K T hc0 hc1 hn h x)

/-- **The one-step recursion for the expected hitting time.**  Off the target,
`E_x[H_T] = 1 + ∑ y, K x y · E_y[H_T]`.

This is the identity that makes `EHT` a ranking supermartingale with
`ε = 1`: the `+1` *is* the unit of expected progress. -/
theorem EHT_recursion (K : FinChain Ω) (T : Finset Ω) (hs : ∀ y, HittingSummable K T y)
    {x : Ω} (hx : x ∉ T) :
    EHT K T x = 1 + ∑ y, K x y * EHT K T y := by
  rw [EHT, Summable.tsum_eq_zero_add (hs x)]
  congr 1
  · rw [survive_zero, offTarget_apply, if_neg hx]
  · have hstep : ∀ n, survive K T (n + 1) x = ∑ y, K x y * survive K T n y := fun n => by
      rw [survive_succ_apply, if_neg hx]
    simp only [hstep]
    rw [Summable.tsum_finsetSum (fun y _ => (hs y).mul_left (K x y))]
    exact Finset.sum_congr rfl fun y _ => tsum_mul_left

end Arlib.MarkovChains
