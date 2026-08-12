/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Progress paths: a quantitative hitting-time bound from a graph condition

`HittingTime` reduces "how long to hit `T`?" to the survival probabilities
`survive K T n x`, and `RankingSupermartingale` bounds them from a certificate.
This module bounds them from a purely *combinatorial* condition on the chain,
which is how the certificate gets built in the first place.

The condition is `HasProgressPaths K T q D`: from every state there is a path to
`T` of length at most `D`, **all of whose steps have probability at least `q`**.
Following such a path is a single event of probability at least `q ^ D`, so:

* `survive_le_of_hasProgressPaths` — `Pr_x[H_T > D] ≤ 1 - q ^ D`, uniformly in
  `x`;
* `EHT_le_of_hasProgressPaths` — `E_x[H_T] ≤ D / q ^ D`, by feeding that uniform
  bound to the submultiplicativity lemma `survive_mul_le` and summing the
  resulting geometric series in blocks of length `D`;
* `almostSureReach_of_hasProgressPaths` — and hence almost-sure reachability.

Stating the hypothesis in terms of a *path with a uniform edge bound* rather
than "every nonzero transition probability is at least `q`" is deliberate, and
it is what makes the module reusable.  The two are equivalent for the chain one
starts from, but the interesting applications perturb the chain: an estimated
kernel `K'` that is close to `K` need not have a uniform lower bound on its
nonzero entries — a spurious transition can carry arbitrarily small mass — while
it *does* still contain every progress path of `K`, with each edge weight
reduced by at most the estimation error.  `hasProgressPaths_of_le` is that
transfer, and it is the reason the bound survives estimation.

* `ReachInWith`, `HasProgressPaths` — the graph condition.
* `hasProgressPaths_of_le` — and it transfers to any kernel that dominates the
  progress edges.

The bridge from the usual "`p_min` bounds every nonzero transition" hypothesis
to this condition is `Techniques.ReachDistance`, which also supplies the
distance function `Dist` and the eccentricity `D`.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.RankingSupermartingale

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The graph condition -/

/-- `ReachInWith K T q n x`: the target `T` can be reached from `x` in at most
`n` steps along transitions each of probability at least `q`. -/
def ReachInWith (K : FinChain Ω) (T : Finset Ω) (q : ℝ) : ℕ → Ω → Prop
  | 0, x => x ∈ T
  | (n + 1), x => x ∈ T ∨ ∃ y, q ≤ K x y ∧ ReachInWith K T q n y

/-- From every state there is a path to `T` of length at most `D`, each of whose
steps has probability at least `q`. -/
def HasProgressPaths (K : FinChain Ω) (T : Finset Ω) (q : ℝ) (D : ℕ) : Prop :=
  ∀ x, ReachInWith K T q D x

omit [DecidableEq Ω] in
theorem reachInWith_of_mem (K : FinChain Ω) (T : Finset Ω) (q : ℝ) (n : ℕ) {x : Ω}
    (hx : x ∈ T) : ReachInWith K T q n x := by
  cases n with
  | zero => exact hx
  | succ n => exact Or.inl hx

omit [DecidableEq Ω] in
/-- One extra step of budget never hurts. -/
theorem reachInWith_succ (K : FinChain Ω) (T : Finset Ω) (q : ℝ) :
    ∀ (n : ℕ) (x : Ω), ReachInWith K T q n x → ReachInWith K T q (n + 1) x := by
  intro n
  induction n with
  | zero => intro x hx; exact Or.inl hx
  | succ n ih =>
    intro x hx
    rcases hx with hx | ⟨y, hy, hry⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy, ih y hry⟩

omit [DecidableEq Ω] in
/-- A shorter path is also a path of the allowed length. -/
theorem reachInWith_mono (K : FinChain Ω) (T : Finset Ω) (q : ℝ) {m n : ℕ} (h : m ≤ n)
    {x : Ω} (hx : ReachInWith K T q m x) : ReachInWith K T q n x := by
  induction n, h using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact reachInWith_succ K T q n x ih

omit [DecidableEq Ω] in
/-- Lowering the required edge weight only makes paths easier to find. -/
theorem reachInWith_mono_prob (K : FinChain Ω) (T : Finset Ω) {q q' : ℝ} (h : q' ≤ q)
    (n : ℕ) {x : Ω} (hx : ReachInWith K T q n x) : ReachInWith K T q' n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    rcases hx with hx | ⟨y, hy, hry⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, le_trans h hy, ih hry⟩

omit [DecidableEq Ω] in
/-- **Transfer along a perturbation.**  Any kernel whose entries dominate `K`'s
progress edges (up to the shift `q - q'`) inherits the progress paths.  This is
the form used for an *estimated* kernel `K'` with `|K - K'| ≤ q - q'` entrywise:
`K'` keeps every progress path of `K`, with each edge weight reduced by at most
the estimation error. -/
theorem hasProgressPaths_of_le (K K' : FinChain Ω) (T : Finset Ω) {q q' : ℝ} (D : ℕ)
    (h : HasProgressPaths K T q D) (hle : ∀ x y, q ≤ K x y → q' ≤ K' x y) :
    HasProgressPaths K' T q' D := by
  have key : ∀ (n : ℕ) (x : Ω), ReachInWith K T q n x → ReachInWith K' T q' n x := by
    intro n
    induction n with
    | zero => intro x hx; exact hx
    | succ n ih =>
      intro x hx
      rcases hx with hx | ⟨y, hy, hry⟩
      · exact Or.inl hx
      · exact Or.inr ⟨y, hle x y hy, ih y hry⟩
  exact fun x => key D x (h x)

/-! ## The uniform hitting bound -/

/-- Auxiliary: a probability raised to any power is at most `1`. -/
theorem pow_le_one_aux {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : ∀ m : ℕ, q ^ m ≤ 1 := by
  intro m
  induction m with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; nlinarith [pow_nonneg hq0 k]

/-- Following a progress path of length `n` succeeds with probability at least
`q ^ n`: the survival probability after `n` steps is at most `1 - q ^ n`. -/
theorem survive_le_of_reachInWith (K : FinChain Ω) (T : Finset Ω) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) {x : Ω} (hx : ReachInWith K T q n x) :
    survive K T n x ≤ 1 - q ^ n := by
  have hpow : ∀ m : ℕ, q ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith [pow_nonneg hq0 k]
  induction n generalizing x with
  | zero =>
    rw [survive_eq_zero_of_mem K T 0 hx]; norm_num
  | succ n ih =>
    rcases hx with hxT | ⟨y, hy, hry⟩
    · rw [survive_eq_zero_of_mem K T _ hxT]
      have := hpow (n + 1); linarith
    · by_cases hxT : x ∈ T
      · rw [survive_eq_zero_of_mem K T _ hxT]
        have := hpow (n + 1); linarith
      · have hb : ∀ z : Ω, survive K T n z ≤ 1 - (if z = y then q ^ n else 0) := by
          intro z
          by_cases hz : z = y
          · subst hz; rw [if_pos rfl]; exact ih hry
          · rw [if_neg hz, sub_zero]; exact survive_le_one K T n z
        have hsplit : ∀ z : Ω, K x z * (1 - (if z = y then q ^ n else 0))
            = K x z - (if z = y then K x y * q ^ n else 0) := by
          intro z
          by_cases hz : z = y
          · subst hz; rw [if_pos rfl, if_pos rfl]; ring
          · rw [if_neg hz, if_neg hz]; ring
        rw [survive_succ_apply, if_neg hxT]
        calc ∑ z, K x z * survive K T n z
            ≤ ∑ z, K x z * (1 - (if z = y then q ^ n else 0)) :=
              Finset.sum_le_sum fun z _ =>
                mul_le_mul_of_nonneg_left (hb z) (K.coe_nonneg x z)
          _ = 1 - K x y * q ^ n := by
              rw [Finset.sum_congr rfl fun z _ => hsplit z, Finset.sum_sub_distrib,
                K.sum_coe, Finset.sum_ite_eq' Finset.univ y (fun _ => K x y * q ^ n)]
              simp
          _ ≤ 1 - q * q ^ n := by nlinarith [pow_nonneg hq0 n]
          _ = 1 - q ^ (n + 1) := by ring

/-- **The uniform hitting bound.**  Under `HasProgressPaths K T q D` the chain
hits `T` within `D` steps with probability at least `q ^ D`, from every state. -/
theorem survive_le_of_hasProgressPaths (K : FinChain Ω) (T : Finset Ω) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {D : ℕ} (h : HasProgressPaths K T q D) (x : Ω) :
    survive K T D x ≤ (1 - q ^ D) * offTarget T x := by
  by_cases hx : x ∈ T
  · rw [survive_eq_zero_of_mem K T D hx, offTarget_apply, if_pos hx, mul_zero]
  · rw [offTarget_apply, if_neg hx, mul_one]
    exact survive_le_of_reachInWith K T hq0 hq1 D (h x)

/-- **The expected hitting-time bound.**  `E_x[H_T] ≤ D / q ^ D`.

The proof is the block decomposition: `Pr_x[H_T > kD] ≤ (1 - q^D)^k` by
submultiplicativity, and the tail sum over each block of `D` consecutive times
is at most `D` times its first term. -/
theorem EHT_le_of_hasProgressPaths (K : FinChain Ω) (T : Finset Ω) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) {D : ℕ} (h : HasProgressPaths K T q D) (x : Ω) :
    HittingSummable K T x ∧ EHT K T x ≤ (D : ℝ) / q ^ D := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have hxT : x ∈ T := h x
    have hz : ∀ n, survive K T n x = 0 := fun n => survive_eq_zero_of_mem K T n hxT
    refine ⟨?_, ?_⟩
    · have hfun : (fun n => survive K T n x) = fun _ => (0 : ℝ) := funext hz
      show Summable fun n => survive K T n x
      rw [hfun]; exact summable_zero
    · rw [EHT_eq_zero_of_mem K T hxT]
      norm_num
  · have hqD0 : 0 < q ^ D := pow_pos hq0 D
    have hqD1 : q ^ D ≤ 1 := pow_le_one_aux hq0.le hq1 D
    have hc0 : (0 : ℝ) ≤ 1 - q ^ D := by linarith
    have hc1 : (1 : ℝ) - q ^ D < 1 := by linarith
    obtain ⟨hs, hb⟩ := hittingSummable_of_survive_le K T hc0 hc1 hD
      (survive_le_of_hasProgressPaths K T hq0.le hq1 h) x
    refine ⟨hs, ?_⟩
    rwa [sub_sub_cancel] at hb

theorem almostSureReach_of_hasProgressPaths (K : FinChain Ω) (T : Finset Ω) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) {D : ℕ} (h : HasProgressPaths K T q D) (x : Ω) :
    AlmostSureReach K T x :=
  almostSureReach_of_hittingSummable K T (EHT_le_of_hasProgressPaths K T hq0 hq1 h x).1

end Arlib.MarkovChains
