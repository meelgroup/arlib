/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The Robbins–Monro condition `∑ aₙ = ∞`, and the deterministic recursion under it

The **deterministic** half of stochastic approximation.  Nothing in this module
mentions a probability space: it is real analysis about a single nonnegative
sequence `a : ℕ → ℝ` of step sizes and the recursion it drives.

Two independent pieces:

## 1. What divergence buys you

* `tendsto_prod_one_sub_atTop_nhds_zero` — **the Robbins–Monro product lemma**:
  if `aₙ ∈ [0,1]` and `∑ aₙ = ∞` then `∏_{k<n} (1 − a_k) → 0`, via
  `1 − x ≤ exp (−x)`.  This is the mechanism by which a step-size schedule makes
  an iteration forget its initial condition, and it is the only place the
  divergence hypothesis is ever used.
* `detProc` — the deterministic auxiliary process `Y_{n+1} = (1 − aₙ)Yₙ + aₙ·c`,
  with `detProc_sub_const` (the closed form `Yₙ − c = (y₀ − c)∏(1 − a_k)`),
  `tendsto_detProc` (`Yₙ → c`), and the convexity bounds `le_detProc`,
  `detProc_le`.

## 2. How to establish divergence

Criteria for `∑_{t<n} α t → ∞` when the sequence is `0` almost everywhere and
only bounded below along a sparse set of "active" times — the situation in
asynchronous stochastic approximation, where a coordinate is updated only at the
times it is visited.

* `tendsto_sum_atTop_of_strictMono_harmonic_le` — a harmonic lower bound along a
  strictly monotone subsequence suffices; **no** hypothesis at all is placed on
  the sequence off that subsequence beyond nonnegativity.
* `tendsto_sum_atTop_of_count_harmonic_le` — the same, phrased by a *counter*:
  `p` holds infinitely often and `α t ≥ 1/(Nat.count p t + 1)` at every time `p`
  holds.  This is the form a visit-count-indexed schedule supplies directly.
* `setOf_infinite_of_forall_exists_le` — the bridge from "for every `N` there is
  a later active time" to `Set.Infinite`.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot

namespace Arlib.Probability.StochApprox

open scoped BigOperators Topology
open Filter Finset

/-! ## 1. The product lemma and the deterministic recursion -/

/-- **The Robbins–Monro product lemma.**  If `aₙ ∈ [0,1]` and `∑ aₙ = ∞` then
`∏_{k<n} (1 − a_k) → 0`.  This is what forces a process driven by the step
sizes `a` to forget its initial condition. -/
theorem tendsto_prod_one_sub_atTop_nhds_zero (a : ℕ → ℝ)
    (h01 : ∀ k, a k ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Tendsto (fun n => ∑ k ∈ range n, a k) atTop atTop) :
    Tendsto (fun n => ∏ k ∈ range n, (1 - a k)) atTop (𝓝 0) := by
  -- Lower bound: the product of nonnegative factors is nonnegative.
  have hnonneg : ∀ n, 0 ≤ ∏ k ∈ range n, (1 - a k) := by
    intro n
    refine Finset.prod_nonneg fun i _ => ?_
    have := (h01 i).2
    linarith
  -- Upper bound: `1 - x ≤ exp (-x)` factorwise, then collapse the product.
  have hle : ∀ n, (∏ k ∈ range n, (1 - a k)) ≤ Real.exp (-∑ k ∈ range n, a k) := by
    intro n
    have hstep : (∏ k ∈ range n, (1 - a k)) ≤ ∏ k ∈ range n, Real.exp (-(a k)) := by
      refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
      · have := (h01 i).2; linarith
      · have := Real.add_one_le_exp (-(a i)); linarith
    have hexp : (∏ k ∈ range n, Real.exp (-(a k))) = Real.exp (-∑ k ∈ range n, a k) := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_neg_distrib]
    rwa [hexp] at hstep
  -- The dominating sequence tends to `0`.
  have hexp0 : Tendsto (fun n => Real.exp (-∑ k ∈ range n, a k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum)
  exact squeeze_zero hnonneg hle hexp0

/-- **The deterministic auxiliary process** `Y_{n+1} = (1 − aₙ)Yₙ + aₙ·c`, with
`Y₀ = y₀`.  (`detProc a c y₀ n` is `Y_n`.) -/
noncomputable def detProc (a : ℕ → ℝ) (c y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | (n + 1) => (1 - a n) * detProc a c y₀ n + a n * c

@[simp] theorem detProc_zero (a : ℕ → ℝ) (c y₀ : ℝ) : detProc a c y₀ 0 = y₀ := rfl

@[simp] theorem detProc_succ (a : ℕ → ℝ) (c y₀ : ℝ) (n : ℕ) :
    detProc a c y₀ (n + 1) = (1 - a n) * detProc a c y₀ n + a n * c := rfl

/-- **The closed form of the offset**: `Yₙ − c = (y₀ − c)·∏_{k<n}(1 − a_k)`.
The offset `Zₙ := Yₙ − c` satisfies `Z_{n+1} = (1 − aₙ)Zₙ`, solved. -/
theorem detProc_sub_const (a : ℕ → ℝ) (c y₀ : ℝ) (n : ℕ) :
    detProc a c y₀ n - c = (y₀ - c) * ∏ k ∈ range n, (1 - a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [detProc_succ, Finset.prod_range_succ]
      have h : detProc a c y₀ n = c + (y₀ - c) * ∏ k ∈ range n, (1 - a k) := by linarith [ih]
      rw [h]; ring

/-- **`Yₙ → c`** — the deterministic process forgets its initial value. -/
theorem tendsto_detProc (a : ℕ → ℝ) (c y₀ : ℝ)
    (h01 : ∀ k, a k ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Tendsto (fun n => ∑ k ∈ range n, a k) atTop atTop) :
    Tendsto (detProc a c y₀) atTop (𝓝 c) := by
  have hfun : detProc a c y₀ = fun n => c + (y₀ - c) * ∏ k ∈ range n, (1 - a k) := by
    funext n
    have := detProc_sub_const a c y₀ n
    linarith
  have hprod := (tendsto_prod_one_sub_atTop_nhds_zero a h01 hsum).const_mul (y₀ - c)
  rw [mul_zero] at hprod
  have hlim := (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))).add hprod
  rw [hfun]
  simpa using hlim

/-- Both convexity bounds at once — the induction has to carry them together,
since each step is a convex combination of `Yₙ` and `c`. -/
theorem le_detProc_and_detProc_le (a : ℕ → ℝ) (c y₀ : ℝ)
    (h01 : ∀ k, a k ∈ Set.Icc (0 : ℝ) 1) (hcy : c ≤ y₀) (n : ℕ) :
    c ≤ detProc a c y₀ n ∧ detProc a c y₀ n ≤ y₀ := by
  induction n with
  | zero => exact ⟨hcy, le_rfl⟩
  | succ n ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      obtain ⟨ha0, ha1⟩ := h01 n
      rw [detProc_succ]
      constructor
      · nlinarith
      · nlinarith

/-- The process stays below its initial value: a convex combination never leaves
the interval. -/
theorem detProc_le (a : ℕ → ℝ) (c y₀ : ℝ) (h01 : ∀ k, a k ∈ Set.Icc (0 : ℝ) 1)
    (hcy : c ≤ y₀) (n : ℕ) : detProc a c y₀ n ≤ y₀ :=
  (le_detProc_and_detProc_le a c y₀ h01 hcy n).2

/-- The process stays above its target. -/
theorem le_detProc (a : ℕ → ℝ) (c y₀ : ℝ) (h01 : ∀ k, a k ∈ Set.Icc (0 : ℝ) 1)
    (hcy : c ≤ y₀) (n : ℕ) : c ≤ detProc a c y₀ n :=
  (le_detProc_and_detProc_le a c y₀ h01 hcy n).1

/-! ## 2. Criteria for `∑ α = ∞`

Nothing in this section mentions a probability space either.  The point of each
statement is that the sequence is constrained **only** along a sparse set of
times; off that set it may be `0`, which is the asynchronous case. -/

/-- **Divergence transfers along a strictly monotone subsequence.**

If `α ≥ 0` everywhere and `α (v k) ≥ 1/(k+1)` along a strictly monotone
`v : ℕ → ℕ`, then `∑_{t<n} α t → ∞`.

The proof is the sandwich
`∑_{i<m} 1/(i+1) ≤ ∑_{k<m} α (v k) = ∑_{t ∈ v''[0,m)} α t ≤ ∑_{t < v m} α t`:
the middle equality is `Finset.sum_image` at the injective `v`, the last
inequality is `Finset.sum_le_sum_of_subset_of_nonneg` at the inclusion
`v''[0,m) ⊆ [0, v m)` supplied by strict monotonicity, and the partial sums are
monotone because the terms are nonnegative, so unboundedness upgrades to
convergence to `atTop`.  Note that **no** lower bound whatsoever is assumed on
`α` off the range of `v`. -/
theorem tendsto_sum_atTop_of_strictMono_harmonic_le {α : ℕ → ℝ}
    (hα : ∀ t, 0 ≤ α t) {v : ℕ → ℕ} (hv : StrictMono v)
    (hle : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ α (v k)) :
    Tendsto (fun n => ∑ t ∈ Finset.range n, α t) atTop atTop := by
  have hmono : Monotone fun n => ∑ t ∈ Finset.range n, α t := by
    intro m n hmn
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.mpr hmn)
      fun i _ _ => hα i
  refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
  obtain ⟨m, hm⟩ :=
    (tendsto_atTop.mp Real.tendsto_sum_range_one_div_nat_succ_atTop b).exists
  refine ⟨v m, ?_⟩
  have hsub : (Finset.range m).image v ⊆ Finset.range (v m) := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_range] at ht ⊢
    obtain ⟨k, hk, rfl⟩ := ht
    exact hv hk
  calc b ≤ ∑ i ∈ Finset.range m, (1 / (i + 1) : ℝ) := hm
    _ ≤ ∑ k ∈ Finset.range m, α (v k) := Finset.sum_le_sum fun k _ => hle k
    _ = ∑ t ∈ (Finset.range m).image v, α t :=
        (Finset.sum_image fun x _ y _ h => hv.injective h).symm
    _ ≤ ∑ t ∈ Finset.range (v m), α t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hα i

/-- **The same, phrased by a counter rather than an enumeration.**

`p` holds at infinitely many times, and at every such time `t` the term `α t` is
at least `1/(N+1)` where `N = Nat.count p t` is the number of *earlier* times at
which `p` held.  Then `∑_{t<n} α t → ∞`.

This is the form an asynchronous schedule supplies: `p t` is "the coordinate is
the one updated at step `t`", `Nat.count p t` is its update counter, and the
bound is the harmonic schedule.  `Nat.nth p` is the strictly monotone enumeration
of `{t | p t}` (`Nat.nth_strictMono`), and `Nat.count_nth_of_infinite` says its
counter at the `k`-th occurrence is exactly `k`. -/
theorem tendsto_sum_atTop_of_count_harmonic_le {α : ℕ → ℝ} {p : ℕ → Prop}
    [DecidablePred p] (hα : ∀ t, 0 ≤ α t) (hp : {t | p t}.Infinite)
    (hle : ∀ t, p t → 1 / ((Nat.count p t : ℝ) + 1) ≤ α t) :
    Tendsto (fun n => ∑ t ∈ Finset.range n, α t) atTop atTop := by
  refine tendsto_sum_atTop_of_strictMono_harmonic_le hα (Nat.nth_strictMono hp) fun k : ℕ => ?_
  have h := hle _ (Nat.nth_mem_of_infinite hp k)
  rwa [Nat.count_nth_of_infinite hp k] at h

/-- **"Unbounded" is "infinitely often", for `ℕ`-indexed predicates.**  The
bridge for a caller who has the hypothesis in the form *"for every `N` there is a
later occurrence"* but needs `Set.Infinite`. -/
theorem setOf_infinite_of_forall_exists_le {p : ℕ → Prop} (h : ∀ N, ∃ t, N ≤ t ∧ p t) :
    {t | p t}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  obtain ⟨t, ht, hpt⟩ := h (B + 1)
  exact absurd (hB hpt) (by omega)

end Arlib.Probability.StochApprox
