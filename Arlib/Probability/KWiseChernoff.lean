/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Tactic.IntervalCases
import Arlib.Probability.StirlingMoment
import Arlib.Probability.MomentToTail

/-!
# The `k`-wise Chernoff bound for sums of `k`-wise independent indicators

Let `Z` be a `K`-wise independent family of `{0,1}`-indicators, `X = ∑_{i ∈ S} Zᵢ`
and `μ = Ex[X]`.  This file proves an **exponential** tail bound for `X` — the
Schmidt–Siegel–Srinivasan / Bellare–Rompel inequality — with explicit absolute
constants:

  `Pr[|X - μ| ≥ γ μ] ≤ exp(-γ² μ / 35)`   for `0 < γ ≤ 1`,  `100 ≤ γ² μ ≤ K`;
  `Pr[|X - μ| ≥ γ μ] ≤ exp(-γ μ / 35)`    for `1 ≤ γ`,      `100 ≤ γ μ ≤ K`.

The side conditions `k ≥ γ² μ` and `k ≥ γ μ` are those of the literature; the
constant in the exponent is `1/35` rather than the sharp `1/3`, and there is an
absolute threshold `100` on the budget.  See *What is proved, and what is not*
below.

## The route: a Poisson-shaped moment bound, proved by the moment recursion

The analytic half of the argument — turning a moment bound `Ex[(X-μ)^{2t}] ≤ K Bᵗ`
with `e B ≤ a²` into `Pr[|X - μ| ≥ a] ≤ K e^{-t}` — is
`Arlib.exp_tail_of_moment_le_pow` of `Arlib.Probability.MomentToTail`.  What this
file supplies is the **moment bound**.

The crux is `abs_Ex_centre_sum_pow_le_exp`: writing `Wᵢ = Zᵢ - Ex[Zᵢ]`,
`A = ∑_{i ∈ s} Wᵢ` and `V = varSum P Z s` for the total variance, for every
`x > 0` and every `n ≤ K`

  `|Ex[Aⁿ]| ≤ n! · exp(V · (e^x - 1 - x)) / xⁿ`.                            (★)

The right-hand side is exactly the Cauchy coefficient estimate
`n! [x^n] F ≤ n! F(x)/xⁿ` for `F(x) = exp(V (e^x - 1 - x))`, the exponential
generating function of the central moments of a `Poisson(V)` variable — which is
the correct comparison object, as the docstring of
`Arlib.Probability.StirlingMoment` explains.  **No generating function, and no
partition counting, occurs in the proof.**  (★) is proved by induction on the
index set `s`, simultaneously in all `n ≤ K`, straight from the moment recursion
`Ex_centre_sum_pow_insert` of `Arlib.Probability.EvenMoment`:

  `Ex[(A + W_a)ⁿ] = ∑_{j ≤ n} C(n,j) · Ex[W_aʲ] · Ex[A^{n-j}]`,

in which the `j = 1` term vanishes and every `j ≥ 2` term obeys the uniform
estimate `|Ex[W_aʲ]| ≤ Ex[W_a²] =: v`.  With `C(n,j)(n-j)! = n!/j!` this makes the
induction step

  `n!e^{Vφ}/xⁿ · (1 + v ∑_{j=2}^n xʲ/j!) ≤ n!e^{Vφ}/xⁿ · e^{vφ} = n!e^{(v+V)φ}/xⁿ`,

using only `∑_{j=2}^n xʲ/j! ≤ φ(x) := e^x - 1 - x` and `1 + y ≤ e^y`.  This
bypasses the plan sketched in `StirlingMoment.lean` — group the surviving tuples
by their image and count the set partitions with blocks of size `≥ 2` — entirely;
the associated Stirling numbers never appear, and neither does
`noSingletonTuples`.

Optimising `x` in (★) at `n = 2t` (`Ex_sum_sub_mean_pow_le_bellareRompel`) gives
the **Bellare–Rompel shape**

  `Ex[(X - μ)^{2t}] ≤ (e · (3 t μ + 4 t²))ᵗ`,                               (BR)

with `x² = min(1, 4t/(3μ))`, the crude factorial estimate `(2t)! ≤ (2t)^{2t}` and
`e^x - 1 - x ≤ (3/4)x²` on `[0,1]`.  This is the shape of Bellare–Rompel,
*Randomness-efficient oblivious sampling* (FOCS 1994) — their bound is
`8 (2tμ + 4t²)ᵗ`, and `e(3tμ + 4t²) ≤ (3e/2)(2tμ + 4t²)`, so (BR) is theirs with
the leading constant `8` traded for `(3e/2)ᵗ ≈ 4.08ᵗ`.  The same shape is proved
by an explicit partition count in the `uniqueskolem` development
(`UniqueSkolem.survivor_sum_le`, in a sibling repository not distributed with
this library); the proof here is independent of it and takes a different route.

Crucially, (BR) is **not** of the Stirling shape `K (2tμ/e)ᵗ` that the module
docstring of `Arlib.Probability.StirlingMoment` *refutes*: the additive `4t²` is
exactly what carries the regime `μ = O(t)` in which no constant `K` can work.
The refutation is therefore no obstruction here, and nothing below contradicts
it.

## Structure

* `sum_Ico_two_pow_div_factorial_le` — `∑_{j=2}^n xʲ/j! ≤ e^x - 1 - x`;
* `abs_Ex_centre_sum_pow_le_exp` — the crux (★), for the centred sum;
* `abs_Ex_sum_sub_mean_pow_le_exp` — (★) about `X - μ`, using `varSum ≤ μ`;
* `exp_sub_one_sub_le`, `factorial_two_mul_le_pow`, `exp_one_le` — the three
  elementary estimates the optimisation consumes;
* `Ex_sum_sub_mean_pow_le_bellareRompel` — (BR);
* `exp_tail_of_budget` — the tail bound in "deviation budget" form: `b ≥ 100`,
  `bμ ≤ a²`, `b² ≤ a²`, `b ≤ K` give `Pr[|X-μ| ≥ a] ≤ exp(-b/35)`, by taking
  `t = ⌈b/35⌉₊`;
* `exp_tail_relative`, `exp_tail_relative_ge_one` — the two `γ`-branches.

## What is proved, and what is not

**Proved, with these exact constants:** (★) for all `x > 0` and all `n ≤ K`; (BR)
with the base `e(3tμ + 4t²)` and multiplicative constant `1`; and the two tail
branches with exponent constant `1/35` and budget threshold `100`.

**Not proved:** the sharp Schmidt–Siegel–Srinivasan constant `1/3`.  Nothing
downstream needs it — the consumer of these bounds treats the per-region failure
probability as an abstract parameter — so no attempt was made to optimise.  For
the record, where the losses are:

* `(2t)! ≤ (2t)^{2t}` throws away a factor `e^{2t}`; Stirling's
  `(2t)! ≤ e√(2t)·(2t/e)^{2t}` would divide the base of the first regime by `e²`.
* `e^x - 1 - x ≤ (3/4)x²` (the `n = 2` Taylor remainder) is used where
  `(1/2)x² + (1/6)x³ + …` is true.

With both repaired, (★) yields base `≈ 1.1 t μ` and, after re-optimising the
choice of `t`, an exponent constant approaching `1/3`; the polynomial factor `√t`
coming from Stirling then has to be absorbed into the base, which is the only
genuinely fiddly step.  None of this is done here.

The tail bounds are stated for `X = ∑_{i ∈ S} Zᵢ` centred at its **own** mean
`Ex[X]`; a version centred at a nearby nominal mean would follow from
`exp_tail_of_moment_le_pow` in the same way, but is not stated.

No `sorry`; `#print axioms` on every theorem above reports exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## A truncated exponential estimate -/

/-- The tail `∑_{j=2}^{n} xʲ/j!` of the exponential series is at most
`e^x - 1 - x`, for `x ≥ 0`.  (Partial sums of a series with nonnegative terms.) -/
theorem sum_Ico_two_pow_div_factorial_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ j ∈ Finset.Ico 2 (n + 1), x ^ j / (j.factorial : ℝ) ≤ Real.exp x - 1 - x := by
  have hnn : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  rcases le_or_gt (n + 1) 2 with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    simpa using hnn
  · have hsplit : ∑ j ∈ Finset.Ico 0 2, x ^ j / (j.factorial : ℝ)
        + ∑ j ∈ Finset.Ico 2 (n + 1), x ^ j / (j.factorial : ℝ)
        = ∑ j ∈ Finset.Ico 0 (n + 1), x ^ j / (j.factorial : ℝ) :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    have h2 : ∑ j ∈ Finset.Ico 0 2, x ^ j / (j.factorial : ℝ) = 1 + x := by
      rw [← Finset.range_eq_Ico]
      simp [Finset.sum_range_succ]
    have hall : ∑ j ∈ Finset.Ico 0 (n + 1), x ^ j / (j.factorial : ℝ) ≤ Real.exp x := by
      rw [← Finset.range_eq_Ico]
      exact Real.sum_le_exp_of_nonneg hx (n + 1)
    linarith

section Crux

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The degenerate cases `n = 0` and `n = 1` of the moment bound, valid for every
index set: the zeroth moment is `1` and the first moment of a centred sum
vanishes. -/
theorem abs_Ex_centre_sum_pow_le_exp_of_lt_two (s : Finset ι) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n < 2) :
    |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ n)|
      ≤ (n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n := by
  have hphi : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  have hV0 : 0 ≤ varSum P Z s := varSum_nonneg P Z s
  have harg : 0 ≤ varSum P Z s * (Real.exp x - 1 - x) := mul_nonneg hV0 hphi
  interval_cases n
  · have h1 : (fun ω => (∑ i ∈ s, centre Z i ω) ^ 0) = fun _ : P.Ω => (1 : ℝ) := by
      funext ω; simp
    rw [h1, P.Ex_const]
    have := Real.one_le_exp harg
    simpa using this
  · have h1 : (fun ω => (∑ i ∈ s, centre Z i ω) ^ 1) = fun ω => ∑ i ∈ s, centre Z i ω := by
      funext ω; simp
    have h0 : P.Ex (fun ω => ∑ i ∈ s, centre Z i ω) = 0 := by
      rw [P.Ex_sum s (fun i ω => centre Z i ω)]
      exact Finset.sum_eq_zero fun i _ => Ex_centre Z i
    rw [h1, h0]
    have : (0:ℝ) < (Nat.factorial 1 : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x))
        / x ^ 1 := by positivity
    simpa using this.le

/-- **The crux: a Poisson-shaped bound on every central moment of a sum of
`k`-wise independent indicators.**  For every `x > 0` and every `n ≤ K`, writing
`Wᵢ = Zᵢ - Ex[Zᵢ]`, `A = ∑_{i ∈ s} Wᵢ` and `V = varSum P Z s`,

  `|Ex[Aⁿ]| ≤ n! · exp(V · (e^x - 1 - x)) / xⁿ`.

The right-hand side is the Cauchy coefficient bound for the exponential
generating function `exp(V (e^x - 1 - x))` of the central moments of a
`Poisson(V)` variable — but no generating function appears in the proof.

Induction on `s`, simultaneously in all `n ≤ K`.  The moment recursion
`Ex_centre_sum_pow_insert` gives, for a fresh index `a` with `v = Ex[W_a²]`,

  `Ex[(A + W_a)ⁿ] = ∑_{j ≤ n} C(n,j) · Ex[W_aʲ] · Ex[A^{n-j}]`,

in which the `j = 1` term vanishes (`Ex[W_a] = 0`) and every `j ≥ 2` term obeys
`|Ex[W_aʲ]| ≤ v` (`abs_Ex_centre_pow_le`).  Since `C(n,j)·(n-j)! = n!/j!`, the
whole sum is at most `n! e^{Vφ}/xⁿ · (1 + v ∑_{j=2}^n xʲ/j!)`, and
`∑_{j=2}^n xʲ/j! ≤ φ(x) = e^x - 1 - x` together with `1 + y ≤ e^y` upgrades the
bracket to `e^{vφ}`, which is exactly the passage from `V` to `v + V`. -/
theorem abs_Ex_centre_sum_pow_le_exp (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    {x : ℝ} (hx : 0 < x) (s : Finset ι) :
    ∀ n, n ≤ K → |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ n)|
      ≤ (n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n := by
  have hphi : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  induction s using Finset.induction_on with
  | empty =>
    intro n _
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · exact abs_Ex_centre_sum_pow_le_exp_of_lt_two _ hx hn2
    · have h1 : (fun ω => (∑ i ∈ (∅ : Finset ι), centre Z i ω) ^ n) = fun _ : P.Ω => (0 : ℝ) := by
        funext ω
        simp [Finset.sum_empty, zero_pow (by omega : n ≠ 0)]
      rw [h1, P.Ex_const, abs_zero]
      have : (0:ℝ) < (n.factorial : ℝ)
          * Real.exp (varSum P Z (∅ : Finset ι) * (Real.exp x - 1 - x)) / x ^ n := by
        have : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
        positivity
      exact this.le
  | @insert a s ha ih =>
    intro n hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · exact abs_Ex_centre_sum_pow_le_exp_of_lt_two _ hx hn2
    -- Abbreviations.
    have hV0 : 0 ≤ varSum P Z s := varSum_nonneg P Z s
    have hv0 : 0 ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) := Ex_centre_sq_nonneg Z a
    have hxn : (0:ℝ) < x ^ n := pow_pos hx n
    have hM0 : 0 ≤ (n.factorial : ℝ)
        * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n := by
      have : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
      positivity
    rw [varSum_insert P Z ha, Ex_centre_sum_pow_insert hind hZ ha hn]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    -- Split off the `j = 0` and `j = 1` terms.
    have hsplit : ∑ j ∈ Finset.range (n + 1),
          |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
            * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))|
        = |(n.choose 0 : ℝ) * (P.Ex (fun ω => centre Z a ω ^ 0)
              * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - 0)))|
          + |(n.choose 1 : ℝ) * (P.Ex (fun ω => centre Z a ω ^ 1)
              * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - 1)))|
          + ∑ j ∈ Finset.Ico 2 (n + 1),
              |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
                * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))| := by
      have hc := Finset.sum_Ico_consecutive
        (fun j => |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
          * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))|)
        (by omega : 0 ≤ 2) (by omega : 2 ≤ n + 1)
      rw [Finset.range_eq_Ico, ← hc]
      congr 1
      rw [← Finset.range_eq_Ico]
      simp [Finset.sum_range_succ]
    rw [hsplit]
    -- The `j = 0` term is `|Ex[Aⁿ]|`.
    have h0 : |(n.choose 0 : ℝ) * (P.Ex (fun ω => centre Z a ω ^ 0)
          * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - 0)))|
        ≤ (n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n := by
      have he : P.Ex (fun ω => centre Z a ω ^ 0) = 1 := by
        have : (fun ω => centre Z a ω ^ 0) = fun _ : P.Ω => (1:ℝ) := by funext ω; simp
        rw [this, P.Ex_const]
      simp only [Nat.choose_zero_right, Nat.cast_one, he, one_mul, Nat.sub_zero]
      exact ih n hn
    -- The `j = 1` term vanishes.
    have h1 : |(n.choose 1 : ℝ) * (P.Ex (fun ω => centre Z a ω ^ 1)
          * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - 1)))| = 0 := by
      have he : P.Ex (fun ω => centre Z a ω ^ 1) = 0 := by
        have h : (fun ω => centre Z a ω ^ 1) = centre Z a := funext fun ω => pow_one _
        rw [h]
        exact Ex_centre Z a
      rw [he, zero_mul, mul_zero, abs_zero]
    -- Every `j ≥ 2` term is at most `v · M · xʲ/j!`.
    have h2 : ∀ j ∈ Finset.Ico 2 (n + 1),
        |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
            * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))|
          ≤ P.Ex (fun ω => (centre Z a ω) ^ 2)
              * ((n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n)
              * (x ^ j / (j.factorial : ℝ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      obtain ⟨hj2, hjn⟩ := hj
      have hjle : j ≤ n := by omega
      have habs : |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
            * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))|
          = (n.choose j : ℝ) * (|P.Ex (fun ω => centre Z a ω ^ j)|
              * |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j))|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n.choose j : ℝ))]
      rw [habs]
      -- The two factors.
      have hA : |P.Ex (fun ω => centre Z a ω ^ j)| ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) :=
        abs_Ex_centre_pow_le hZ a hj2
      have hB : |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j))|
          ≤ ((n - j).factorial : ℝ)
              * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ (n - j) :=
        ih (n - j) (by omega)
      have hB0 : (0:ℝ) ≤ ((n - j).factorial : ℝ)
          * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ (n - j) := by
        have : (0:ℝ) ≤ ((n - j).factorial : ℝ) := by positivity
        positivity
      have hstep : (n.choose j : ℝ) * (|P.Ex (fun ω => centre Z a ω ^ j)|
              * |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j))|)
          ≤ (n.choose j : ℝ) * (P.Ex (fun ω => (centre Z a ω) ^ 2)
              * (((n - j).factorial : ℝ)
                  * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ (n - j))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hA hB (abs_nonneg _) hv0
      refine hstep.trans (le_of_eq ?_)
      -- `C(n,j)·(n-j)!·xʲ = n!/j!·xʲ` and `xⁿ = xʲ·x^{n-j}`.
      have hfac : (n.choose j : ℝ) * ((n - j).factorial : ℝ) * (j.factorial : ℝ)
          = (n.factorial : ℝ) := by
        have h := Nat.choose_mul_factorial_mul_factorial hjle
        have : ((n.choose j * j.factorial * (n - j).factorial : ℕ) : ℝ) = (n.factorial : ℝ) := by
          exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
        push_cast at this
        linarith [this]
      have hxsplit : x ^ n = x ^ j * x ^ (n - j) := by
        rw [← pow_add]
        congr 1
        omega
      have hjf : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
      have hxj : (0:ℝ) < x ^ j := pow_pos hx j
      have hxnj : (0:ℝ) < x ^ (n - j) := pow_pos hx (n - j)
      rw [hxsplit, ← hfac]
      field_simp
    -- Sum up.
    have hsum : ∑ j ∈ Finset.Ico 2 (n + 1),
          |(n.choose j : ℝ) * (P.Ex (fun ω => centre Z a ω ^ j)
            * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j)))|
        ≤ P.Ex (fun ω => (centre Z a ω) ^ 2)
            * ((n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n)
            * (Real.exp x - 1 - x) := by
      refine (Finset.sum_le_sum h2).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (sum_Ico_two_pow_div_factorial_le hx.le n) ?_
      positivity
    -- Combine: `M (1 + v φ) ≤ M e^{v φ}`.
    have hfin : (n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n
          + 0
          + P.Ex (fun ω => (centre Z a ω) ^ 2)
            * ((n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n)
            * (Real.exp x - 1 - x)
        ≤ (n.factorial : ℝ)
            * Real.exp ((P.Ex (fun ω => (centre Z a ω) ^ 2) + varSum P Z s)
                * (Real.exp x - 1 - x)) / x ^ n := by
      have hexp : Real.exp ((P.Ex (fun ω => (centre Z a ω) ^ 2) + varSum P Z s)
              * (Real.exp x - 1 - x))
          = Real.exp (P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x))
            * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) := by
        rw [← Real.exp_add]; ring_nf
      have hone : 1 + P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x)
          ≤ Real.exp (P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x)) := by
        linarith [Real.add_one_le_exp
          (P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x))]
      rw [hexp]
      have hkey := mul_le_mul_of_nonneg_right hone hM0
      calc (n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n
            + 0
            + P.Ex (fun ω => (centre Z a ω) ^ 2)
              * ((n.factorial : ℝ) * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n)
              * (Real.exp x - 1 - x)
          = (1 + P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x))
              * ((n.factorial : ℝ)
                  * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n) := by ring
        _ ≤ Real.exp (P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x))
              * ((n.factorial : ℝ)
                  * Real.exp (varSum P Z s * (Real.exp x - 1 - x)) / x ^ n) := hkey
        _ = (n.factorial : ℝ)
              * (Real.exp (P.Ex (fun ω => (centre Z a ω) ^ 2) * (Real.exp x - 1 - x))
                  * Real.exp (varSum P Z s * (Real.exp x - 1 - x))) / x ^ n := by ring
    rw [h1]
    linarith [h0, hsum, hfin]

/-- **The crux, stated about the mean.**  For `X = ∑_{i ∈ s} Zᵢ` and `μ = Ex[X]`,

  `|Ex[(X - μ)ⁿ]| ≤ n! · exp(μ · (e^x - 1 - x)) / xⁿ`   (`n ≤ K`, `x > 0`).

This is `abs_Ex_centre_sum_pow_le_exp` after centring (`X - μ = ∑ᵢ Wᵢ`) and after
replacing the total variance `V` by the mean, using `varSum_le_mean` (`V ≤ μ`)
and the monotonicity of `exp` — legitimate because `e^x - 1 - x ≥ 0`. -/
theorem abs_Ex_sum_sub_mean_pow_le_exp (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≤ K) :
    |P.Ex (fun ω => ((∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ n)|
      ≤ (n.factorial : ℝ)
          * Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp x - 1 - x)) / x ^ n := by
  have hphi : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  have hmu : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') = ∑ i ∈ s, P.Ex (Z i) := P.Ex_sum s Z
  have hpt : (fun ω => ((∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ n)
      = fun ω => (∑ i ∈ s, centre Z i ω) ^ n := by
    funext ω
    congr 1
    rw [hmu, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hpt]
  refine (abs_Ex_centre_sum_pow_le_exp hind hZ hx s n hn).trans ?_
  have hmono : Real.exp (varSum P Z s * (Real.exp x - 1 - x))
      ≤ Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp x - 1 - x)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (varSum_le_mean hZ s) hphi)
  have hfac : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
  have hxn : (0:ℝ) < x ^ n := pow_pos hx n
  gcongr

end Crux

/-! ## Two elementary estimates -/

/-- `e^x - 1 - x ≤ (3/4) x²` on `[0, 1]`: the quadratic Taylor remainder of the
exponential, from `Real.exp_bound` at `n = 2`. -/
theorem exp_sub_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ 3 / 4 * x ^ 2 := by
  have habs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.exp_bound habs (n := 2) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℝ) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hsum, abs_of_nonneg hx0] at h
  have h2 : |Real.exp x - (1 + x)| ≤ x ^ 2 * (3 / 4) := by
    refine h.trans (le_of_eq ?_)
    norm_num
  have := (abs_le.mp h2).2
  linarith

/-- The crude factorial bound `(2t)! ≤ (4t²)^t`, i.e. `n! ≤ nⁿ` at `n = 2t`.
Sharpening this to Stirling's `(2t/e)^{2t}` would improve every constant below by
a factor `e²` per unit of `t`, but nothing downstream needs it. -/
theorem factorial_two_mul_le_pow (t : ℕ) :
    (((2 * t).factorial : ℕ) : ℝ) ≤ (4 * (t : ℝ) ^ 2) ^ t := by
  have h : ((2 * t).factorial : ℕ) ≤ (2 * t) ^ (2 * t) := Nat.factorial_le_pow (2 * t)
  have h' : (((2 * t).factorial : ℕ) : ℝ) ≤ (((2 * t) ^ (2 * t) : ℕ) : ℝ) := by
    exact_mod_cast h
  refine h'.trans (le_of_eq ?_)
  push_cast
  rw [pow_mul]
  congr 1
  ring

section BellareRompel

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **The Bellare–Rompel-shaped central moment bound.**  For a `2t`-wise
independent family of `{0,1}`-indicators, `X = ∑_{i ∈ s} Zᵢ` and `μ = Ex[X]`,

  `Ex[(X - μ)^{2t}] ≤ (e · (3 t μ + 4 t²))^t`.

This is the shape of Bellare–Rompel (*Randomness-efficient oblivious sampling*,
FOCS 1994), `Ex[(X-μ)^{2t}] ≤ 8 (2tμ + 4t²)^t`, with a different absolute
constant: `e (3tμ + 4t²) ≤ (3e/2) (2tμ + 4t²)`, so the bound proved here is the
Bellare–Rompel one with the constant `8` replaced by `(3e/2)^t`.  It is **not**
of the refuted Stirling shape `K (2tμ/e)^t` of `Arlib.Probability.StirlingMoment`
— the additive `4t²` is exactly what makes it true in the regime `μ = O(t)` where
that shape fails.

Proof: apply `abs_Ex_sum_sub_mean_pow_le_exp` at `n = 2t` and optimise `x`.  With
`(2t)! ≤ (4t²)^t` and `e^x - 1 - x ≤ (3/4)x²` on `[0,1]`, the bound reads
`(4t²)^t exp((3/4)μx²) / (x²)^t`, which is minimised at `x² = 4t/(3μ)`:

* if `4t ≤ 3μ` that value of `x` is admissible (`x ≤ 1`) and gives `(3 e t μ)^t`;
* otherwise `x = 1` gives `(4 e t²)^t`, because then `(3/4)μ ≤ t`.

Both are at most `(e (3tμ + 4t²))^t`. -/
theorem Ex_sum_sub_mean_pow_le_bellareRompel (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) {t : ℕ} (ht : 0 < t) (h2t : 2 * t ≤ K) :
    P.Ex (fun ω => ((∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ (2 * t))
      ≤ (Real.exp 1 * (3 * (t : ℝ) * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
          + 4 * (t : ℝ) ^ 2)) ^ t := by
  have hmu0 : 0 ≤ P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := by
    rw [P.Ex_sum s Z]
    exact Finset.sum_nonneg fun i _ => Ex_indicator_nonneg hZ i
  have ht0 : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hfact := factorial_two_mul_le_pow t
  have hexp1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  -- The bound is monotone in the base, so it suffices to reach `(e (3tμ))^t` or `(4et²)^t`.
  have hmono : ∀ B : ℝ, 0 ≤ B → B ≤ Real.exp 1 * (3 * (t : ℝ)
        * P.Ex (fun ω' => ∑ i ∈ s, Z i ω') + 4 * (t : ℝ) ^ 2) →
      B ^ t ≤ (Real.exp 1 * (3 * (t : ℝ) * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
        + 4 * (t : ℝ) ^ 2)) ^ t := fun B hB0 hB => pow_le_pow_left₀ hB0 hB t
  -- Remove the absolute value: an even power has nonnegative expectation.
  have hnn : P.Ex (fun ω => ((∑ i ∈ s, Z i ω)
        - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ (2 * t))
      ≤ |P.Ex (fun ω => ((∑ i ∈ s, Z i ω)
        - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ (2 * t))| := le_abs_self _
  refine hnn.trans ?_
  rcases le_or_gt (4 * (t:ℝ)) (3 * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) with hcase | hcase
  · -- Regime `4t ≤ 3μ`: the optimal `x = √(4t/(3μ))` is at most `1`.
    have hmupos : (0:ℝ) < P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := by linarith
    have hq0 : (0:ℝ) < 4 * (t:ℝ) / (3 * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) := by positivity
    have hq1 : 4 * (t:ℝ) / (3 * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ≤ 1 :=
      (div_le_one (by linarith)).mpr hcase
    set q := 4 * (t:ℝ) / (3 * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) with hqdef
    have hx : (0:ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq0
    have hxsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have hxle : Real.sqrt q ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hq1
    have hbound := abs_Ex_sum_sub_mean_pow_le_exp hind hZ s hx (n := 2 * t) h2t
    refine hbound.trans ?_
    -- `μ φ(x) ≤ t`.
    have hphi : Real.exp (Real.sqrt q) - 1 - Real.sqrt q ≤ 3 / 4 * q := by
      have := exp_sub_one_sub_le hx.le hxle
      rwa [hxsq] at this
    have hmuphi : P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
        * (Real.exp (Real.sqrt q) - 1 - Real.sqrt q) ≤ (t : ℝ) := by
      refine (mul_le_mul_of_nonneg_left hphi hmu0).trans (le_of_eq ?_)
      rw [hqdef]
      field_simp
    have hexple : Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
          * (Real.exp (Real.sqrt q) - 1 - Real.sqrt q))
        ≤ Real.exp 1 ^ t := by
      refine (Real.exp_le_exp.mpr hmuphi).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hxpow : Real.sqrt q ^ (2 * t) = q ^ t := by rw [pow_mul, hxsq]
    have hqpow : (0:ℝ) < q ^ t := pow_pos hq0 t
    have hstep : (((2 * t).factorial : ℕ) : ℝ)
          * Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
              * (Real.exp (Real.sqrt q) - 1 - Real.sqrt q)) / Real.sqrt q ^ (2 * t)
        ≤ (4 * (t:ℝ) ^ 2) ^ t * Real.exp 1 ^ t / q ^ t := by
      rw [hxpow]
      have hfac0 : (0:ℝ) ≤ (((2 * t).factorial : ℕ) : ℝ) := by positivity
      gcongr
    refine hstep.trans ?_
    -- `(4t²)^t e^t / q^t = (3 e t μ)^t`
    have heq : (4 * (t:ℝ) ^ 2) ^ t * Real.exp 1 ^ t / q ^ t
        = (Real.exp 1 * (3 * (t:ℝ) * P.Ex (fun ω' => ∑ i ∈ s, Z i ω'))) ^ t := by
      rw [← mul_pow, ← div_pow]
      congr 1
      rw [hqdef]
      field_simp
    rw [heq]
    refine hmono _ (by positivity) (mul_le_mul_of_nonneg_left ?_ hexp1.le)
    linarith [sq_nonneg ((t : ℝ))]
  · -- Regime `3μ < 4t`: take `x = 1`.
    have hbound := abs_Ex_sum_sub_mean_pow_le_exp hind hZ s
      (x := 1) one_pos (n := 2 * t) h2t
    refine hbound.trans ?_
    have hphi : Real.exp 1 - 1 - 1 ≤ 3 / 4 := by
      have := exp_sub_one_sub_le (by norm_num : (0:ℝ) ≤ 1) le_rfl
      norm_num at this
      linarith
    have hmuphi : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp 1 - 1 - 1) ≤ (t : ℝ) := by
      have h1 : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp 1 - 1 - 1)
          ≤ P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (3 / 4) :=
        mul_le_mul_of_nonneg_left hphi hmu0
      linarith
    have hexple : Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp 1 - 1 - 1))
        ≤ Real.exp 1 ^ t := by
      refine (Real.exp_le_exp.mpr hmuphi).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hstep : (((2 * t).factorial : ℕ) : ℝ)
          * Real.exp (P.Ex (fun ω' => ∑ i ∈ s, Z i ω') * (Real.exp 1 - 1 - 1)) / (1:ℝ) ^ (2 * t)
        ≤ (4 * (t:ℝ) ^ 2) ^ t * Real.exp 1 ^ t := by
      rw [one_pow, div_one]
      have hfac0 : (0:ℝ) ≤ (((2 * t).factorial : ℕ) : ℝ) := by positivity
      gcongr
    refine hstep.trans ?_
    have hrw : (4 * (t:ℝ) ^ 2) ^ t * Real.exp 1 ^ t = (Real.exp 1 * (4 * (t:ℝ) ^ 2)) ^ t := by
      rw [← mul_pow]
      congr 1
      ring
    rw [hrw]
    refine hmono _ (by positivity) (mul_le_mul_of_nonneg_left ?_ hexp1.le)
    have : (0:ℝ) ≤ 3 * (t:ℝ) * P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := by positivity
    linarith

end BellareRompel

/-! ## The exponential tail -/

/-- `e ≤ 68/25 = 2.72`, from `Real.exp_bound` at `x = 1`, `n = 4`
(`e ≤ 1 + 1 + 1/2 + 1/6 + 5/96 = 2.71875`). -/
theorem exp_one_le : Real.exp 1 ≤ 68 / 25 := by
  have h := Real.exp_bound (x := 1) (by norm_num) (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, (1:ℝ) ^ m / (m.factorial : ℝ) = 8 / 3 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have h2 := (abs_le.mp h).2
  norm_num [Nat.factorial] at h2
  linarith

/-- The purely numerical side condition of the optimisation: if `t ≤ (27/700) b`,
`μ ≥ 0`, `b μ ≤ a²` and `b² ≤ a²`, then the Bellare–Rompel base
`B = e (3tμ + 4t²)` satisfies `e B ≤ a²`.

Indeed `3tμ ≤ (81/700) bμ ≤ (81/700) a²` and `4t² ≤ (2916/490000) b² ≤
(2916/490000) a²`, while `e² ≤ 4624/625 = 7.3984`; and
`7.3984 · (81/700 + 2916/490000) = 0.9002… < 1`. -/
private theorem exp_sq_mul_base_le {t μ a b : ℝ} (htnn : 0 ≤ t) (ht : t ≤ 27 / 700 * b)
    (hmu0 : 0 ≤ μ) (hbmu : b * μ ≤ a ^ 2) (hb2 : b ^ 2 ≤ a ^ 2) :
    (Real.exp 1 * (3 * t * μ + 4 * t ^ 2)) * Real.exp 1 ≤ a ^ 2 := by
  have he : Real.exp 1 ≤ 68 / 25 := exp_one_le
  have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 1 * Real.exp 1 ≤ 4624 / 625 := by nlinarith
  have hA : 3 * t * μ ≤ 81 / 700 * a ^ 2 := by nlinarith
  have hB : 4 * t ^ 2 ≤ 2916 / 490000 * a ^ 2 := by nlinarith
  have hs0 : (0:ℝ) ≤ 3 * t * μ + 4 * t ^ 2 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) htnn) hmu0) (by positivity)
  have hstep : Real.exp 1 * Real.exp 1 * (3 * t * μ + 4 * t ^ 2)
      ≤ (4624 / 625) * ((81 / 700 + 2916 / 490000) * a ^ 2) :=
    mul_le_mul he2 (by linarith) hs0 (by norm_num)
  nlinarith [hstep, sq_nonneg a]

section Tail

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **The `k`-wise Chernoff bound, budget form.**  Let `X = ∑_{i ∈ S} Zᵢ` be a sum
of `K`-wise independent `{0,1}`-indicators with mean `μ`, let `a > 0` be a
deviation and let `b` be a *budget* with

  `b ≥ 100`,  `b μ ≤ a²`,  `b² ≤ a²`,  `b ≤ K`.

Then `Pr[|X - μ| ≥ a] ≤ exp(-b/35)`.

The proof takes `t = ⌈b/35⌉₊` in `Ex_sum_sub_mean_pow_le_bellareRompel` and feeds
the resulting moment bound to `Arlib.exp_tail_of_moment_le_pow` with `K = 1` and
`B = e (3tμ + 4t²)`.  The side condition `e B ≤ a²` becomes
`e² (3tμ + 4t²) ≤ a²`, and `b ≥ 100` gives `t ≤ b/35 + 1 ≤ (27/700) b`, whence
`3tμ ≤ (81/700) bμ ≤ (81/700) a²` and `4t² ≤ (2916/490000) b² ≤ (2916/490000) a²`;
since `e² ≤ 7.3984` and `7.3984 · (81/700 + 2916/490000) < 0.91`, the condition
holds with room to spare.

The constant `1/35` is not optimal — see the module docstring — but it is an
absolute constant, which is all the exponential tail is used for. -/
theorem exp_tail_of_budget (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    (S : Finset ι) {a b : ℝ} (ha : 0 < a) (hb : 100 ≤ b)
    (hbmu : b * P.Ex (fun ω' => ∑ i ∈ S, Z i ω') ≤ a ^ 2) (hb2 : b ^ 2 ≤ a ^ 2)
    (hK : b ≤ (K : ℝ)) :
    P.Pr (Finset.univ.filter fun ω =>
        a ≤ |(∑ i ∈ S, Z i ω) - P.Ex (fun ω' => ∑ i ∈ S, Z i ω')|)
      ≤ Real.exp (-b / 35) := by
  have hmu0 : 0 ≤ P.Ex (fun ω' => ∑ i ∈ S, Z i ω') := by
    rw [P.Ex_sum S Z]
    exact Finset.sum_nonneg fun i _ => Ex_indicator_nonneg hZ i
  have hb0 : (0:ℝ) < b := by linarith
  -- The choice of `t`.
  have hbpos : (0:ℝ) < b / 35 := by positivity
  have ht1 : b / 35 ≤ (⌈b / 35⌉₊ : ℝ) := Nat.le_ceil _
  have ht2 : ((⌈b / 35⌉₊ : ℕ) : ℝ) ≤ b / 35 + 1 := (Nat.ceil_lt_add_one hbpos.le).le
  have ht0 : 0 < ⌈b / 35⌉₊ := Nat.ceil_pos.mpr hbpos
  set t := ⌈b / 35⌉₊ with htdef
  have ht27 : (t : ℝ) ≤ 27 / 700 * b := by linarith
  have htnn : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  -- `2t ≤ K`.
  have h2tK : 2 * t ≤ K := by
    have hcast : ((2 * t : ℕ) : ℝ) ≤ (K : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  -- The side condition `e·B ≤ a²`, purely numerical.
  have hB0 : (0:ℝ) ≤ Real.exp 1
      * (3 * (t:ℝ) * P.Ex (fun ω' => ∑ i ∈ S, Z i ω') + 4 * (t:ℝ) ^ 2) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) htnn) hmu0) (by positivity))
  have hfin := exp_sq_mul_base_le (μ := P.Ex (fun ω' => ∑ i ∈ S, Z i ω'))
    htnn ht27 hmu0 hbmu hb2
  have hexpo : -(t : ℝ) ≤ -b / 35 := by linarith
  have hmom := Ex_sum_sub_mean_pow_le_bellareRompel hind hZ S ht0 h2tK
  have hmain := exp_tail_of_moment_le_pow (P := P) (fun ω => ∑ i ∈ S, Z i ω)
    (μ := P.Ex (fun ω' => ∑ i ∈ S, Z i ω')) t ha zero_le_one hB0 hfin
    (by rw [one_mul]; exact hmom)
  rw [one_mul] at hmain
  exact hmain.trans (Real.exp_le_exp.mpr hexpo)

/-- **The `k`-wise Chernoff bound, relative deviation `γ ≤ 1`.**  For a sum
`X = ∑_{i ∈ S} Zᵢ` of `K`-wise independent `{0,1}`-indicators with mean `μ`, and
`0 < γ ≤ 1` with `γ² μ ≥ 100` and `γ² μ ≤ K`,

  `Pr[|X - μ| ≥ γ μ] ≤ exp(-γ² μ / 35)`.

This is the first branch of the Schmidt–Siegel–Srinivasan / Bellare–Rompel
`k`-wise tail inequality, with the exponent constant `1/35` in place of the sharp
`1/3`; the side condition `k ≥ γ² μ` is the one in the literature.  It is
`exp_tail_of_budget` at `a = γ μ`, `b = γ² μ`: then `b μ = a²` exactly and
`b² = γ⁴ μ² ≤ γ² μ² = a²` because `γ ≤ 1`. -/
theorem exp_tail_relative (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    (S : Finset ι) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hbig : 100 ≤ γ ^ 2 * P.Ex (fun ω' => ∑ i ∈ S, Z i ω'))
    (hK : γ ^ 2 * P.Ex (fun ω' => ∑ i ∈ S, Z i ω') ≤ (K : ℝ)) :
    P.Pr (Finset.univ.filter fun ω =>
        γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')
          ≤ |(∑ i ∈ S, Z i ω) - P.Ex (fun ω' => ∑ i ∈ S, Z i ω')|)
      ≤ Real.exp (-(γ ^ 2 * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')) / 35) := by
  have hmu0 : (0:ℝ) < P.Ex (fun ω' => ∑ i ∈ S, Z i ω') := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg γ]
  refine exp_tail_of_budget hind hZ S (mul_pos hγ0 hmu0) hbig (le_of_eq (by ring)) ?_ hK
  have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
  have heq : (γ ^ 2 * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')) ^ 2
      = γ ^ 2 * (γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')) ^ 2 := by ring
  rw [heq]
  nlinarith [sq_nonneg (γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω'))]

/-- **The `k`-wise Chernoff bound, relative deviation `γ ≥ 1`.**  For a sum
`X = ∑_{i ∈ S} Zᵢ` of `K`-wise independent `{0,1}`-indicators with mean `μ`, and
`γ ≥ 1` with `γ μ ≥ 100` and `γ μ ≤ K`,

  `Pr[|X - μ| ≥ γ μ] ≤ exp(-γ μ / 35)`.

This is the second branch of the Schmidt–Siegel–Srinivasan / Bellare–Rompel
inequality, again with `1/35` in place of `1/3`; the side condition `k ≥ γ μ` is
the one in the literature.  It is `exp_tail_of_budget` at `a = γ μ`, `b = γ μ`:
then `b² = a²` and `b μ = γ μ² ≤ γ² μ² = a²` because `γ ≥ 1`. -/
theorem exp_tail_relative_ge_one (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    (S : Finset ι) {γ : ℝ} (hγ : 1 ≤ γ)
    (hbig : 100 ≤ γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω'))
    (hK : γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω') ≤ (K : ℝ)) :
    P.Pr (Finset.univ.filter fun ω =>
        γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')
          ≤ |(∑ i ∈ S, Z i ω) - P.Ex (fun ω' => ∑ i ∈ S, Z i ω')|)
      ≤ Real.exp (-(γ * P.Ex (fun ω' => ∑ i ∈ S, Z i ω')) / 35) := by
  have hγ0 : (0:ℝ) < γ := lt_of_lt_of_le zero_lt_one hγ
  have hmu0 : (0:ℝ) < P.Ex (fun ω' => ∑ i ∈ S, Z i ω') := by
    by_contra h
    push Not at h
    nlinarith
  refine exp_tail_of_budget hind hZ S (mul_pos hγ0 hmu0) hbig ?_ (le_of_eq (by ring)) hK
  nlinarith [hmu0, hγ]

end Tail

end Arlib.Probability


