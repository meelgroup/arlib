/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The discrete Poisson distribution: mass function, mgf, Chernoff tails

A self-contained, elementary toolkit for the Poisson distribution on `ℕ`, working
directly with the real-valued mass function

  `poissonPMF μ k = e^{-μ} μ^k / k!`

and ordinary `tsum`s over `ℕ`.  No measure theory is used anywhere: every
statement is an inequality between explicit series, which is exactly the shape in
which Poisson estimates are consumed by randomized-algorithm analyses.

## Main results

* `hasSum_poissonPMF`, `tsum_poissonPMF` — the mass function sums to `1`.
* `hasSum_poissonPMF_mul_exp`, `tsum_poissonPMF_mul_exp` — the **moment generating
  function** `∑ₖ pₖ e^{tk} = e^{μ(e^t - 1)}`, valid for every real `t`.
* `tsum_poissonPMF_mul_id` — the mean, `∑ₖ pₖ k = μ`.
* `tsum_ite_poissonPMF_le` — the generic **Chernoff step**: for any exponential
  tilt `s` and any predicate contained in the half-line `{k : c ≤ s k}`,
  `∑ₖ 1{P k} pₖ ≤ e^{-c} e^{μ(e^s - 1)}`.
* `poisson_tail_upper`, `poisson_tail_lower` — the two **Poisson tail bounds** of
  Banks–Garrabrant–Huber–Perizzolo, *Using TPA to count linear extensions*,
  Lemma 2: for `0 < a ≤ μ`,
  `Pr[X ≥ μ + a] ≤ exp(-a²/(2μ) + a³/(2μ²))` and `Pr[X ≤ μ - a] ≤ exp(-a²/(2μ))`.
* `tsum_poissonPMF_mul_sqrt_le` — Jensen for the square root (their Lemma 3),
  `∑ₖ pₖ √k ≤ √μ`.
* `poissonPMF_conv` — the convolution identity `Poisson μ ⋆ Poisson ν = Poisson (μ+ν)`.

## A correction to the source

The published proof of the *lower* tail in Lemma 2 of Banks–Garrabrant–Huber–
Perizzolo rests on the claim `-log(1-x) ≤ x + x²/2` for `x ∈ (0,1]`.  That claim
is **false for every `x > 0`**, since `-log(1-x) = x + x²/2 + x³/3 + ⋯`.  The
conclusion is nevertheless correct.  We replace the faulty step by the true
inequality `neg_add_sq_div_two_le_one_sub_mul_log` below,

  `(1-x) log(1-x) ≥ -x + x²/2`   for `x ∈ [0,1)`,

which yields the stated bound directly.  (The `x = 1` boundary, where Lean's
`log 0 = 0` makes the Chernoff step degenerate, is handled separately: there the
left tail is the single atom `p₀ = e^{-μ} ≤ e^{-μ/2}`.)

No `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

namespace Arlib

open scoped Nat

/-- The Poisson mass function with rate `mu`, as a real-valued function on `ℕ`:
`poissonPMF mu k = e^{-mu} · mu^k / k!`.

We keep `mu : ℝ` unconstrained (rather than `ℝ≥0`) so that the definition unfolds
without coercions; every lemma that needs it assumes `0 ≤ mu` explicitly. -/
noncomputable def poissonPMF (mu : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-mu) * mu ^ k / (Nat.factorial k)

/-! ## Tier 1: the mass function is a probability distribution -/

/-- The Poisson mass function is nonnegative for a nonnegative rate. -/
theorem poissonPMF_nonneg {mu : ℝ} (hmu : 0 ≤ mu) (k : ℕ) : 0 ≤ poissonPMF mu k := by
  unfold poissonPMF
  positivity

/-- The real exponential series, in the `HasSum` form used throughout this file:
`∑ₖ x^k / k! = e^x`.  This is `NormedSpace.expSeries_div_hasSum_exp` transported
along `Real.exp_eq_exp_ℝ`. -/
theorem hasSum_exp_series (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ x

/-- The Poisson mass function sums to `1`. -/
theorem hasSum_poissonPMF (mu : ℝ) : HasSum (poissonPMF mu) 1 := by
  have h := (hasSum_exp_series mu).mul_left (Real.exp (-mu))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun ?_
  intro k
  simp [poissonPMF, mul_div_assoc]

/-- The Poisson mass function is summable. -/
theorem summable_poissonPMF (mu : ℝ) : Summable (poissonPMF mu) :=
  (hasSum_poissonPMF mu).summable

/-- The Poisson mass function is a probability distribution: `∑ₖ pₖ = 1`. -/
theorem tsum_poissonPMF (mu : ℝ) : ∑' k : ℕ, poissonPMF mu k = 1 :=
  (hasSum_poissonPMF mu).tsum_eq

/-! ## Tier 2: the moment generating function -/

/-- The **moment generating function** of the Poisson distribution, in `HasSum`
form: `∑ₖ pₖ e^{t k} = e^{μ (e^t - 1)}`.

The proof is the observation that `pₖ e^{tk} = e^{-μ} (μ e^t)^k / k!`, so the
series is again the exponential series, evaluated at `μ e^t`. -/
theorem hasSum_poissonPMF_mul_exp (mu t : ℝ) :
    HasSum (fun k : ℕ => poissonPMF mu k * Real.exp (t * k))
      (Real.exp (mu * (Real.exp t - 1))) := by
  have h := (hasSum_exp_series (mu * Real.exp t)).mul_left (Real.exp (-mu))
  rw [← Real.exp_add] at h
  have hval : -mu + mu * Real.exp t = mu * (Real.exp t - 1) := by ring
  rw [hval] at h
  refine h.congr_fun ?_
  intro k
  rw [poissonPMF, mul_pow, mul_comm t (k : ℝ), Real.exp_nat_mul]
  field_simp
  ring

/-- The moment generating function of the Poisson distribution:
`∑ₖ pₖ e^{t k} = e^{μ (e^t - 1)}` for every real `t`. -/
theorem tsum_poissonPMF_mul_exp (mu t : ℝ) :
    ∑' k : ℕ, poissonPMF mu k * Real.exp (t * k) = Real.exp (mu * (Real.exp t - 1)) :=
  (hasSum_poissonPMF_mul_exp mu t).tsum_eq

/-- The recurrence `(k+1) · p_{k+1} = μ · p_k` behind the mean computation. -/
theorem succ_mul_poissonPMF_succ (mu : ℝ) (k : ℕ) :
    poissonPMF mu (k + 1) * ((k : ℝ) + 1) = mu * poissonPMF mu k := by
  have hk : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [poissonPMF, poissonPMF, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The **mean** of the Poisson distribution, in `HasSum` form: `∑ₖ pₖ · k = μ`.
No sign hypothesis on `μ` is needed. -/
theorem hasSum_poissonPMF_mul_id (mu : ℝ) :
    HasSum (fun k : ℕ => poissonPMF mu k * (k : ℝ)) mu := by
  have h : HasSum (fun k : ℕ => poissonPMF mu (k + 1) * ((k + 1 : ℕ) : ℝ)) mu := by
    have hm := (hasSum_poissonPMF mu).mul_left mu
    rw [mul_one] at hm
    refine hm.congr_fun ?_
    intro k
    push_cast
    rw [succ_mul_poissonPMF_succ]
  have h' := (hasSum_nat_add_iff (f := fun k : ℕ => poissonPMF mu k * (k : ℝ)) 1).mp h
  simpa using h'

/-- The **mean** of the Poisson distribution: `∑ₖ pₖ · k = μ`.  No sign hypothesis
on `μ` is needed. -/
theorem tsum_poissonPMF_mul_id (mu : ℝ) : ∑' k : ℕ, poissonPMF mu k * (k : ℝ) = mu :=
  (hasSum_poissonPMF_mul_id mu).tsum_eq

/-- `k ↦ pₖ · k` is summable. -/
theorem summable_poissonPMF_mul_id (mu : ℝ) :
    Summable (fun k : ℕ => poissonPMF mu k * (k : ℝ)) :=
  (hasSum_poissonPMF_mul_id mu).summable

/-! ## Tier 3: the Chernoff step, and the two Poisson tail bounds -/

/-- The generic **Chernoff / exponential Markov step** for the Poisson
distribution.

If a predicate `P` on `ℕ` is contained in the half-line `{k | c ≤ s·k}` for some
exponential tilt `s`, then the mass `P` carries is at most `e^{-c}` times the
moment generating function at `s`:
`∑ₖ 1{P k} pₖ ≤ e^{-c} · e^{μ(e^s - 1)}`.

Taking `s > 0` (so that `c ≤ s k` says `k` is large) gives upper tails; taking
`s < 0` gives lower tails.  Both tails below are instances of this lemma. -/
theorem tsum_ite_poissonPMF_le {mu : ℝ} (hmu : 0 ≤ mu) (s c : ℝ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ k, P k → c ≤ s * k) :
    ∑' k : ℕ, (if P k then poissonPMF mu k else 0)
      ≤ Real.exp (-c) * Real.exp (mu * (Real.exp s - 1)) := by
  have hRHS : HasSum (fun k : ℕ => Real.exp (-c) * (poissonPMF mu k * Real.exp (s * k)))
      (Real.exp (-c) * Real.exp (mu * (Real.exp s - 1))) :=
    (hasSum_poissonPMF_mul_exp mu s).mul_left _
  have hnonneg : ∀ k : ℕ, (0 : ℝ) ≤ if P k then poissonPMF mu k else 0 := by
    intro k
    by_cases hk : P k
    · rw [if_pos hk]; exact poissonPMF_nonneg hmu k
    · rw [if_neg hk]
  have hle : ∀ k : ℕ, (if P k then poissonPMF mu k else 0)
      ≤ Real.exp (-c) * (poissonPMF mu k * Real.exp (s * k)) := by
    intro k
    by_cases hk : P k
    · rw [if_pos hk]
      have h1 : (1 : ℝ) ≤ Real.exp (-c) * Real.exp (s * k) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [hP k hk])
      calc poissonPMF mu k = poissonPMF mu k * 1 := (mul_one _).symm
        _ ≤ poissonPMF mu k * (Real.exp (-c) * Real.exp (s * k)) :=
            mul_le_mul_of_nonneg_left h1 (poissonPMF_nonneg hmu k)
        _ = Real.exp (-c) * (poissonPMF mu k * Real.exp (s * k)) := by ring
    · rw [if_neg hk]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (poissonPMF_nonneg hmu k) (Real.exp_pos _).le)
  have hsum : Summable (fun k : ℕ => if P k then poissonPMF mu k else 0) :=
    Summable.of_nonneg_of_le hnonneg hle hRHS.summable
  calc ∑' k : ℕ, (if P k then poissonPMF mu k else 0)
      ≤ ∑' k : ℕ, Real.exp (-c) * (poissonPMF mu k * Real.exp (s * k)) :=
        tsum_le_tsum hle hsum hRHS.summable
    _ = Real.exp (-c) * Real.exp (mu * (Real.exp s - 1)) := hRHS.tsum_eq

/-! ### Two sharp logarithmic inequalities

Both tails need a second-order lower bound on a logarithm.  These are the exact
places where the Chernoff exponent is converted into the advertised Gaussian
shape, and the second one is where the source paper's proof goes wrong (see the
module docstring). -/

/-- `log (1 + x) ≥ x - x²/2` for `x ≥ 0`.

Proof by monotonicity: the difference `log(1+x) - x + x²/2` vanishes at `0` and has
derivative `x²/(1+x) ≥ 0` on `(0, ∞)`. -/
theorem sub_sq_div_two_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  set f : ℝ → ℝ := fun y => Real.log (1 + y) - (y - y ^ 2 / 2) with hfdef
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun y => y ^ 2 / (1 + y)) ?_ ?_ ?_
    · intro y hy
      simp only [Set.mem_Ici] at hy
      have h1y : (1 : ℝ) + y ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt
        (((continuousAt_const.add continuousAt_id).log h1y).sub (by fun_prop))
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      have h1y : (1 : ℝ) + y ≠ 0 := by positivity
      have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y :=
        ((hasDerivAt_id y).const_add 1).log h1y
      have hpoly : HasDerivAt (fun z : ℝ => z - z ^ 2 / 2) (1 - y) y := by
        have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
          simpa using (hasDerivAt_pow 2 y).div_const 2
        simpa using (hasDerivAt_id y).sub h2
      have : HasDerivAt f (y ^ 2 / (1 + y)) y := by
        have := hlog.sub hpoly
        convert this using 1
        field_simp
        ring
      exact this.hasDerivWithinAt
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      positivity
  have h0 : f 0 = 0 := by simp [hfdef]
  have := hmono (Set.left_mem_Ici) (Set.mem_Ici.mpr hx) hx
  rw [h0] at this
  simp only [hfdef] at this
  linarith

/-- `(1 - x) · log (1 - x) ≥ -x + x²/2` for `x ∈ [0, 1)`.

This is the **correct** replacement for the step `-log(1-x) ≤ x + x²/2` asserted in
the proof of Lemma 2 of Banks–Garrabrant–Huber–Perizzolo; that step is false for
every `x > 0`, because `-log(1-x) = x + x²/2 + x³/3 + ⋯ > x + x²/2`.

Proof by monotonicity: the difference `(1-x)log(1-x) + x - x²/2` vanishes at `0`
and has derivative `-log(1-x) - x ≥ 0` on `(0,1)`, the last inequality being
`Real.log_le_sub_one_of_pos` at `1 - x`. -/
theorem neg_add_sq_div_two_le_one_sub_mul_log {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -x + x ^ 2 / 2 ≤ (1 - x) * Real.log (1 - x) := by
  set f : ℝ → ℝ := fun y => (1 - y) * Real.log (1 - y) - (-y + y ^ 2 / 2) with hfdef
  have hmono : MonotoneOn f (Set.Ico (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun y => -Real.log (1 - y) - y) ?_ ?_ ?_
    · intro y hy
      rw [Set.mem_Ico] at hy
      have h1y : (1 : ℝ) - y ≠ 0 := by intro h; linarith [hy.2]
      exact ContinuousAt.continuousWithinAt
        ((((continuousAt_const.sub continuousAt_id)).mul
          ((continuousAt_const.sub continuousAt_id).log h1y)).sub (by fun_prop))
    · intro y hy
      rw [interior_Ico, Set.mem_Ioo] at hy
      have h1y : (1 : ℝ) - y ≠ 0 := by intro h; linarith [hy.2]
      have hu : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub 1
      have hv : HasDerivAt (fun z : ℝ => Real.log (1 - z)) (-1 / (1 - y)) y := hu.log h1y
      have hpoly : HasDerivAt (fun z : ℝ => -z + z ^ 2 / 2) (-1 + y) y := by
        have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
          simpa using (hasDerivAt_pow 2 y).div_const 2
        simpa using (hasDerivAt_id y).neg.add h2
      have hd : HasDerivAt f (-Real.log (1 - y) - y) y := by
        have := (hu.mul hv).sub hpoly
        convert this using 1
        field_simp
        ring
      exact hd.hasDerivWithinAt
    · intro y hy
      rw [interior_Ico, Set.mem_Ioo] at hy
      have h := Real.log_le_sub_one_of_pos (x := 1 - y) (by linarith [hy.2])
      show (0 : ℝ) ≤ -Real.log (1 - y) - y
      linarith
  have h0 : f 0 = 0 := by simp [hfdef]
  have hstep := hmono (Set.left_mem_Ico.mpr one_pos) (Set.mem_Ico.mpr ⟨hx0, hx1⟩) hx0
  rw [h0] at hstep
  simp only [hfdef] at hstep
  linarith

/-! ### The tail bounds -/

set_option linter.unusedVariables false in
/-- **Poisson upper tail** (Banks–Garrabrant–Huber–Perizzolo, Lemma 2).
For `0 < a ≤ μ`,

  `Pr[X ≥ μ + a] = ∑_{k ≥ μ+a} pₖ ≤ exp(-a²/(2μ) + a³/(2μ²))`.

Chernoff with the optimal tilt `t = log(1 + a/μ)` gives the exponent
`a - (μ+a) log(1 + a/μ)`, and `sub_sq_div_two_le_log_one_add` turns that into the
stated quadratic-over-cubic expression, *exactly* (the two agree after clearing
denominators).

The hypothesis `a ≤ μ` is not actually used: the bound holds for all `a > 0`.  It
is retained because the companion lower tail genuinely needs it, and callers
invoke the pair together. -/
theorem poisson_tail_upper {mu a : ℝ} (hmu : 0 < mu) (ha : 0 < a) (hamu : a ≤ mu) :
    ∑' k : ℕ, (if mu + a ≤ (k : ℝ) then poissonPMF mu k else 0)
      ≤ Real.exp (-(1/2) * a^2 / mu + (1/2) * a^3 / mu^2) := by
  have hx0 : 0 < a / mu := div_pos ha hmu
  have h1x : (0 : ℝ) < 1 + a / mu := by linarith
  set t := Real.log (1 + a / mu) with ht
  have hexpt : Real.exp t = 1 + a / mu := Real.exp_log h1x
  have ht0 : 0 < t := Real.log_pos (by linarith)
  have hP : ∀ k : ℕ, mu + a ≤ (k : ℝ) → t * (mu + a) ≤ t * k := fun _ hk =>
    mul_le_mul_of_nonneg_left hk ht0.le
  have hch := tsum_ite_poissonPMF_le hmu.le t (t * (mu + a))
    (fun k : ℕ => mu + a ≤ (k : ℝ)) hP
  refine hch.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hmean : mu * (Real.exp t - 1) = a := by
    rw [hexpt]; field_simp
  rw [hmean]
  have haux := sub_sq_div_two_le_log_one_add (x := a / mu) hx0.le
  rw [← ht] at haux
  have hmul : (mu + a) * (a / mu - (a / mu) ^ 2 / 2) ≤ (mu + a) * t :=
    mul_le_mul_of_nonneg_left haux (by linarith)
  have heq : a - (mu + a) * (a / mu - (a / mu) ^ 2 / 2)
      = -(1/2) * a^2 / mu + (1/2) * a^3 / mu^2 := by
    field_simp
    ring
  nlinarith [hmul, heq]

/-- **Poisson lower tail** (Banks–Garrabrant–Huber–Perizzolo, Lemma 2).
For `0 < a ≤ μ`,

  `Pr[X ≤ μ - a] = ∑_{k ≤ μ-a} pₖ ≤ exp(-a²/(2μ))`.

Chernoff with the optimal tilt `s = log(1 - a/μ) < 0` gives the exponent
`-a - (μ-a) log(1 - a/μ)`, which `neg_add_sq_div_two_le_one_sub_mul_log` bounds by
`-a²/(2μ)`.  (The source paper instead invokes `-log(1-x) ≤ x + x²/2`, which is
false; see the module docstring.)

At the boundary `a = μ` the tilt degenerates (`log 0 = 0` in Lean), so that case is
handled directly: the tail is the single atom `p₀ = e^{-μ} ≤ e^{-μ/2}`. -/
theorem poisson_tail_lower {mu a : ℝ} (hmu : 0 < mu) (ha : 0 < a) (hamu : a ≤ mu) :
    ∑' k : ℕ, (if (k : ℝ) ≤ mu - a then poissonPMF mu k else 0)
      ≤ Real.exp (-a^2 / (2 * mu)) := by
  obtain heq | hlt := eq_or_lt_of_le hamu
  · -- Boundary case `a = μ`: the tail is the single atom `k = 0`.
    subst heq
    have hzero : ∀ k : ℕ, k ≠ 0 → (if (k : ℝ) ≤ a - a then poissonPMF a k else 0) = 0 := by
      intro k hk
      have hne : ¬((k : ℝ) ≤ a - a) := by
        simp only [sub_self, not_le]
        exact_mod_cast Nat.pos_of_ne_zero hk
      rw [if_neg hne]
    have hatom : (if ((0 : ℕ) : ℝ) ≤ a - a then poissonPMF a 0 else 0) = Real.exp (-a) := by
      norm_num [poissonPMF]
    rw [tsum_eq_single 0 hzero, hatom]
    refine Real.exp_le_exp.mpr ?_
    have hval : -a ^ 2 / (2 * a) = -a / 2 := by
      field_simp
      ring
    rw [hval]
    linarith
  · -- Main case `a < μ`: Chernoff with tilt `s = log(1 - a/μ)`.
    have hx0 : 0 < a / mu := div_pos ha hmu
    have hx1 : a / mu < 1 := (div_lt_one hmu).mpr hlt
    have h1x : (0 : ℝ) < 1 - a / mu := by linarith
    set s := Real.log (1 - a / mu) with hs
    have hexps : Real.exp s = 1 - a / mu := Real.exp_log h1x
    have hs0 : s < 0 := Real.log_neg h1x (by linarith)
    have hP : ∀ k : ℕ, (k : ℝ) ≤ mu - a → s * (mu - a) ≤ s * k := fun _ hk =>
      mul_le_mul_of_nonpos_left hk hs0.le
    have hch := tsum_ite_poissonPMF_le hmu.le s (s * (mu - a))
      (fun k : ℕ => (k : ℝ) ≤ mu - a) hP
    refine hch.trans ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hmean : mu * (Real.exp s - 1) = -a := by
      rw [hexps]; field_simp; ring
    rw [hmean]
    have haux := neg_add_sq_div_two_le_one_sub_mul_log (x := a / mu) hx0.le hx1
    rw [← hs] at haux
    have hmul : mu * (-(a / mu) + (a / mu) ^ 2 / 2) ≤ mu * ((1 - a / mu) * s) :=
      mul_le_mul_of_nonneg_left haux hmu.le
    have h1 : mu * (-(a / mu) + (a / mu) ^ 2 / 2) = -a + a ^ 2 / (2 * mu) := by
      field_simp; ring
    have h2 : mu * ((1 - a / mu) * s) = (mu - a) * s := by
      field_simp
    rw [h1, h2] at hmul
    rw [show s * (mu - a) = (mu - a) * s from mul_comm _ _]
    have hval : -a ^ 2 / (2 * mu) = -(a ^ 2 / (2 * mu)) := by ring
    rw [hval]
    linarith

/-! ## Tier 4: Jensen for the square root -/

/-- The AM–GM tangent-line bound `√y ≤ (y/c + c)/2`, valid for `y ≥ 0` and `c > 0`,
with equality at `c = √y`.  This is the linear majorant of `√·` that turns Jensen's
inequality for the (concave) square root into a one-line computation. -/
theorem sqrt_le_div_add_div_two {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) :
    Real.sqrt y ≤ (y / c + c) / 2 := by
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r * r = y :=
    ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.mul_self_sqrt hy⟩
  have hsy : Real.sqrt y = r := by rw [← hr]; exact Real.sqrt_mul_self hr0
  rw [hsy, ← hr, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
  have hrw : r * r / c + c - r * 2 = (r - c) ^ 2 / c := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (sq_nonneg _) hc.le

/-- **Jensen for the square root** (Banks–Garrabrant–Huber–Perizzolo, Lemma 3):
if `X ~ Poisson(μ)` then `E[√X] ≤ √μ`.

Rather than invoking a general concavity/Jensen API we use the tangent-line bound
`sqrt_le_div_add_div_two` at `c = √μ`, which reduces the claim to the mean
`∑ₖ pₖ k = μ` and the normalisation `∑ₖ pₖ = 1`:
`∑ₖ pₖ √k ≤ ∑ₖ pₖ (k/√μ + √μ)/2 = μ/(2√μ) + √μ/2 = √μ`. -/
theorem tsum_poissonPMF_mul_sqrt_le {mu : ℝ} (hmu : 0 ≤ mu) :
    ∑' k : ℕ, poissonPMF mu k * Real.sqrt k ≤ Real.sqrt mu := by
  obtain heq | hpos := eq_or_lt_of_le hmu
  · -- Degenerate rate `μ = 0`: every term vanishes.
    subst heq
    have hterm : (fun k : ℕ => poissonPMF 0 k * Real.sqrt k) = fun _ => 0 := by
      funext k
      cases k with
      | zero => simp
      | succ n => simp [poissonPMF]
    rw [hterm, tsum_zero, Real.sqrt_zero]
  · obtain ⟨c, hc0, hcc⟩ : ∃ c : ℝ, 0 < c ∧ c * c = mu :=
      ⟨Real.sqrt mu, Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt hmu⟩
    have hsqrt : Real.sqrt mu = c := by rw [← hcc]; exact Real.sqrt_mul_self hc0.le
    rw [hsqrt]
    have hbound : ∀ k : ℕ, poissonPMF mu k * Real.sqrt k
        ≤ poissonPMF mu k * (((k : ℝ) / c + c) / 2) := fun k =>
      mul_le_mul_of_nonneg_left (sqrt_le_div_add_div_two (Nat.cast_nonneg k) hc0)
        (poissonPMF_nonneg hmu k)
    have hRHS : HasSum (fun k : ℕ => poissonPMF mu k * (((k : ℝ) / c + c) / 2)) c := by
      have h := ((hasSum_poissonPMF_mul_id mu).mul_left (1 / (2 * c))).add
        ((hasSum_poissonPMF mu).mul_left (c / 2))
      have hval : 1 / (2 * c) * mu + c / 2 * 1 = c := by
        field_simp
        linarith [hcc]
      rw [hval] at h
      refine h.congr_fun ?_
      intro k
      field_simp
      ring
    have hsum : Summable (fun k : ℕ => poissonPMF mu k * Real.sqrt k) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (poissonPMF_nonneg hmu k) (Real.sqrt_nonneg _))
        hbound hRHS.summable
    calc ∑' k : ℕ, poissonPMF mu k * Real.sqrt k
        ≤ ∑' k : ℕ, poissonPMF mu k * (((k : ℝ) / c + c) / 2) :=
          tsum_le_tsum hbound hsum hRHS.summable
      _ = c := hRHS.tsum_eq

/-! ## Tier 5: convolution -/

/-- **The Poisson family is closed under convolution**: the sum of independent
`Poisson(μ)` and `Poisson(ν)` variables is `Poisson(μ+ν)`,

  `∑_{j ≤ k} p_μ(j) · p_ν(k-j) = p_{μ+ν}(k)`.

This is the binomial theorem together with
`Nat.choose_mul_factorial_mul_factorial`.  It is what lets `r` independent runs of
a Poisson-output procedure be analysed as a single Poisson variable of rate `r·μ`. -/
theorem poissonPMF_conv (mu nu : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), poissonPMF mu j * poissonPMF nu (k - j)
      = poissonPMF (mu + nu) k := by
  have hrhs : poissonPMF (mu + nu) k
      = ∑ j ∈ Finset.range (k + 1),
          Real.exp (-(mu + nu)) * (mu ^ j * nu ^ (k - j) * (Nat.choose k j))
            / (Nat.factorial k) := by
    rw [poissonPMF, add_pow, Finset.mul_sum, Finset.sum_div]
  rw [hrhs]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
  have hj! : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hkj! : (Nat.factorial (k - j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - j))
  have hC : (Nat.choose k j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hjk).ne'
  have hchoose : (Nat.choose k j : ℝ) * (Nat.factorial j) * (Nat.factorial (k - j))
      = (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
  rw [poissonPMF, poissonPMF, ← hchoose, neg_add, Real.exp_add]
  field_simp
  ring

end Arlib
