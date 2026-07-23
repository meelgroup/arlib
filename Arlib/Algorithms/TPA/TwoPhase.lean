/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two-phase TPA schedule: the arithmetic of the run counts

TPA's counter is `Poisson(A)` with `A = ln(μ(B)/μ(B'))` (`Arlib.Algorithms.TPA.Count`), so
to make `k/r` concentrate one wants `r ≈ A` — but `A` is the unknown.  Hence the
two-phase schedule: a cheap first phase with `r₁ = 2 ln(2/δ)` produces a rough
`Â₁`, and the second phase uses

  `r₂ = 2 (Â₁ + √Â₁ + 2) · [ε'² − ε'³]⁻¹ · ln(4/δ)`,   `ε' = ln(1+ε)`.

This file isolates the **purely arithmetic** content of that analysis — the
inequalities that must hold for the Chernoff exponents to clear `ln(2/δ)` and
`ln(4/δ)`.  Separating them from the probability is worth doing: it is exactly
here that the published proof goes wrong, and stating each step as a standalone
real inequality makes the missing hypothesis visible.

## What the arithmetic reveals

* **Phase one is exact, not approximate.**  The threshold `t = A − 3/2 − √(A−7/4)`
  is precisely the fixed point of `x ↦ x + √x + 2` (`phase1_threshold_fixed`),
  because `t` is the perfect square `(√(A−7/4) − 1/2)²`.  So the failure event
  `{Â₁ + √Â₁ + 2 < A}` is *exactly* `{Â₁ < t}` (`phase1_event_subset`), with no
  slack lost.

* **Phase two forces `1 ≤ A`.**  Substituting `r₂` into the upper-tail exponent
  reduces the requirement to `(1 − ε'/A)/(1 − ε') ≥ 1`, i.e. to `A ≥ 1`
  (`phase2_upper_budget`).  The source paper states its Theorem 5 for an
  arbitrary poset and never records this; for `#(𝓛) ∈ {1,2}` the displayed chain
  of inequalities does not close.  The lower tail (`phase2_lower_budget`) needs
  only `A > 0`.

* **The payoff is a two-line exponential fact.**  `relative_error_of_log_error`
  converts additive accuracy `ln(1+ε)` on the log scale into multiplicative
  accuracy `1 + ε`, which is the form the theorem is stated in.

Throughout, `e` is the paper's `ε' = ln(1+ε)` and `d` is the target log-failure
budget (`ln(2/δ)` or `ln(4/δ)`).
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Arlib.Algorithms.TPA

/-! ## Phase one: the run-count guess is big enough -/

/-- `√(A - 7/4) ≥ 1/2` when `A ≥ 2`. -/
theorem half_le_sqrt {A : ℝ} (hA : 2 ≤ A) : (1:ℝ)/2 ≤ Real.sqrt (A - 7/4) := by
  have h : Real.sqrt (1/4 : ℝ) ≤ Real.sqrt (A - 7/4) := Real.sqrt_le_sqrt (by linarith)
  rwa [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-- The phase-one threshold is a perfect square: `A - 3/2 - √(A-7/4) = (√(A-7/4) - 1/2)²`. -/
theorem phase1_threshold_sq {A : ℝ} (hA : 2 ≤ A) :
    A - 3/2 - Real.sqrt (A - 7/4) = (Real.sqrt (A - 7/4) - 1/2) ^ 2 := by
  have hA74 : (0:ℝ) ≤ A - 7/4 := by linarith
  have hsq : Real.sqrt (A - 7/4) ^ 2 = A - 7/4 := Real.sq_sqrt hA74
  nlinarith [hsq]

theorem phase1_threshold_nonneg {A : ℝ} (hA : 2 ≤ A) :
    0 ≤ A - 3/2 - Real.sqrt (A - 7/4) := by
  rw [phase1_threshold_sq hA]; positivity

/-- The phase-one threshold `t = A - 3/2 - √(A - 7/4)` is the exact fixed point:
`t + √t + 2 = A`. -/
theorem phase1_threshold_eq {A : ℝ} (hA : 2 ≤ A) :
    Real.sqrt (A - 3/2 - Real.sqrt (A - 7/4)) = Real.sqrt (A - 7/4) - 1/2 := by
  rw [phase1_threshold_sq hA, Real.sqrt_sq (by linarith [half_le_sqrt hA])]

theorem phase1_threshold_fixed {A : ℝ} (hA : 2 ≤ A) :
    (A - 3/2 - Real.sqrt (A - 7/4))
      + Real.sqrt (A - 3/2 - Real.sqrt (A - 7/4)) + 2 = A := by
  rw [phase1_threshold_eq hA]; ring

/-- `x ↦ x + √x + 2` is monotone on `[0,∞)`. -/
theorem phase1_mono {x y : ℝ} (hxy : x ≤ y) :
    x + Real.sqrt x + 2 ≤ y + Real.sqrt y + 2 := by
  have := Real.sqrt_le_sqrt hxy
  linarith

/-- **The phase-one event, restated as a tail event.**  If the first-phase
estimate `Ahat` fails to certify `A` — that is, `Ahat + √Ahat + 2 < A` — then
`Ahat` lies below the explicit threshold `A - 3/2 - √(A - 7/4)`, which is what
lets a Poisson lower-tail bound be applied. -/
theorem phase1_event_subset {A Ahat : ℝ} (hA : 2 ≤ A)
    (hfail : Ahat + Real.sqrt Ahat + 2 < A) :
    Ahat < A - 3/2 - Real.sqrt (A - 7/4) := by
  by_contra hcon
  push_neg at hcon
  have hle := phase1_mono hcon
  rw [phase1_threshold_fixed hA] at hle
  linarith

/-- The deviation `a = 3/2 + √(A - 7/4)` satisfies `a² / A ≥ 1` for `A ≥ 2`, so
the Poisson lower-tail exponent `−a²/(2μ)` is at most `−r₁/2`. -/
theorem phase1_deviation_sq {A : ℝ} (hA : 2 ≤ A) :
    A ≤ (3/2 + Real.sqrt (A - 7/4)) ^ 2 := by
  have hA74 : (0:ℝ) ≤ A - 7/4 := by linarith
  have hsq : Real.sqrt (A - 7/4) ^ 2 = A - 7/4 := Real.sq_sqrt hA74
  nlinarith [Real.sqrt_nonneg (A - 7/4), hsq]

/-- And the deviation is admissible for the Chernoff bound (`a ≤ μ`). -/
theorem phase1_deviation_le {A : ℝ} (hA : 2 ≤ A) :
    3/2 + Real.sqrt (A - 7/4) ≤ A := by
  have hA74 : (0:ℝ) ≤ A - 7/4 := by linarith
  have hsq : Real.sqrt (A - 7/4) ^ 2 = A - 7/4 := Real.sq_sqrt hA74
  nlinarith [Real.sqrt_nonneg (A - 7/4), hsq]

/-! ## Phase two: the run count delivers the accuracy -/

/-- **The phase-two upper-tail budget.**  This is the inequality the paper's
proof needs at `:934-941`, and it is where the hypothesis `1 ≤ A` is forced:
after substituting `r₂`, the requirement reduces to `(1 − e/A)/(1 − e) ≥ 1`. -/
theorem phase2_upper_budget {A e d r : ℝ} (hA : 1 ≤ A) (he0 : 0 < e) (he1 : e < 1)
    (hd : 0 ≤ d) (hr : 2 * A * (e^2 - e^3)⁻¹ * d ≤ r) :
    d ≤ (1/2) * r * e^2 / A - (1/2) * r * e^3 / A^2 := by
  have hA0 : 0 < A := by linarith
  have hden : 0 < e^2 - e^3 := by
    have hfe : e^2 - e^3 = e^2 * (1 - e) := by ring
    rw [hfe]; exact mul_pos (by positivity) (by linarith)
  have hkey : (1/2) * r * e^2 / A - (1/2) * r * e^3 / A^2
      = (r / 2) * (e^2 / A) * (1 - e / A) := by
    field_simp; ring
  rw [hkey]
  have hr2 : A * (e^2 - e^3)⁻¹ * d ≤ r / 2 := by linarith
  have hfac : 0 < e^2 / A := by positivity
  have hfac2 : 0 ≤ 1 - e / A := by
    have : e / A ≤ e := by
      rw [div_le_iff₀ hA0]; nlinarith
    linarith
  -- lower-bound `r/2` and simplify
  have hstep : A * (e^2 - e^3)⁻¹ * d * (e^2 / A) * (1 - e / A)
      ≤ (r / 2) * (e^2 / A) * (1 - e / A) := by
    apply mul_le_mul_of_nonneg_right _ hfac2
    exact mul_le_mul_of_nonneg_right hr2 (le_of_lt hfac)
  refine le_trans ?_ hstep
  -- `A·(e²−e³)⁻¹·d·(e²/A)·(1−e/A) = d·(1−e/A)/(1−e) ≥ d`
  have hcalc : A * (e^2 - e^3)⁻¹ * d * (e^2 / A) * (1 - e / A)
      = d * (1 - e / A) / (1 - e) := by
    have h1e : (1 : ℝ) - e ≠ 0 := by linarith
    have hfe : e^2 - e^3 = e^2 * (1 - e) := by ring
    rw [hfe]
    field_simp
    ring
  rw [hcalc]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - e)]
  have : e / A ≤ e := by
    rw [div_le_iff₀ hA0]; nlinarith
  nlinarith

/-- **The phase-two lower-tail budget.**  No hypothesis on `A` beyond positivity
is needed here — the left tail is the easy side. -/
theorem phase2_lower_budget {A e d r : ℝ} (hA : 0 < A) (he0 : 0 < e) (he1 : e < 1)
    (hd : 0 ≤ d) (hr : 2 * A * (e^2 - e^3)⁻¹ * d ≤ r) :
    d ≤ (1/2) * r * e^2 / A := by
  have hden : 0 < e^2 - e^3 := by
    have hfe : e^2 - e^3 = e^2 * (1 - e) := by ring
    rw [hfe]; exact mul_pos (by positivity) (by linarith)
  have hr2 : A * (e^2 - e^3)⁻¹ * d ≤ r / 2 := by linarith
  have hfac : 0 < e^2 / A := by positivity
  have hstep : A * (e^2 - e^3)⁻¹ * d * (e^2 / A) ≤ (r / 2) * (e^2 / A) :=
    mul_le_mul_of_nonneg_right hr2 (le_of_lt hfac)
  have hcalc : A * (e^2 - e^3)⁻¹ * d * (e^2 / A) = d / (1 - e) := by
    have hfe : e^2 - e^3 = e^2 * (1 - e) := by ring
    have h1e : (1 : ℝ) - e ≠ 0 := by linarith
    rw [hfe]; field_simp; ring
  have hgoal : (1/2) * r * e^2 / A = (r / 2) * (e^2 / A) := by field_simp
  rw [hgoal]
  refine le_trans ?_ hstep
  rw [hcalc, le_div_iff₀ (by linarith : (0:ℝ) < 1 - e)]
  nlinarith

/-! ## From additive accuracy on the log scale to multiplicative accuracy -/

/-- **The payoff.**  An additive error of at most `ln(1+ε)` in the estimate of
`A = ln #(𝓛)` is exactly a multiplicative error of at most `1 + ε` in the
estimate `exp Ahat` of `exp A = #(𝓛)`.  This is the paper's final step
(`:950-954`). -/
theorem relative_error_of_log_error {A Ahat eps : ℝ} (heps : 0 < eps)
    (h : |Ahat - A| ≤ Real.log (1 + eps)) :
    (1 + eps)⁻¹ ≤ Real.exp Ahat / Real.exp A ∧
      Real.exp Ahat / Real.exp A ≤ 1 + eps := by
  have hpos : (0:ℝ) < 1 + eps := by linarith
  rw [← Real.exp_sub]
  rw [abs_le] at h
  constructor
  · rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith [h.1])
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr h.2

end Arlib.Algorithms.TPA
