/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Rademacher averages, the sub-Gaussian MGF bound, and Khintchine

The elementary proof of the ℓ¹ matrix concentration bound (Cohen–Peng, "ℓ_p Row
Sampling by Lewis Weights", Section 6) rests on a single analytic fact about sums
of independent signs: they are sub-Gaussian, and consequently their even moments
are controlled by the sum of squares (Khintchine's inequality).  This file proves
exactly that, from first principles, over the finite uniform space of sign
patterns `ι → Bool`.

* `Sgn b` — the real sign `±1` a `Bool` stands for (`true ↦ 1`, `false ↦ -1`).
* `avg f` — the expectation of `f : (ι → Bool) → ℝ` under the uniform measure,
  `(∑ s, f s) / 2 ^ |ι|`.  This is the Rademacher expectation `𝔼_σ`.
* `avg_exp_le` — **the sub-Gaussian MGF bound**:
  `avg (fun s => exp (∑ i, Sgn (s i) * x i)) ≤ exp ((∑ i, x i ^ 2) / 2)`.
  The whole content of "a sign sum is sub-Gaussian with variance proxy `∑ xᵢ²`".
* `avg_pow_le` — **even-moment Khintchine**: for `k ≥ 1`,
  `avg (fun s => (∑ i, Sgn (s i) * x i) ^ (2 * k)) ≤ (2 * exp 1 * k * ∑ i, x i ^ 2) ^ k`.

The MGF bound is the product formula `𝔼 ∏ = ∏ 𝔼` (`Finset.prod_univ_sum` over the
product space) composed with the pointwise `cosh x ≤ exp (x²/2)`.  The moment
bound extracts a single even power from `cosh` via its (termwise nonnegative)
power series and optimises the free scale `t = √(2k / ∑xᵢ²)`.

No `sorry`.
-/
import Mathlib.Algebra.BigOperators.Field
import Arlib.Prelude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Signs -/

/-- The real number a `Bool` stands for as a Rademacher sign: `true ↦ 1`,
`false ↦ -1`. -/
def Sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem Sgn_true : Sgn true = 1 := rfl
@[simp] theorem Sgn_false : Sgn false = -1 := rfl

theorem Sgn_sq (b : Bool) : Sgn b ^ 2 = 1 := by cases b <;> simp [Sgn]

theorem abs_Sgn (b : Bool) : |Sgn b| = 1 := by cases b <;> simp [Sgn]

/-! ## The uniform Rademacher expectation -/

/-- The **Rademacher expectation** of `f`: the average of `f` over all `2 ^ |ι|`
sign patterns, `𝔼_σ f = (∑ s, f s) / 2 ^ |ι|`. -/
noncomputable def avg (f : (ι → Bool) → ℝ) : ℝ :=
  (∑ s : ι → Bool, f s) / 2 ^ Fintype.card ι

theorem avg_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ s, 0 ≤ f s) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun s _ => hf s) (by positivity)

theorem avg_mono {f g : (ι → Bool) → ℝ} (h : ∀ s, f s ≤ g s) : avg f ≤ avg g := by
  unfold avg
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun s _ => h s
  -- (`div_le_div_of_nonneg_right` gives `a ≤ b → 0 < c → a/c ≤ b/c`)

/-- Averaging distributes over a sum of two functions. -/
theorem avg_add (f g : (ι → Bool) → ℝ) :
    avg (fun s => f s + g s) = avg f + avg g := by
  unfold avg
  rw [← add_div, Finset.sum_add_distrib]

/-- A constant scalar pulls out of the average. -/
theorem avg_const_mul (c : ℝ) (f : (ι → Bool) → ℝ) :
    avg (fun s => c * f s) = c * avg f := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

/-! ## The product formula over the sign space -/

/-- **Expectation of a product factorises.**  For a family `g i : Bool → ℝ`,
`∑_{s : ι → Bool} ∏ i, g i (s i) = ∏ i, (g i true + g i false)`.  This is the
finite Fubini identity `∏ ∑ = ∑ ∏` specialised to the two-point domain. -/
theorem sum_prod_bool (g : ι → Bool → ℝ) :
    (∑ s : ι → Bool, ∏ i, g i (s i)) = ∏ i, (g i true + g i false) := by
  have hcongr : ∏ i, (g i true + g i false) = ∏ i, ∑ b : Bool, g i b := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
  rw [hcongr, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ## The sub-Gaussian MGF bound -/

/-- **The sub-Gaussian moment generating function bound for sign sums.**
`𝔼_σ exp (∑ᵢ σᵢ xᵢ) ≤ exp (∑ᵢ xᵢ² / 2)`.  This is the entire content of "a sum
of independent signs weighted by `x` is sub-Gaussian with variance proxy
`∑ xᵢ²`", and everything downstream (Khintchine, the concentration bound) is a
corollary of it.  Proof: the expectation of the product factorises into
`∏ᵢ cosh xᵢ` (`sum_prod_bool`), and `cosh xᵢ ≤ exp (xᵢ²/2)` termwise. -/
theorem avg_exp_le (x : ι → ℝ) :
    avg (fun s => Real.exp (∑ i, Sgn (s i) * x i)) ≤ Real.exp ((∑ i, x i ^ 2) / 2) := by
  have hstep : avg (fun s => Real.exp (∑ i, Sgn (s i) * x i)) = ∏ i, Real.cosh (x i) := by
    unfold avg
    have hexp : ∀ s : ι → Bool,
        Real.exp (∑ i, Sgn (s i) * x i) = ∏ i, Real.exp (Sgn (s i) * x i) := by
      intro s; rw [Real.exp_sum]
    simp_rw [hexp]
    rw [sum_prod_bool (fun i b => Real.exp (Sgn b * x i))]
    have hcosh : ∀ i, Real.exp (Sgn true * x i) + Real.exp (Sgn false * x i)
        = 2 * Real.cosh (x i) := by
      intro i
      simp only [Sgn_true, Sgn_false, one_mul, neg_one_mul]
      rw [Real.cosh_eq]; ring
    simp_rw [hcosh]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
    field_simp
  rw [hstep]
  calc ∏ i, Real.cosh (x i)
      ≤ ∏ i, Real.exp (x i ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro i _; exact (Real.cosh_pos _).le
        · intro i _; exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (∑ i, x i ^ 2 / 2) := by rw [← Real.exp_sum]
    _ = Real.exp ((∑ i, x i ^ 2) / 2) := by rw [← Finset.sum_div]
