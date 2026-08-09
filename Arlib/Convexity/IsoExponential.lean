/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.Isoperimetry
import Mathlib.Analysis.SpecialFunctions.Exp

/-
# The one-dimensional isoperimetric inequality for the exponential density

This file proves the one-dimensional isoperimetric inequality **outright** for the
exponential density — the extremal case, which is what fixes the constant in the general
theorem.

For `f(x) = λe^{-λx}` and `u ≤ v`, the three masses of the partition
`(-∞,u] , [u,v] , [v,∞)` are

  `A = 1 - e^{-λu}`,   `M = e^{-λu} - e^{-λv}`,   `B = e^{-λv}`,

and `Arlib.exp_isoperimetry` says

  `λ · (v - u) · A · B  ≤  M`.

**The constant is sharp and is `λ = 1/E|X|`**, which is the normalisation
Kannan–Lovász–Simonovits state their inequality in: for an isotropic density the
coefficient is an absolute constant precisely because `E|X|` is fixed. So this is not an
isolated computation — it is the case that determines the general constant.

The proof: `M = e^{-λv}(e^{λd} - 1)` with `d = v - u`, then `e^{λd} - 1 ≥ λd` and `A ≤ 1`.

## Scope

The general one-dimensional inequality (an arbitrary log-concave density) reduces to this
extremal case, but that reduction — a variational/localization argument in one dimension —
is **not** proved here. See `Arlib.Convexity.Isoperimetry` for the interface and for the
half of the general case that is proved (`Arlib.le_intervalIntegral_of_logConcave`).
-/

namespace Arlib

open Real

/-- **The exponential weight is log-concave.** It is log-affine, so the defining
inequality holds with equality. -/
theorem logConcave_exp (lam : ℝ) : LogConcave (fun x => Real.exp (-(lam * x))) := by
  intro x y t _ _
  simp only
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

/-- **The one-dimensional isoperimetric inequality for the exponential density.**

With `A = 1 - e^{-λu}` the left tail mass, `B = e^{-λv}` the right tail mass and
`M = e^{-λu} - e^{-λv}` the mass of the separating interval `[u,v]`,

  `λ · (v - u) · A · B  ≤  M`.

The coefficient `λ` is exactly `1/E|X|` for this density, which is the
Kannan–Lovász–Simonovits normalisation. -/
theorem exp_isoperimetry {lam u v : ℝ} (hlam : 0 < lam) (huv : u ≤ v) :
    lam * (v - u) * ((1 - Real.exp (-(lam * u))) * Real.exp (-(lam * v)))
      ≤ Real.exp (-(lam * u)) - Real.exp (-(lam * v)) := by
  set d : ℝ := v - u with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  -- `e^{-λu} = e^{-λv} · e^{λd}`, so the middle mass factorises
  have hmid : Real.exp (-(lam * u)) - Real.exp (-(lam * v))
      = Real.exp (-(lam * v)) * (Real.exp (lam * d) - 1) := by
    have hsplit : Real.exp (-(lam * u)) = Real.exp (-(lam * v)) * Real.exp (lam * d) := by
      rw [← Real.exp_add]
      congr 1
      rw [hd]; ring
    rw [hsplit]; ring
  -- `λd ≤ e^{λd} - 1`
  have hkey : lam * d ≤ Real.exp (lam * d) - 1 := by
    have := Real.add_one_le_exp (lam * d); linarith
  -- the left tail mass is at most `1`
  have hA : 1 - Real.exp (-(lam * u)) ≤ 1 := by
    have := Real.exp_pos (-(lam * u)); linarith
  have hBpos : 0 < Real.exp (-(lam * v)) := Real.exp_pos _
  rw [hmid]
  calc lam * d * ((1 - Real.exp (-(lam * u))) * Real.exp (-(lam * v)))
      ≤ lam * d * (1 * Real.exp (-(lam * v))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hA hBpos.le
    _ = Real.exp (-(lam * v)) * (lam * d) := by ring
    _ ≤ Real.exp (-(lam * v)) * (Real.exp (lam * d) - 1) :=
        mul_le_mul_of_nonneg_left hkey hBpos.le

end Arlib
