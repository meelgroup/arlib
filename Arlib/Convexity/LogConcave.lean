/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Basic

/-
# Log-concave functions on `ℝ`

Mathlib (`v4.15`) has no notion of log-concavity, so this file introduces one in the
multiplicative form the convex-geometry literature uses:

  `f((1−t)x + ty) ≥ f(x)^(1−t) · f(y)^t`.

This is the hypothesis under which the isoperimetric inequality of
`Arlib.Convexity.Isoperimetry` is stated, and it is the form in which the
Lovász–Simonovits / Kannan–Lovász–Simonovits results are quoted.

Stated with `Real.rpow` rather than `Monotone`/`ConvexOn (-log f)` so that it applies to
functions with zeros — which is essential, since the densities of interest are supported
on a bounded body and vanish outside it.

## Main definitions

* `Arlib.LogConcave` — the multiplicative inequality above.

## Main results

* `Arlib.LogConcave.mul` — a product of log-concave functions is log-concave. This is the
  closure property the Gaussian-restricted densities `f · γ` need.
* `Arlib.logConcave_const` — constants are log-concave.
-/

namespace Arlib

open Real

/-- **Log-concavity** on `ℝ`, in multiplicative form:
`f(x)^(1−t) · f(y)^t ≤ f((1−t)x + ty)` for every `t ∈ [0,1]`.

Nonnegativity is carried separately (`hf : ∀ x, 0 ≤ f x`) rather than bundled, so the
definition composes with Mathlib's `Real.rpow` lemmas without side conditions. -/
def LogConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) * x + t * y)

/-- A nonnegative constant function is log-concave. -/
theorem logConcave_const {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun _ => c) := by
  intro x y t ht0 ht1
  simp only
  rcases eq_or_lt_of_le hc with h | h
  · simp [← h, Real.zero_rpow, sub_eq_zero]
    rcases eq_or_lt_of_le ht0 with h' | h'
    · simp [← h']
    · simp [Real.zero_rpow (ne_of_gt h'), zero_mul]
  · rw [← Real.rpow_add h]
    simp

/-- **Log-concave functions are unimodal**: on any interval, the value is at least the
smaller of the two endpoint values.

This is the pointwise fact underneath the one-dimensional isoperimetric inequality — it is
what stops a log-concave density from dipping in the middle of the separating interval,
and hence what makes the middle set carry mass. -/
theorem LogConcave.min_le_of_mem_Icc {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v t : ℝ} (ht : t ∈ Set.Icc u v) : min (f u) (f v) ≤ f t := by
  obtain ⟨htu, htv⟩ := ht
  rcases eq_or_lt_of_le (le_trans htu htv) with huv | huv
  · have htu' : t = u := le_antisymm (huv ▸ htv) htu
    subst htu'
    exact min_le_left _ _
  · have hvu : (0 : ℝ) < v - u := by linarith
    set s := (t - u) / (v - u) with hsdef
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hvu.le
    have hs1 : s ≤ 1 := by rw [hsdef, div_le_one hvu]; linarith
    have hts : (1 - s) * u + s * v = t := by
      rw [hsdef]; field_simp; ring
    have hm0 : 0 ≤ min (f u) (f v) := le_min (hf0 u) (hf0 v)
    rcases eq_or_lt_of_le hm0 with hm | hm
    · rw [← hm]; exact hf0 t
    · calc min (f u) (f v)
          = min (f u) (f v) ^ (1 - s) * min (f u) (f v) ^ s := by
            rw [← Real.rpow_add hm]; simp
        _ ≤ f u ^ (1 - s) * f v ^ s := by
            refine mul_le_mul (Real.rpow_le_rpow hm0 (min_le_left _ _) (by linarith))
              (Real.rpow_le_rpow hm0 (min_le_right _ _) hs0)
              (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg (hf0 u) _)
        _ ≤ f ((1 - s) * u + s * v) := hf u v s hs0 hs1
        _ = f t := by rw [hts]

/-- **A product of log-concave functions is log-concave.**

This is the closure property the analysis of Gaussian-restricted densities needs: if `f`
is log-concave and `γ` is the Gaussian weight (log-concave, being `exp` of a concave
quadratic), then `f · γ` is log-concave. -/
theorem LogConcave.mul {f g : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : LogConcave f) (hg : LogConcave g) : LogConcave (fun x => f x * g x) := by
  intro x y t ht0 ht1
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  calc (f x * g x) ^ (1 - t) * (f y * g y) ^ t
      = (f x ^ (1 - t) * f y ^ t) * (g x ^ (1 - t) * g y ^ t) := by
        rw [Real.mul_rpow (hf0 x) (hg0 x), Real.mul_rpow (hf0 y) (hg0 y)]; ring
    _ ≤ f ((1 - t) * x + t * y) * g ((1 - t) * x + t * y) := by
        refine mul_le_mul (hf x y t ht0 ht1) (hg x y t ht0 ht1) ?_ ?_
        · exact mul_nonneg (Real.rpow_nonneg (hg0 x) _) (Real.rpow_nonneg (hg0 y) _)
        · exact le_trans (mul_nonneg (Real.rpow_nonneg (hf0 x) _)
            (Real.rpow_nonneg (hf0 y) _)) (hf x y t ht0 ht1)

end Arlib
