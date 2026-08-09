/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.LogConcave
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-
# Isoperimetry for log-concave measures: the elementary reductions

An *isoperimetric inequality* for a measure `π` on a metric space bounds the mass of the
"middle" set `S₃` of a partition below, in terms of the separation between `S₁` and `S₂`:

  `π(S₃) ≥ c · d(S₁,S₂) · π(S₁) · π(S₂)`.

Such bounds are what lower-bound the **conductance** of a random walk, and hence its
mixing time; they are the geometric input to every log-concave sampling analysis
(Lovász–Simonovits, Kannan–Lovász–Simonovits, and the volume algorithms built on them).

## What this file proves

The **product-to-minimum conversion**. The inequality above is naturally proved in
*product* form `π S₁ · π S₂`, but conductance arguments consume it in *minimum* form
`min (π S₁) (π S₂)`. `Arlib.min_le_of_prod_le` is that conversion, and it is exact
arithmetic on a partition of unit mass — no measure theory, no geometry, so it is reusable
for any partition-based expansion argument (graph conductance, Cheeger-type bounds,
Markov-chain expansion).

It is the step Kannan–Lovász–Simonovits perform in one line, and the constant it produces,
`c / (2 + c)`, is the one the literature quotes.

## What this file does NOT prove

The isoperimetric inequality itself. The one-dimensional case for log-concave densities
(KLS95, Theorem 5.1) is a genuine theorem whose proof is not here, and the
`n`-dimensional case reduces to it only via the Lovász–Simonovits localization lemma.
Neither is available in Mathlib. `Arlib.OneDimIsoperimetry` states the one-dimensional
inequality as an explicit interface so that consumers can be written against it now and it
can be discharged later.

## Main results

* `Arlib.min_le_of_prod_le` — product form implies minimum form, with constant `c/(2+c)`.
* `Arlib.OneDimIsoperimetry` — the one-dimensional inequality, as an interface.
* `Arlib.OneDimIsoperimetry.min_form` — its minimum-form consequence.
-/

namespace Arlib

/-- **Product form implies minimum form.**

If three nonnegative numbers summing to `1` satisfy `c · p₁ · p₂ ≤ p₃`, then
`(c / (2 + c)) · min p₁ p₂ ≤ p₃`.

This is the step that turns an isoperimetric bound stated as a *product* of the two side
masses into the *minimum* form that conductance arguments use. The constant `c/(2+c)` is
sharp for this derivation: the worst case is `p₁ = p₂ = 1/2`.

Purely arithmetic, so it applies to any partition of unit mass — a measure-theoretic
partition, a vertex partition of a graph, or the state space of a Markov chain. -/
theorem min_le_of_prod_le {c p₁ p₂ p₃ : ℝ} (hc : 0 < c)
    (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0 ≤ p₃) (hsum : p₁ + p₂ + p₃ = 1)
    (h : c * p₁ * p₂ ≤ p₃) :
    c / (2 + c) * min p₁ p₂ ≤ p₃ := by
  have hc2 : (0 : ℝ) < 2 + c := by linarith
  -- The core, applied to whichever side is smaller. Writing `q` for that side:
  -- `p₃(1 + cq) ≥ cq(1−q)` from the product bound, and `(1−q)(2+c) ≥ 1 + cq`
  -- from `q ≤ 1/2`; multiplying and cancelling `1 + cq > 0` gives the claim.
  have key : ∀ q r : ℝ, 0 ≤ q → q ≤ r → q + r + p₃ = 1 → c * q * r ≤ p₃ →
      c * q ≤ p₃ * (2 + c) := by
    intro q r hq hqr hs hprod
    have hhalf : q ≤ 1 / 2 := by linarith
    have hr' : r = 1 - q - p₃ := by linarith
    rw [hr'] at hprod
    have hcq : 0 ≤ c * q := mul_nonneg hc.le hq
    have hpos : (0 : ℝ) < 1 + c * q := by linarith
    have hA : c * q * (1 - q) ≤ p₃ * (1 + c * q) := by nlinarith [hprod]
    have hB : 1 + c * q ≤ (1 - q) * (2 + c) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + c) (by linarith : (0:ℝ) ≤ 1 - 2 * q)]
    have hmul1 : c * q * (1 + c * q) ≤ c * q * ((1 - q) * (2 + c)) :=
      mul_le_mul_of_nonneg_left hB hcq
    have hmul2 : c * q * (1 - q) * (2 + c) ≤ p₃ * (1 + c * q) * (2 + c) :=
      mul_le_mul_of_nonneg_right hA hc2.le
    nlinarith [hmul1, hmul2, hpos]
  rcases le_total p₁ p₂ with hab | hab
  · rw [min_eq_left hab, div_mul_eq_mul_div, div_le_iff₀ hc2]
    exact key p₁ p₂ h1 hab hsum h
  · rw [min_eq_right hab, div_mul_eq_mul_div, div_le_iff₀ hc2]
    refine key p₂ p₁ h2 hab (by linarith) ?_
    rw [show c * p₂ * p₁ = c * p₁ * p₂ by ring]; exact h

/-! ## Toward the one-dimensional inequality

The one-dimensional isoperimetric inequality asks, for a log-concave density `f` and
`u ≤ v` separating the two outer sets,

  `∫ᵤᵛ f  ≥  c · (v − u) · (∫_{-∞}^u f) · (∫_v^∞ f)`.

Its proof splits in two. The **first half** is the mass the separating interval must carry
purely because `f` is log-concave, and it is proved below: unimodality
(`Arlib.LogConcave.min_le_of_mem_Icc`) says `f` does not dip between `u` and `v`, so the
interval carries at least `(v − u) · min (f u) (f v)`.

The **second half** — bounding `min (f u) (f v)` below by a multiple of the product of the
two tail masses — is where the theorem actually lives, and where the normalisation (the
isotropy / `E|x|` constant of Kannan–Lovász–Simonovits) enters. It is not proved here. -/

/-- **The mass of a separating interval, from log-concavity alone.**

Since a log-concave `f` cannot dip below its endpoint values on `[u,v]`, the interval
carries mass at least `(v − u) · min (f u) (f v)`.

This is the first half of the one-dimensional isoperimetric inequality (see the section
docstring). Combined with a lower bound on `min (f u) (f v)` in terms of the tail masses,
it gives the full statement. -/
theorem le_intervalIntegral_of_logConcave {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) {u v : ℝ} (huv : u ≤ v)
    (hint : IntervalIntegrable f MeasureTheory.volume u v) :
    (v - u) * min (f u) (f v) ≤ ∫ x in u..v, f x := by
  have hconst : IntervalIntegrable (fun _ => min (f u) (f v)) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on huv hconst hint
    (fun x hx => LogConcave.min_le_of_mem_Icc hf0 hf hx)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- **The one-dimensional isoperimetric inequality, modulo the endpoint-density bound.**

Everything around the missing step, proved. `A` and `B` are the two tail masses (instantiate
with `∫_{-∞}^u f` and `∫_v^∞ f`); `hend` is the residual — that the smaller endpoint density
dominates `c · A · B`. Given it, the isoperimetric inequality follows from unimodality alone.

This isolates exactly what a proof of the one-dimensional inequality still has to supply.
`hend` is the half where the normalisation constant of Kannan–Lovász–Simonovits lives, and
it is **not** proved here. -/
theorem oneDim_iso_of_endpoint_bound {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) {u v c A B : ℝ} (huv : u ≤ v)
    (hint : IntervalIntegrable f MeasureTheory.volume u v)
    (hend : c * A * B ≤ min (f u) (f v)) :
    c * A * B * (v - u) ≤ ∫ x in u..v, f x := by
  refine le_trans (mul_le_mul_of_nonneg_right hend (by linarith)) ?_
  rw [mul_comm]
  exact le_intervalIntegral_of_logConcave hf0 hf huv hint

/-- **The one-dimensional isoperimetric inequality for log-concave densities**
(Kannan–Lovász–Simonovits 1995, Theorem 5.1), as an interface.

`π` assigns mass to subsets of `ℝ`; `sep` is a lower bound on the distance between the two
outer sets of the partition. The field `iso` is the inequality itself.

**This is an assumption, not a theorem** — see the file docstring. It is stated here so
that conductance arguments can be written against it and it can be discharged by a future
formalization without changing its consumers. The intended instance is the normalized
measure of an isotropic log-concave density (`Arlib.LogConcave`). -/
structure OneDimIsoperimetry (π : Set ℝ → ℝ) (c : ℝ) : Prop where
  /-- Mass is nonnegative. -/
  nonneg : ∀ S, 0 ≤ π S
  /-- The constant is positive. -/
  const_pos : 0 < c
  /-- **The isoperimetric inequality.** For a partition `S₁, S₂, S₃` of `ℝ` in which every
  point of `S₁` is at distance at least `sep` from every point of `S₂`, the middle set
  carries mass at least `c · sep · π S₁ · π S₂`. -/
  iso : ∀ (S₁ S₂ S₃ : Set ℝ) (sep : ℝ), 0 ≤ sep →
    π S₁ + π S₂ + π S₃ = 1 →
    (∀ u ∈ S₁, ∀ v ∈ S₂, sep ≤ |u - v|) →
    c * sep * π S₁ * π S₂ ≤ π S₃

/-- **The minimum form of the isoperimetric inequality**, which is what a conductance
argument consumes: the middle set carries mass at least a constant multiple of the smaller
side.

The constant degrades from `c · sep` to `(c · sep) / (2 + c · sep)` — the price of the
product-to-minimum conversion. -/
theorem OneDimIsoperimetry.min_form {π : Set ℝ → ℝ} {c : ℝ}
    (H : OneDimIsoperimetry π c) (S₁ S₂ S₃ : Set ℝ) {sep : ℝ} (hsep : 0 < sep)
    (hpart : π S₁ + π S₂ + π S₃ = 1)
    (hsep' : ∀ u ∈ S₁, ∀ v ∈ S₂, sep ≤ |u - v|) :
    (c * sep) / (2 + c * sep) * min (π S₁) (π S₂) ≤ π S₃ := by
  refine min_le_of_prod_le (mul_pos H.const_pos hsep)
    (H.nonneg _) (H.nonneg _) (H.nonneg _) hpart ?_
  have := H.iso S₁ S₂ S₃ sep hsep.le hpart hsep'
  linarith [this]

end Arlib
