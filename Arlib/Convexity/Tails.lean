/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.LogConcave
import Mathlib.Analysis.SpecificLimits.Basic

/-
# Exponential tail decay of log-concave functions on `ℝ`

A log-concave function cannot have a heavy tail: once it has dropped, it keeps dropping at
least geometrically. Concretely, `log f` is concave, so its slope is nonincreasing, and the
drop from `f u` to `f v` is therefore repeated — at least — over every further step of the
same length. Everything in this file is that one sentence, made quantitative.

The engine is the defining inequality at `t = 1/2`: for the midpoint `v = (u + w)/2`,

  `f u * f w ≤ f v ^ 2`,

i.e. the value at the midpoint dominates the geometric mean of the two ends. Rearranged
(when `f u > 0`) this reads `f w ≤ f v ^ 2 / f u = f u * (f v / f u) ^ 2`: one step past
`v` costs another factor of the ratio `f v / f u`.

Iterating is not done by induction here. The defining inequality applied at `t = 1/s`
gives the `s`-step bound in one shot, for *real* `s ≥ 1`:

  `f (u + s * (v - u)) ≤ f u * (f v / f u) ^ s`   (`Real.rpow`),

since `v = (1 - 1/s) * u + (1/s) * (u + s * (v - u))` exhibits `v` as a convex combination
of `u` and the far point. Note that this needs **no** hypothesis `f v ≤ f u` and no
ordering of `u` and `v`: it is an identity of convex combinations. When `f v ≤ f u` the
ratio is `≤ 1` and the bound is genuine geometric decay; when `f v > f u` it is a (true but
vacuous-looking) growth bound in the direction where `f` is increasing.

## Main results

* `Arlib.LogConcave.mul_le_sq_midpoint` — `f u * f w ≤ f ((u + w) / 2) ^ 2`, the midpoint
  (geometric-mean) inequality. This is the one-step engine, and it needs no positivity.
* `Arlib.LogConcave.le_sq_div` — its rearrangement `f (2 * v - u) ≤ f v ^ 2 / f u` for
  `f u > 0`: reflecting `u` through `v` multiplies the value by at most `f v / f u`.
* `Arlib.LogConcave.le_mul_rpow_ratio` — the `s`-step bound
  `f (u + s * (v - u)) ≤ f u * (f v / f u) ^ s` for real `s ≥ 1`.
* `Arlib.LogConcave.le_mul_rpow_ratio_beyond` — the same statement parametrised from `v`
  instead of `u`: `f (v + t * (v - u)) ≤ f u * (f v / f u) ^ (1 + t)` for `t ≥ 0`.
* `Arlib.LogConcave.le_mul_pow_ratio` — the discrete version
  `f (u + k * (v - u)) ≤ f u * (f v / f u) ^ k` for `k : ℕ` (ordinary `Monoid.npow`; the
  case `k = 0` is trivially included).
* `Arlib.LogConcave.le_mul_exp_neg` — the literal exponential form: for `f u, f v > 0`,
  `f (u + s * (v - u)) ≤ f u * exp (-(log (f u / f v) * s))`. The rate `log (f u / f v)` is
  `≥ 0` exactly when `f v ≤ f u` (`Real.log_nonneg`), and `> 0` when `f v < f u`
  (`Real.log_pos`), which is what "decays at least exponentially" means.
* `Arlib.LogConcave.tendsto_atTop_nhds_zero` — the qualitative consequence: if
  `f v < f u` then `f (u + k * (v - u)) → 0` as `k → ∞` along `ℕ`.

## Scope

**This file does not prove `hend`.** The residual hypothesis of
`Arlib.oneDim_iso_of_endpoint_bound` in `Arlib.Convexity.Isoperimetry` is
`c * A * B ≤ min (f u) (f v)`, where `A` and `B` are the two *tail masses*
`∫_{-∞}^u f` and `∫_v^∞ f`. Bounding a tail mass by the endpoint density is exactly an
integration of the decay estimates proved here — `B = ∫_v^∞ f ≤ f v · (something)/rate`
after substituting the geometric bound — and that integration step, together with the
normalisation (the isotropy / `E|x|` constant of Kannan–Lovász–Simonovits) that converts
the resulting rate into an absolute constant, is **not** carried out here. What is supplied
is the pointwise decay estimate that such an argument consumes.

Also absent:

* **No integrability, no integrals.** Nothing here says a log-concave function is
  measurable or that its tail integral converges (both true, and both derivable from the
  bounds here plus Mathlib's comparison tests, but neither is proved).
* **No two-sided statement.** The bounds are along the ray from `u` through `v`. The mirror
  statement on the other side follows by `Arlib.LogConcave.comp_neg`, but is not spelled
  out.
* **No sharpness.** The exponential density (`Arlib.Convexity.IsoExponential`) shows the
  rate cannot be improved in general, but no extremality statement is proved.
-/

namespace Arlib

open Real

/-- **The midpoint inequality**: the value of a log-concave function at the midpoint
dominates the geometric mean of the values at the two ends,

  `f u * f w ≤ f ((u + w) / 2) ^ 2`.

This is the defining inequality at `t = 1/2`, squared, and it is the engine behind every
other statement in this file: a log-concave function's values along an arithmetic
progression are log-concave as a sequence, so the successive ratios are nonincreasing.

No positivity of `f u` is needed — if `f u = 0` both sides are handled by the same
computation. -/
theorem LogConcave.mul_le_sq_midpoint {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    (u w : ℝ) : f u * f w ≤ f ((u + w) / 2) ^ 2 := by
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hmid : (1 - 1 / 2 : ℝ) * u + (1 / 2) * w = (u + w) / 2 := by ring
  have h := hf u w (1 / 2) (by norm_num) (by norm_num)
  rw [hmid, hhalf] at h
  -- `h : f u ^ (1/2) * f w ^ (1/2) ≤ f ((u + w) / 2)`; now square it.
  have hsq : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
    norm_num
  calc f u * f w = (f u ^ (1 / 2 : ℝ) * f w ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [mul_pow, hsq _ (hf0 u), hsq _ (hf0 w)]
    _ ≤ f ((u + w) / 2) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg (Real.rpow_nonneg (hf0 u) _) (Real.rpow_nonneg (hf0 w) _)) h 2

/-- **The one-step ratio bound**: reflecting `u` through `v` costs a factor `f v / f u`.

For `f u > 0`, `f (2 * v - u) ≤ f v ^ 2 / f u`. Since `f v ^ 2 / f u = f u * (f v / f u) ^ 2`,
this says the value one step beyond `v` is at most the value at `v` times the ratio
`f v / f u` already realised over `[u, v]` — the geometric-decay step. It is
`LogConcave.mul_le_sq_midpoint` at `w = 2 * v - u`, for which `v` is the midpoint. -/
theorem LogConcave.le_sq_div {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v : ℝ} (hu : 0 < f u) : f (2 * v - u) ≤ f v ^ 2 / f u := by
  have h := hf.mul_le_sq_midpoint hf0 u (2 * v - u)
  have hmid : (u + (2 * v - u)) / 2 = v := by ring
  rw [hmid] at h
  rw [le_div_iff₀ hu]
  linarith

/-- **Geometric decay along a ray, real exponent.**

If `f u > 0` then for every `s ≥ 1`

  `f (u + s * (v - u)) ≤ f u * (f v / f u) ^ s`   (`Real.rpow`).

The point `u + s * (v - u)` is the point at distance `s` steps from `u` in the direction of
`v`, so with `r := f v / f u` the bound says the value decays like `r ^ s`. When `f v ≤ f u`
we have `r ≤ 1` and this is genuine exponential decay (see `LogConcave.le_mul_exp_neg` for
the same statement written with `exp`).

The proof is a single application of the definition rather than an induction: `v` is the
convex combination `(1 - 1/s) * u + (1/s) * (u + s * (v - u))`, so log-concavity at
`t = 1/s` gives `f u ^ (1 - 1/s) * f (u + s * (v - u)) ^ (1/s) ≤ f v`, and raising to the
power `s` and dividing by `f u ^ (s - 1)` is the claim. In particular no hypothesis
`f v ≤ f u` and no ordering of `u` and `v` is required. -/
theorem LogConcave.le_mul_rpow_ratio {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v : ℝ} (hu : 0 < f u) {s : ℝ} (hs : 1 ≤ s) :
    f (u + s * (v - u)) ≤ f u * (f v / f u) ^ s := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hune : f u ≠ 0 := ne_of_gt hu
  have ht0 : (0 : ℝ) ≤ 1 / s := by positivity
  have ht1 : 1 / s ≤ 1 := by rw [div_le_one hs0]; exact hs
  have hinv : (1 / s) * s = 1 := by field_simp
  -- `v` is a convex combination of `u` and the far point.
  have hcomb : (1 - 1 / s) * u + (1 / s) * (u + s * (v - u)) = v := by
    have hexp : (1 - 1 / s) * u + (1 / s) * (u + s * (v - u))
        = u + ((1 / s) * s) * (v - u) := by ring
    rw [hexp, hinv, one_mul]
    ring
  have h := hf u (u + s * (v - u)) (1 / s) ht0 ht1
  rw [hcomb] at h
  -- raise to the power `s`
  have hnn : 0 ≤ f u ^ (1 - 1 / s) * f (u + s * (v - u)) ^ (1 / s) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg (hf0 _) _)
  have h2 : (f u ^ (1 - 1 / s) * f (u + s * (v - u)) ^ (1 / s)) ^ s ≤ f v ^ s :=
    Real.rpow_le_rpow hnn h hs0.le
  rw [Real.mul_rpow (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg (hf0 _) _),
    ← Real.rpow_mul hu.le, ← Real.rpow_mul (hf0 _)] at h2
  have e1 : (1 - 1 / s) * s = s - 1 := by field_simp
  rw [e1, hinv, Real.rpow_one] at h2
  -- `h2 : f u ^ (s - 1) * f (u + s * (v - u)) ≤ f v ^ s`
  have hp : (0 : ℝ) < f u ^ (s - 1) := Real.rpow_pos_of_pos hu _
  have hps : (0 : ℝ) < f u ^ s := Real.rpow_pos_of_pos hu _
  have hrw : f u * (f v / f u) ^ s = f v ^ s / f u ^ (s - 1) := by
    rw [Real.div_rpow (hf0 v) hu.le, Real.rpow_sub hu, Real.rpow_one]
    field_simp
    ring
  rw [hrw, le_div_iff₀ hp]
  linarith

/-- **Geometric decay measured from `v`.**

The restatement of `LogConcave.le_mul_rpow_ratio` in which the base point of the ray is `v`
rather than `u`: for `t ≥ 0`,

  `f (v + t * (v - u)) ≤ f u * (f v / f u) ^ (1 + t)`.

This is the form in which the decay is usually quoted — "`t` further steps past `v` cost
`t` further factors of the ratio" — and it is the case `s = 1 + t` of the previous theorem,
using `u + (1 + t) * (v - u) = v + t * (v - u)`. At `t = 0` it degenerates to `f v ≤ f v`. -/
theorem LogConcave.le_mul_rpow_ratio_beyond {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) {u v : ℝ} (hu : 0 < f u) {t : ℝ} (ht : 0 ≤ t) :
    f (v + t * (v - u)) ≤ f u * (f v / f u) ^ (1 + t) := by
  have h := hf.le_mul_rpow_ratio hf0 hu (v := v) (s := 1 + t) (by linarith)
  have hpt : u + (1 + t) * (v - u) = v + t * (v - u) := by ring
  rwa [hpt] at h

/-- **Geometric decay along a ray, integer exponent.**

For every `k : ℕ`,

  `f (u + k * (v - u)) ≤ f u * (f v / f u) ^ k`

with the ordinary monoid power on the right. This is `LogConcave.le_mul_rpow_ratio` at
`s = k` for `k ≥ 1`, plus the trivial case `k = 0`; it is the form an induction over
successive intervals of equal length consumes, and the form that feeds
`LogConcave.tendsto_atTop_nhds_zero`. -/
theorem LogConcave.le_mul_pow_ratio {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v : ℝ} (hu : 0 < f u) (k : ℕ) :
    f (u + k * (v - u)) ≤ f u * (f v / f u) ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h := hf.le_mul_rpow_ratio hf0 hu (v := v) hk1
    rwa [Real.rpow_natCast] at h

/-- **The exponential form of the decay.**

If `f u > 0` and `f v > 0` then for every `s ≥ 1`

  `f (u + s * (v - u)) ≤ f u * exp (-(log (f u / f v) * s))`.

This is `LogConcave.le_mul_rpow_ratio` with the ratio written as an exponential, and it is
the statement "a log-concave function decays at least exponentially away from a point where
it is large" in its literal form: the decay rate is `log (f u / f v)`, the log-drop realised
over the single interval `[u, v]`, and it is not improved as one moves out — it is repeated.

The rate is nonnegative exactly when `f v ≤ f u` (`Real.log_nonneg` applied to
`1 ≤ f u / f v`) and strictly positive when `f v < f u` (`Real.log_pos`); those two facts
are pure `Real.log` arithmetic and are left to the caller, since the inequality above holds
regardless of the sign. -/
theorem LogConcave.le_mul_exp_neg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v : ℝ} (hu : 0 < f u) (hv : 0 < f v) {s : ℝ} (hs : 1 ≤ s) :
    f (u + s * (v - u)) ≤ f u * Real.exp (-(Real.log (f u / f v) * s)) := by
  have h := hf.le_mul_rpow_ratio hf0 hu (v := v) hs
  have hratio : (0 : ℝ) < f v / f u := div_pos hv hu
  have hlog : Real.log (f v / f u) = -Real.log (f u / f v) := by
    rw [← Real.log_inv]
    congr 1
    rw [inv_div]
  rw [Real.rpow_def_of_pos hratio, hlog, neg_mul] at h
  exact h

/-- **The qualitative tail statement**: a log-concave function that has strictly decreased
from `u` to `v` tends to `0` along the arithmetic progression `u + k * (v - u)`.

The immediate consequence of `LogConcave.le_mul_pow_ratio` and the convergence of the
geometric series ratio `f v / f u < 1`, squeezed against nonnegativity of `f`. It is stated
along `ℕ` because that is what the geometric bound is indexed by; the corresponding
statement along `ℝ` follows from `LogConcave.le_mul_rpow_ratio` in the same way but is not
needed downstream. -/
theorem LogConcave.tendsto_atTop_nhds_zero {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) {u v : ℝ} (hu : 0 < f u) (hlt : f v < f u) :
    Filter.Tendsto (fun k : ℕ => f (u + k * (v - u))) Filter.atTop (nhds 0) := by
  have hr0 : 0 ≤ f v / f u := div_nonneg (hf0 v) hu.le
  have hr1 : f v / f u < 1 := (div_lt_one hu).2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => f u * (f v / f u) ^ k) Filter.atTop (nhds 0) := by
    have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using hgeom.const_mul (f u)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => hf0 _) (fun k => hf.le_mul_pow_ratio hf0 hu k)

end Arlib
