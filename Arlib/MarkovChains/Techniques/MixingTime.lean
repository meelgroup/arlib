/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Mixing time from the spectral gap

Everything in `Arlib.MarkovChains.Techniques` so far measures convergence in
`L²(μ)`: the spectral gap makes `Var_μ(P^t f)` and `D_{χ²}(ν P^t ‖ μ)` decay
geometrically.  What a sampling algorithm needs instead is a *uniform over
starting states* bound in total variation, and this module supplies the missing
link.  It is the formal counterpart of §3.5 of Zongchen Chen, Daniel Štefankovič,
Eric Vigoda, *Spectral Independence and Local-to-Global Techniques for Optimal
Mixing of Markov Chains*, arXiv:2307.13826 (2023) — cited below as [CSV23] — the
place where the analysis becomes an algorithmic guarantee.

The chain of reasoning is short because every analytic ingredient is already in
place.  Starting the chain at a state `x` means pushing forward the point mass
`δ_x`, whose χ²-divergence from `μ` is exactly `1/μ(x) - 1`; the χ²-divergence
contracts by `c²` per step; and Cauchy–Schwarz converts χ² into total variation.
The only genuinely new work is the arithmetic that turns `c^t` into a condition
on `t`.

* `FinDist.dirac` and `FinKernel.push_dirac` (both in `Techniques.Chain`) — the
  point mass, and the bridge
  `K.push δ_x = K.row x` between the `push`-phrased χ² machinery and the
  `row`-phrased `MixesWithin`.
* `chiSq_dirac` — `D_{χ²}(δ_x ‖ μ) = 1/μ(x) - 1`: the worst-case initial
  divergence, and the only place `μ(x)` enters the final bound.
* `chiSq_iter_le` — the iterated form of `chiSq_push_le`:
  `D_{χ²}(ν P^t ‖ μ) ≤ (c²)^t D_{χ²}(ν ‖ μ)`.
* `tvDist_iter_row_le` — **the mixing bound**:
  `‖P^t(x, ·) - μ‖_TV ≤ ½ c^t √(1/μ(x) - 1)`.
* `mixesWithin_of_bound`, `mixesWithin_of_log_le` — the same statement against
  `MixesWithin`, the second with an explicit sufficient condition on `t`.
* `tvDist_iter_row_lazy_le`, `mixesWithin_lazy_of_gap` — the user-facing form,
  stated in terms of the Poincaré constant `γ` rather than the absolute spectral
  bound: the lazy version of any reversible chain with spectral gap at least `γ`
  is `ε`-mixed once `(γ/2) · t ≥ ln(1 / (2 ε √μ_min))`.

No eigenvalue appears anywhere, here or upstream.  Everything here is proved
from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.TotalVariation
import Arlib.MarkovChains.Techniques.Lazy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The χ²-divergence of a point mass.**  `D_{χ²}(δ_x ‖ μ) = 1/μ(x) - 1`.

This is the worst-case initial divergence of a chain started deterministically,
and it is the only place the stationary mass of the starting state enters the
mixing-time bound. -/
theorem chiSq_dirac {μ : FinDist Ω} {x : Ω} (hx : 0 < μ x) :
    chiSq (FinDist.dirac x) μ = 1 / μ x - 1 := by
  have hac : ∀ y, μ y = 0 → FinDist.dirac x y = 0 := by
    intro y hy
    have hyx : y ≠ x := by rintro rfl; exact absurd hy hx.ne'
    simp [FinDist.dirac_apply, hyx]
  have hgx : relDensity (FinDist.dirac x) μ x = 1 / μ x := by
    simp [relDensity, hx.ne']
  have hgy : ∀ y, y ≠ x → relDensity (FinDist.dirac x) μ y = 0 := by
    intro y hy
    simp [relDensity, hy]
  rw [chiSq_eq_ip_sub_one hac, ip_apply]
  have hsum : ∑ y, μ y * relDensity (FinDist.dirac x) μ y * relDensity (FinDist.dirac x) μ y
      = 1 / μ x := by
    rw [Finset.sum_eq_single x (fun z _ hz => by rw [hgy z hz]; ring)
      (fun h => absurd (mem_univ x) h), hgx]
    field_simp
  rw [hsum]

/-! ## Iterated contraction of the χ²-divergence

`chiSq_push_le` contracts by `c²` in one step; iterating it is the same
induction as `Var_iter_le`, with `FinKernel.iter_succ'` supplying the
association that puts the *extra* step outermost. -/

/-- **Geometric decay of the χ²-divergence.**
`D_{χ²}(ν P^t ‖ μ) ≤ (c²)^t D_{χ²}(ν ‖ μ)` for a reversible chain obeying the
absolute spectral bound `c`.

No sign hypothesis on `c` is needed: only `c²` appears. -/
theorem chiSq_iter_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) (ν : FinDist Ω) (t : ℕ) :
    chiSq ((P.iter t).push ν) μ ≤ (c ^ 2) ^ t * chiSq ν μ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.iter_succ', FinKernel.push_comp]
      calc chiSq (P.push ((P.iter t).push ν)) μ
          ≤ c ^ 2 * chiSq ((P.iter t).push ν) μ := chiSq_push_le hrev hpos hc
        _ ≤ c ^ 2 * ((c ^ 2) ^ t * chiSq ν μ) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (c ^ 2) ^ (t + 1) * chiSq ν μ := by ring

/-! ## The mixing bound -/

/-- **Mixing time from the spectral gap.**  For a chain `P` reversible with
respect to a fully supported `μ` and obeying the absolute spectral bound
`c ≥ 0`, the law after `t` steps started at `x` satisfies

  `‖P^t(x, ·) - μ‖_TV ≤ ½ · c^t · √(1/μ(x) - 1)`.

Three facts combine: the initial χ²-divergence from a point start is
`1/μ(x) - 1` (`chiSq_dirac`), the χ²-divergence contracts by `c²` per step
(`chiSq_iter_le`), and total variation is controlled by the square root of the
χ²-divergence (`tvDist_le_sqrt_chiSq`). -/
theorem tvDist_iter_row_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c)
    (x : Ω) (t : ℕ) :
    tvDist ((P.iter t).row x) μ ≤ (1 / 2) * c ^ t * Real.sqrt (1 / μ x - 1) := by
  set ν : FinDist Ω := (P.iter t).push (FinDist.dirac x)
  have hrow : (P.iter t).row x = ν := (FinKernel.push_dirac _ x).symm
  have hac : ∀ y, μ y = 0 → ν y = 0 := fun y hy => absurd hy (hpos y).ne'
  -- the χ²-divergence after `t` steps
  have hchi : chiSq ν μ ≤ (c ^ 2) ^ t * (1 / μ x - 1) := by
    have := chiSq_iter_le hrev hpos hc (FinDist.dirac x) t
    rwa [chiSq_dirac (hpos x)] at this
  -- take square roots
  have hsqrt : Real.sqrt ((c ^ 2) ^ t * (1 / μ x - 1))
      = c ^ t * Real.sqrt (1 / μ x - 1) := by
    rw [show (c ^ 2) ^ t = (c ^ t) ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (pow_nonneg hc0 t)]
  have hmono : Real.sqrt (chiSq ν μ) ≤ c ^ t * Real.sqrt (1 / μ x - 1) := by
    rw [← hsqrt]; exact Real.sqrt_le_sqrt hchi
  have hstep : tvDist ν μ ≤ (1 / 2) * Real.sqrt (chiSq ν μ) := tvDist_le_sqrt_chiSq hac
  rw [hrow]
  linarith

/-! ## Stated against `MixesWithin` -/

/-- The mixing bound in the form of `MixesWithin`: if the bound of
`tvDist_iter_row_le` is at most `ε` at every state, the chain is `ε`-mixed after
`t` steps. -/
theorem mixesWithin_of_bound {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c)
    {ε : ℝ} {t : ℕ} (h : ∀ x, (1 / 2) * c ^ t * Real.sqrt (1 / μ x - 1) ≤ ε) :
    MixesWithin P μ ε t :=
  fun x => (tvDist_iter_row_le hrev hpos hc hc0 x t).trans (h x)

/-- **An explicit mixing time.**  If `μ` is bounded below by `m > 0` and the
absolute spectral bound is `c ∈ [0, 1]`, then the chain is `ε`-mixed after `t`
steps as soon as

  `ln (1 / (2 ε √m)) ≤ (1 - c) · t`,

i.e. after `t ≥ (1 - c)⁻¹ ln(1 / (2 ε √m))` steps.  This is the
`Tmix(ε) ≤ γ⁻¹ ln(1 / (ε √μ_min))` bound of the monograph, with the constants
that the elementary route actually delivers.

The exponential inversion is the one-line inequality `c ≤ exp(c - 1)`
(`Real.add_one_le_exp`), raised to the `t`-th power; no logarithm of `c` is
taken, so no lower bound on `c` is needed. -/
theorem mixesWithin_of_log_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c)
    {m ε : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (2 * ε * Real.sqrt m)) ≤ (1 - c) * t) :
    MixesWithin P μ ε t := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hA : 0 < 2 * ε * Real.sqrt m := by positivity
  -- `c^t ≤ 2 ε √m`, by way of `c ≤ exp (c - 1)`.
  have hct : c ^ t ≤ 2 * ε * Real.sqrt m := by
    have h1 : c ≤ Real.exp (c - 1) := by
      have := Real.add_one_le_exp (c - 1); linarith
    have h2 : c ^ t ≤ Real.exp (c - 1) ^ t := pow_le_pow_left₀ hc0 h1 t
    have h3 : Real.exp ((t : ℝ) * (c - 1)) = Real.exp (c - 1) ^ t :=
      Real.exp_nat_mul (c - 1) t
    have h4 : (t : ℝ) * (c - 1) ≤ Real.log (2 * ε * Real.sqrt m) := by
      rw [one_div, Real.log_inv] at ht
      have hid : (t : ℝ) * (c - 1) = -((1 - c) * (t : ℝ)) := by ring
      linarith
    calc c ^ t ≤ Real.exp ((t : ℝ) * (c - 1)) := by rw [h3]; exact h2
      _ ≤ Real.exp (Real.log (2 * ε * Real.sqrt m)) := Real.exp_le_exp.mpr h4
      _ = 2 * ε * Real.sqrt m := Real.exp_log hA
  refine mixesWithin_of_bound hrev hpos hc hc0 fun x => ?_
  -- `√(1/μ x - 1) ≤ 1/√m`
  have hSx : Real.sqrt (1 / μ x - 1) ≤ (Real.sqrt m)⁻¹ := by
    have hinv : 1 / μ x ≤ 1 / m := one_div_le_one_div_of_le hm (hmin x)
    have h1 : 1 / μ x - 1 ≤ m⁻¹ := by rw [← one_div]; linarith
    calc Real.sqrt (1 / μ x - 1) ≤ Real.sqrt m⁻¹ := Real.sqrt_le_sqrt h1
      _ = (Real.sqrt m)⁻¹ := Real.sqrt_inv m
  have hS0 : 0 ≤ Real.sqrt (1 / μ x - 1) := Real.sqrt_nonneg _
  have hct0 : 0 ≤ c ^ t := pow_nonneg hc0 t
  calc (1 / 2) * c ^ t * Real.sqrt (1 / μ x - 1)
      ≤ (1 / 2) * (2 * ε * Real.sqrt m) * Real.sqrt (1 / μ x - 1) := by nlinarith
    _ ≤ (1 / 2) * (2 * ε * Real.sqrt m) * (Real.sqrt m)⁻¹ := by nlinarith
    _ = ε := by field_simp; ring

/-! ## The user-facing form: mixing from a Poincaré constant

A general reversible chain need not converge at all — a bipartite chain
alternates forever — so the Poincaré inequality alone cannot bound the mixing
time.  Laziness repairs this (`lazy_nonnegDefinite`) at the cost of exactly a
factor two in the gap, and the resulting statement mentions only `γ`. -/

/-- **Mixing of the lazy chain from the Poincaré constant.**  For any chain `P`
reversible with respect to a fully supported `μ` and satisfying the Poincaré
inequality with constant `γ ≤ 2`,

  `‖P_lazy^t(x, ·) - μ‖_TV ≤ ½ (1 - γ/2)^t √(1/μ(x) - 1)`.

No ergodicity hypothesis, no aperiodicity hypothesis, and no eigenvalue. -/
theorem tvDist_iter_row_lazy_le {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 2) (x : Ω) (t : ℕ) :
    tvDist ((P.lazy.iter t).row x) μ
      ≤ (1 / 2) * (1 - γ / 2) ^ t * Real.sqrt (1 / μ x - 1) :=
  tvDist_iter_row_le (lazy_reversible hrev) hpos
    (absSpectralBound_of_gap (lazy_nonnegDefinite hrev.stationary)
      (lazy_spectralGapAtLeast hgap) (by linarith)) (by linarith) x t

/-- **The mixing-time bound.**  Let `P` be reversible with respect to `μ`, let
`μ` be bounded below by `m > 0`, and let `P` satisfy the Poincaré inequality
with constant `γ ≤ 2`.  Then the lazy chain `P_lazy` is `ε`-mixed after `t`
steps whenever

  `ln (1 / (2 ε √m)) ≤ (γ/2) · t`,

that is, after `t ≥ (2/γ) · ln(1 / (2 ε √m))` steps.  Compare
[CSV23, §3.5]: the monograph's `Tmix ≤ (2γ)⁻¹ ln(4/μ*)` differs only in
constants, the factor two coming from laziness. -/
theorem mixesWithin_lazy_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 2)
    {m ε : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (2 * ε * Real.sqrt m)) ≤ (γ / 2) * t) :
    MixesWithin P.lazy μ ε t :=
  mixesWithin_of_log_le (lazy_reversible hrev) hpos
    (absSpectralBound_of_gap (lazy_nonnegDefinite hrev.stationary)
      (lazy_spectralGapAtLeast hgap) (by linarith)) (by linarith) hm hmin hε
    (by rw [show (1 : ℝ) - (1 - γ / 2) = γ / 2 by ring]; exact ht)

end Arlib.MarkovChains
