/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.Isoperimetry
import Arlib.Convexity.Unimodal
import Mathlib.Data.Set.Pointwise.SMul

/-
# How the isoperimetric coefficient transforms under rescaling of the variable

Cousins–Vempala prove their isoperimetric inequality (`thm:iso`) only for the normalised
case and then write: *"by scaling down to increase the variance to exactly `1`, the
isoperimetric coefficient can only go down"*. This file is that step, formalised.

## The scaling direction, derived

Let `μ` be the law of a random variable `X` on `ℝ` and let `c > 0`. Write `c • S` for the
dilate `{c * x | x ∈ S}`. Then

  `μ' S := μ (c • S)`

is the law of `X / c`: indeed `X ∈ c • S ↔ X / c ∈ S`. Under this reparametrisation the
*masses are unchanged* (`μ'` of a set is by definition `μ` of its dilate) while *distances
are divided by `c`* (`|c*u - c*v| = c * |u - v|`, so a pair separated by `sep` in `μ'`-space
is separated by `c * sep` in `μ`-space). Feeding the larger separation `c * sep` into the
inequality for `μ` gives

  `k * (c * sep) * μ' S₁ * μ' S₂ ≤ μ' S₃`,

i.e. **`μ'` satisfies the inequality with coefficient `k * c`** (`OneDimIsoperimetry.smul`).

That fixes the direction: `X ↦ X / c` multiplies the coefficient by `c`. It also confirms
the paper's assertion, since `Var (X / c) = Var X / c²`: to *increase* the variance one
takes `c < 1`, and then `k * c < k` — the coefficient can only go down. The contrapositive
form is the one an argument actually consumes: knowing the inequality for the variance-`1`
rescaling `μ'` with an absolute constant `k` yields it for the original `μ` with the
*better* constant `k / c ≥ k` (`OneDimIsoperimetry.of_smul`), hence a fortiori with `k`
itself (`OneDimIsoperimetry.of_smul_le_one`).

The same scaling at the level of densities: if `f` is the density of `X`, then
`g x = c * f (c * x)` is the density of `X / c`, the `c` in front being the Jacobian that
keeps the total mass at `1`. The tail masses `A`, `B` are unchanged and
`∫ y in u..v, g y = ∫ x in c*u..c*v, f x`, while the separating interval `[u,v]` is `c`
times shorter than `[c*u, c*v]`; so again the coefficient is multiplied by `c`
(`iso_intervalIntegral_scale`).

## Main results

* `Arlib.OneDimIsoperimetry.smul` — the transfer lemma: if `μ` satisfies the
  one-dimensional isoperimetric inequality with coefficient `k`, then `S ↦ μ (c • S)`
  satisfies it with coefficient `k * c`.
* `Arlib.OneDimIsoperimetry.of_smul` — the inverse transfer, coefficient `k / c`.
* `Arlib.OneDimIsoperimetry.of_smul_le_one` — the paper's step verbatim: for `0 < c ≤ 1`
  the constant of the rescaled measure transfers back unchanged.
* `Arlib.OneDimIsoperimetry.mono` — the coefficient may be weakened.
* `Arlib.LogConcave.scaleDensity` — `x ↦ c * f (c * x)` is log-concave (via
  `Arlib.LogConcave.comp_affine` and `Arlib.LogConcave.const_smul`).
* `Arlib.intervalIntegral_scaleDensity` — `∫ y in a..b, c * f (c * y) = ∫ x in c*a..c*b, f x`.
* `Arlib.iso_intervalIntegral_scale` — the same `k ↦ k * c` transfer stated for the
  interval-integral form of the inequality.
* `Arlib.oneDim_iso_scaleDensity_of_endpoint_bound` — the composite with
  `Arlib.oneDim_iso_of_endpoint_bound`: an endpoint-density bound for `f` at `c*u`, `c*v`
  with constant `k` gives the isoperimetric inequality for the rescaled density with
  constant `k * c`.

## Scope

This file proves *only* the behaviour of the coefficient under `x ↦ c * x`. It is an exact
change of variables; it creates no isoperimetric information.

In particular the following are **not** proved here and must not be read into these
statements:

* **No reduction of a general log-concave density to the exponential extremal case.** The
  variational/localization argument that identifies the exponential as the extremal
  one-dimensional log-concave density is not formalised anywhere in this library; see
  `Arlib.Convexity.IsoExponential` for the extremal case itself, proved in isolation.
* **No instance of `Arlib.OneDimIsoperimetry` is constructed.** Every statement below is a
  transfer: it consumes a hypothesis of that form and produces another. The interface
  remains undischarged, exactly as documented in `Arlib.Convexity.Isoperimetry`.
* **No variance, no isotropy, no normalisation.** The phrase "scale so that the variance is
  `1`" is what motivates the lemmas, but the second moment of a measure is never mentioned
  in any statement; the caller must supply the scaling constant `c`. Nothing here says such
  a `c` exists, nor that `μ'` is a probability measure — the structure only requires the
  three masses of the partition at hand to sum to `1`.
* **No Lovász–Simonovits localization**, and nothing `n`-dimensional. Everything is on `ℝ`.
* **No integrability is established.** `Arlib.intervalIntegral_scaleDensity` is a change of
  variables valid because Mathlib's interval integral is defined for all functions; it does
  not assert that either side is the integral of an integrable function.
-/

namespace Arlib

open Real

open scoped Pointwise

/-! ## Transfer for the `OneDimIsoperimetry` interface -/

/-- **The coefficient may always be weakened.** An isoperimetric inequality with constant
`k` implies the one with any smaller positive constant, since the masses are nonnegative.

Recorded because the scaling lemmas below produce a constant of the form `k * c` or `k / c`
which one then wants to round off to a stated absolute constant. -/
theorem OneDimIsoperimetry.mono {μ : Set ℝ → ℝ} {k k' : ℝ} (H : OneDimIsoperimetry μ k)
    (hk' : 0 < k') (hkk : k' ≤ k) : OneDimIsoperimetry μ k' where
  nonneg := H.nonneg
  const_pos := hk'
  iso S₁ S₂ S₃ sep hsep hpart hsep' := by
    refine le_trans ?_ (H.iso S₁ S₂ S₃ sep hsep hpart hsep')
    have h₁ := H.nonneg S₁
    have h₂ := H.nonneg S₂
    have : k' * sep * μ S₁ ≤ k * sep * μ S₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkk hsep) h₁
    exact mul_le_mul_of_nonneg_right this h₂

/-- **The scaling transfer lemma.**

If `μ` satisfies the one-dimensional isoperimetric inequality with coefficient `k`, then the
dilated measure `S ↦ μ (c • S)` satisfies it with coefficient `k * c`, for every `c > 0`.

Probabilistically: if `μ` is the law of `X` then `S ↦ μ (c • S)` is the law of `X / c`, and
the map `X ↦ X / c` multiplies the isoperimetric coefficient by `c`. The mechanism is that
masses are preserved verbatim while a separation of `sep` between two sets becomes a
separation of `c * sep` between their dilates, so the inequality for `μ` may be applied with
the larger separation and the surplus factor `c` is absorbed into the constant.

Since `Var (X / c) = Var X / c²`, taking `c < 1` increases the variance and lowers the
coefficient — the monotonicity asserted (without proof) by Cousins–Vempala in the proof of
their isoperimetric theorem.

No hypothesis relates the three sets beyond what the structure already demands: they need
not partition `ℝ`, only their `μ`-masses need sum to `1`, and dilation by `c ≠ 0` preserves
that automatically since it does not change the masses at all. -/
theorem OneDimIsoperimetry.smul {μ : Set ℝ → ℝ} {k c : ℝ} (hc : 0 < c)
    (H : OneDimIsoperimetry μ k) :
    OneDimIsoperimetry (fun S => μ (c • S)) (k * c) where
  nonneg _ := H.nonneg _
  const_pos := mul_pos H.const_pos hc
  iso S₁ S₂ S₃ sep hsep hpart hsep' := by
    -- dilation multiplies every distance by `c`
    have hdil : ∀ u ∈ c • S₁, ∀ v ∈ c • S₂, c * sep ≤ |u - v| := by
      intro u hu v hv
      simp only [Set.mem_smul_set, smul_eq_mul] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      have habs : |c * u' - c * v'| = c * |u' - v'| := by
        rw [← mul_sub, abs_mul, abs_of_pos hc]
      rw [habs]
      exact mul_le_mul_of_nonneg_left (hsep' u' hu' v' hv') hc.le
    have key := H.iso (c • S₁) (c • S₂) (c • S₃) (c * sep) (mul_nonneg hc.le hsep) hpart hdil
    calc k * c * sep * μ (c • S₁) * μ (c • S₂)
        = k * (c * sep) * μ (c • S₁) * μ (c • S₂) := by ring
      _ ≤ μ (c • S₃) := key

/-- **The inverse scaling transfer.**

If the dilate `S ↦ μ (c • S)` satisfies the inequality with coefficient `k`, then `μ` itself
satisfies it with coefficient `k / c`.

This is the direction an argument consumes. One rescales an arbitrary measure to a normal
form (variance `1`, say), invokes the inequality there with its absolute constant `k`, and
transports the conclusion back to the measure one started with. Formally it is
`OneDimIsoperimetry.smul` applied with `c⁻¹`, using that dilating by `c⁻¹` and then by `c`
is the identity on sets. -/
theorem OneDimIsoperimetry.of_smul {μ : Set ℝ → ℝ} {k c : ℝ} (hc : 0 < c)
    (H : OneDimIsoperimetry (fun S => μ (c • S)) k) : OneDimIsoperimetry μ (k / c) := by
  have h := H.smul (inv_pos.mpr hc)
  have heq : (fun S : Set ℝ => μ (c • c⁻¹ • S)) = μ := by
    funext S
    rw [smul_inv_smul₀ (ne_of_gt hc)]
  rw [div_eq_mul_inv]
  simpa only [heq] using h

/-- **Cousins–Vempala's scaling step, verbatim.**

Suppose the measure has been *scaled down* by a factor `c ≤ 1` — the operation that
increases its variance, since `Var (X / c) = Var X / c²` — and suppose the rescaled measure
`S ↦ μ (c • S)` satisfies the isoperimetric inequality with coefficient `k`. Then the
original `μ` satisfies it with the same coefficient `k`.

"The isoperimetric coefficient can only go down": the honest constant for `μ` is `k / c ≥ k`
(`OneDimIsoperimetry.of_smul`), and this statement simply discards the improvement via
`OneDimIsoperimetry.mono`, which is what one does when the target is a fixed absolute
constant. -/
theorem OneDimIsoperimetry.of_smul_le_one {μ : Set ℝ → ℝ} {k c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : OneDimIsoperimetry (fun S => μ (c • S)) k) : OneDimIsoperimetry μ k := by
  have hk : 0 < k := H.const_pos
  refine (H.of_smul hc).mono hk ?_
  rw [le_div_iff₀ hc]
  nlinarith

/-! ## Transfer at the level of densities -/

/-- **The rescaled density is log-concave.**

If `f` is a nonnegative log-concave density then so is `x ↦ c * f (c * x)`, for `0 ≤ c`.
For `c > 0` and `f` a probability density this is exactly the density of `X / c`, the
leading `c` being the Jacobian of `x ↦ c * x`.

Both closure properties are already available: precomposition with the affine map
`x ↦ c * x + 0` is `LogConcave.comp_affine`, and multiplication by the constant `c` is
`LogConcave.const_smul`. -/
theorem LogConcave.scaleDensity {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun x => c * f (c * x)) := by
  have haff : LogConcave (fun x => f (c * x + 0)) := hf.comp_affine c 0
  simp only [add_zero] at haff
  exact LogConcave.const_smul hc (fun x => hf0 (c * x)) haff

/-- **The change of variables for the rescaled density.**

`∫ y in a..b, c * f (c * y) = ∫ x in c*a..c*b, f x`: the Jacobian factor `c` exactly
compensates the contraction of the domain, so the rescaled density assigns to `[a,b]` the
mass that `f` assigns to `[c*a, c*b]`. This is the "the normalised measure is unchanged"
half of the scaling; the "distances scale by `c`" half is the identity `c*b - c*a =
c * (b - a)`, used in `Arlib.iso_intervalIntegral_scale`.

No hypothesis on `c` (not even `c ≠ 0`) and no integrability hypothesis: both sides are
Mathlib's interval integral, which is defined — and equal to `0` — for non-integrable
functions, and the degenerate case `c = 0` makes both sides `0`. -/
theorem intervalIntegral_scaleDensity (f : ℝ → ℝ) (c a b : ℝ) :
    (∫ y in a..b, c * f (c * y)) = ∫ x in c * a..c * b, f x := by
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_left]

/-- **The `k ↦ k * c` transfer, stated for the interval-integral form of the inequality.**

Read `A` and `B` as the two tail masses; they are *unchanged* by the rescaling
(`intervalIntegral_scaleDensity` applied to the tails), which is why they appear on both
sides untouched. The hypothesis is the isoperimetric inequality for `f` on the interval
`[c*u, c*v]` with coefficient `k`; the conclusion is the inequality for the rescaled density
`y ↦ c * f (c * y)` on `[u, v]` with coefficient `k * c`.

The derivation is pure bookkeeping once `intervalIntegral_scaleDensity` is in hand: the two
middle masses are *equal*, and `(k * c) * (v - u) = k * (c*v - c*u)`. That equality is the
entire content of the scaling direction — the coefficient is multiplied by `c` precisely
because the separating interval got `c` times shorter while carrying the same mass. -/
theorem iso_intervalIntegral_scale {f : ℝ → ℝ} {c k A B u v : ℝ}
    (h : k * A * B * (c * v - c * u) ≤ ∫ x in c * u..c * v, f x) :
    k * c * A * B * (v - u) ≤ ∫ y in u..v, c * f (c * y) := by
  rw [intervalIntegral_scaleDensity]
  calc k * c * A * B * (v - u) = k * A * B * (c * v - c * u) := by ring
    _ ≤ ∫ x in c * u..c * v, f x := h

/-- **The composite with `Arlib.oneDim_iso_of_endpoint_bound`.**

An endpoint-density bound `k * A * B ≤ min (f (c*u)) (f (c*v))` for the original density `f`
at the rescaled endpoints yields the isoperimetric inequality for the rescaled density
`y ↦ c * f (c * y)` on `[u, v]`, with coefficient `k * c`.

This is the form in which the scaling composes with what
`Arlib.Convexity.Isoperimetry` already provides: the residual hypothesis of
`Arlib.oneDim_iso_of_endpoint_bound` — the half where the normalisation constant lives — is
transported across the rescaling by multiplying it by `c`, since
`min (c * f (c*u)) (c * f (c*v)) = c * min (f (c*u)) (f (c*v))` for `c ≥ 0`. The `k * c`
in the conclusion is therefore not an artefact of the bookkeeping: it is the *same* factor
`c` appearing in the endpoint bound and in the length of the interval.

Note that `hend` is *not* proved here for any `f`; see the scope section of the file
docstring. -/
theorem oneDim_iso_scaleDensity_of_endpoint_bound {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) {c k A B u v : ℝ} (hc : 0 < c) (huv : u ≤ v)
    (hint : IntervalIntegrable (fun y => c * f (c * y)) MeasureTheory.volume u v)
    (hend : k * A * B ≤ min (f (c * u)) (f (c * v))) :
    k * c * A * B * (v - u) ≤ ∫ y in u..v, c * f (c * y) := by
  have hg0 : ∀ x, 0 ≤ c * f (c * x) := fun x => mul_nonneg hc.le (hf0 _)
  have hg : LogConcave (fun x => c * f (c * x)) := LogConcave.scaleDensity hf0 hf hc.le
  have hend' : k * c * A * B ≤ min (c * f (c * u)) (c * f (c * v)) := by
    refine le_min ?_ ?_
    · calc k * c * A * B = c * (k * A * B) := by ring
        _ ≤ c * f (c * u) :=
            mul_le_mul_of_nonneg_left (le_trans hend (min_le_left _ _)) hc.le
    · calc k * c * A * B = c * (k * A * B) := by ring
        _ ≤ c * f (c * v) :=
            mul_le_mul_of_nonneg_left (le_trans hend (min_le_right _ _)) hc.le
  exact oneDim_iso_of_endpoint_bound hg0 hg huv hint hend'

end Arlib
