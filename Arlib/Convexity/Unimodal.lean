/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.LogConcave

/-
# Unimodality and the structural calculus of log-concave functions on `ℝ`

`Arlib.Convexity.LogConcave` defines log-concavity and proves the two facts the
definition is *for*: closure under products, and the pointwise unimodality bound
`min (f u) (f v) ≤ f t` for `t` between `u` and `v`. This file supplies the structural
layer around it — the shape of the level sets, and closure under the coordinate changes
that one-dimensional arguments actually perform.

Both halves are what the reduction to the one-dimensional isoperimetric inequality of
`Arlib.Convexity.Isoperimetry` needs. That reduction is a statement about a partition of
a *line*: it localizes an `n`-dimensional log-concave density to a chord, and then argues
about the interval structure of the resulting one-dimensional density.

* Localizing to a chord is exactly precomposition with an affine map `x ↦ a * x + b`, so
  `LogConcave.comp_affine` is what makes "restrict to the line through `p` and `q`" a
  legal move; `LogConcave.const_smul` is what makes renormalizing the restricted density
  a legal move.
* Arguing about the interval structure needs to know that the sets
  `{x | c ≤ f x}` are intervals — that a log-concave density has no second bump, so a
  set separating two others really is a middle segment. `convex_superlevel` (equivalently
  `ordConnected_superlevel`) is that fact, and it is precisely *quasi-concavity*: it is
  weaker than log-concavity, and is the only consequence of log-concavity used by the
  interval bookkeeping.

## Main results

* `Arlib.LogConcave.convex_superlevel` — every superlevel set `{x | c ≤ f x}` is convex,
  i.e. a log-concave function is quasi-concave.
* `Arlib.LogConcave.ordConnected_superlevel` — the same fact repackaged as
  `Set.OrdConnected`, which is the form order-theoretic interval arguments consume.
* `Arlib.LogConcave.convex_pos` and `Arlib.LogConcave.convex_support` — the support of a
  nonnegative log-concave function is convex: it does not vanish strictly between two
  points where it is positive.
* `Arlib.LogConcave.pos_of_mem_Icc` — the pointwise form of the previous statement.
* `Arlib.LogConcave.comp_affine`, `Arlib.LogConcave.comp_neg` — log-concavity is
  preserved by precomposition with an affine map.
* `Arlib.LogConcave.const_smul` — log-concavity is preserved by scaling by a nonnegative
  constant.
* `Arlib.LogConcave.rpow` — log-concavity is preserved by `f ↦ f ^ p` for `p ≥ 0`.

## What this file does NOT prove

* **No converse.** Quasi-concavity does not imply log-concavity (`x ↦ 1 + |x|⁻¹` on a
  ray, or any increasing function with a badly convex logarithm, is a counterexample), so
  `convex_superlevel` is a genuine one-way weakening.
* **No topological or measurability content.** Nothing here says a superlevel set is
  *closed* or *bounded*, only that it is convex; nothing says a log-concave function is
  continuous on the interior of its support (true, but a separate argument), measurable,
  or integrable.
* **No sums, no integrals.** Log-concavity is *not* preserved by addition, and the two
  deep closure properties — that a marginal of a log-concave function is log-concave, and
  that a convolution of log-concave functions is log-concave — are Prékopa–Leindler, which
  is not available in Mathlib `v4.15` and is not proved here.
* **No differentiability characterisation**, i.e. no `f'' * f ≤ (f')ˆ2` criterion.
-/

namespace Arlib

open Real

/-- **Log-concave implies quasi-concave**: every superlevel set `{x | c ≤ f x}` of a
nonnegative log-concave function is convex.

Concretely, a log-concave density has no valley: it cannot exceed the threshold `c` at two
points and dip below it in between, so `{x | c ≤ f x}` is an interval rather than a union
of several. This is the "one bump" shape that lets a one-dimensional isoperimetric
argument treat the separating set as a single middle segment.

For `c ≤ 0` the statement is nonnegativity of `f`; for `c > 0` it is the defining
inequality applied after writing `c = c ^ (1 - t) * c ^ t`. Note that this is a strictly
weaker property than log-concavity — the converse fails. -/
theorem LogConcave.convex_superlevel {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    (c : ℝ) : Convex ℝ {x : ℝ | c ≤ f x} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, smul_eq_mul] at hx hy ⊢
  have hae : a = 1 - b := by linarith
  subst hae
  have hb1 : b ≤ 1 := by linarith
  rcases le_or_lt c 0 with hc | hc
  · exact le_trans hc (hf0 _)
  · calc c = c ^ (1 - b) * c ^ b := by rw [← Real.rpow_add hc]; simp
      _ ≤ f x ^ (1 - b) * f y ^ b :=
          mul_le_mul (Real.rpow_le_rpow hc.le hx (by linarith))
            (Real.rpow_le_rpow hc.le hy hb) (Real.rpow_nonneg hc.le _)
            (Real.rpow_nonneg (hf0 x) _)
      _ ≤ f ((1 - b) * x + b * y) := hf x y b hb hb1

/-- The superlevel sets of a nonnegative log-concave function are **order-connected**:
if `c ≤ f u` and `c ≤ f v` then `c ≤ f t` for every `t ∈ [u, v]`.

This is `LogConcave.convex_superlevel` restated through `Convex.ordConnected`, which over
a linear ordered field are equivalent. The order-theoretic form is the one that composes
with `Set.Icc`-style interval reasoning without having to produce the convex-combination
witness by hand. -/
theorem LogConcave.ordConnected_superlevel {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) (c : ℝ) : {x : ℝ | c ≤ f x}.OrdConnected :=
  (hf.convex_superlevel hf0 c).ordConnected

/-- **The positivity set of a log-concave function is convex.**

A log-concave function that is positive at two points is positive on the whole segment
between them: a strict zero cannot separate two positive values. Unlike
`convex_superlevel` this needs no nonnegativity hypothesis, since the product
`f x ^ (1 - t) * f y ^ t` of two positive powers is already positive. -/
theorem LogConcave.convex_pos {f : ℝ → ℝ} (hf : LogConcave f) :
    Convex ℝ {x : ℝ | 0 < f x} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, smul_eq_mul] at hx hy ⊢
  have hae : a = 1 - b := by linarith
  subst hae
  have hb1 : b ≤ 1 := by linarith
  exact lt_of_lt_of_le
    (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)) (hf x y b hb hb1)

/-- **The support of a nonnegative log-concave function is convex**, hence an interval.

This is the reason log-concave densities are the right class for convex-geometry
arguments: the region where the density lives is itself a convex body, so a statement
about a log-concave density on `ℝ` is a statement about a density on an interval. For a
nonnegative function `Function.support f` and `{x | 0 < f x}` coincide, so this is
`LogConcave.convex_pos` transported along that identification. -/
theorem LogConcave.convex_support {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f) :
    Convex ℝ (Function.support f) := by
  have hsupp : Function.support f = {x : ℝ | 0 < f x} := by
    ext x
    simp only [Function.mem_support, Set.mem_setOf_eq]
    exact ⟨fun hx => lt_of_le_of_ne (hf0 x) (Ne.symm hx), fun hx => ne_of_gt hx⟩
  rw [hsupp]
  exact hf.convex_pos

/-- **No interior zeros**: a nonnegative log-concave function that is positive at the two
endpoints of an interval is positive throughout it.

The pointwise companion of `LogConcave.convex_support`, obtained from the unimodality
bound `min (f u) (f v) ≤ f t` of `LogConcave.min_le_of_mem_Icc`. This is the form used
when one needs to divide by `f t` at an unspecified interior point. -/
theorem LogConcave.pos_of_mem_Icc {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f)
    {u v t : ℝ} (hu : 0 < f u) (hv : 0 < f v) (ht : t ∈ Set.Icc u v) : 0 < f t :=
  lt_of_lt_of_le (lt_min hu hv) (hf.min_le_of_mem_Icc hf0 ht)

/-- **Log-concavity is preserved by affine reparametrisation**: if `f` is log-concave then
so is `x ↦ f (a * x + b)`, for any `a b : ℝ`.

This is the localization move. An `n`-dimensional log-concave density restricted to the
line `s ↦ p + s • (q - p)` is a one-dimensional log-concave function, and in one dimension
that restriction is precisely precomposition with `x ↦ a * x + b`; every reduction of a
higher-dimensional isoperimetric statement to the one-dimensional one passes through it.

The proof is the identity `a * ((1-t) * x + t * y) + b = (1-t) * (a*x + b) + t * (a*y + b)`,
which holds because the affine map sends convex combinations to convex combinations — the
`b` reassembles since `(1-t) + t = 1`. No hypothesis on `a` or `b` is needed, and in
particular no nonnegativity of `f`: the degenerate case `a = 0` reduces to the defining
inequality of `f` at the single point `b`. -/
theorem LogConcave.comp_affine {f : ℝ → ℝ} (hf : LogConcave f) (a b : ℝ) :
    LogConcave (fun x => f (a * x + b)) := by
  intro x y t ht0 ht1
  simp only
  have key : a * ((1 - t) * x + t * y) + b = (1 - t) * (a * x + b) + t * (a * y + b) := by
    ring
  rw [key]
  exact hf (a * x + b) (a * y + b) t ht0 ht1

/-- **Log-concavity is preserved by reflection**: `x ↦ f (-x)` is log-concave.

The case `a = -1`, `b = 0` of `LogConcave.comp_affine`, isolated because symmetrization
arguments on the line use it directly: it is what lets one assume without loss of
generality that a distinguished point lies to the left. -/
theorem LogConcave.comp_neg {f : ℝ → ℝ} (hf : LogConcave f) : LogConcave (fun x => f (-x)) := by
  have h := hf.comp_affine (-1) 0
  simpa using h

/-- **Log-concavity is preserved by scaling by a nonnegative constant.**

Needed for renormalization: after restricting a log-concave density to a chord one divides
by the total mass along that chord to get a probability density, and this says the result
is still log-concave. Since `c = 0` is allowed, it also covers the degenerate case where
the chord carries no mass.

This is `LogConcave.mul` against the constant function, using `logConcave_const`. -/
theorem LogConcave.const_smul {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf0 : ∀ x, 0 ≤ f x)
    (hf : LogConcave f) : LogConcave (fun x => c * f x) :=
  LogConcave.mul (fun _ => hc) hf0 (logConcave_const hc) hf

/-- **Log-concavity is preserved by nonnegative real powers**: if `f` is nonnegative and
log-concave and `0 ≤ p`, then `x ↦ f x ^ p` is log-concave.

The generalization of `LogConcave.mul` from integer to real exponents: `f ^ p` is
log-concave because raising to the power `p` is an increasing map that turns the defining
product inequality into itself. It is what makes the class of log-concave densities stable
under tempering `f ↦ f ^ p`, the reweighting used by annealing schedules in log-concave
sampling. -/
theorem LogConcave.rpow {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : LogConcave f) {p : ℝ}
    (hp : 0 ≤ p) : LogConcave (fun x => f x ^ p) := by
  intro x y t ht0 ht1
  simp only
  calc (f x ^ p) ^ (1 - t) * (f y ^ p) ^ t
      = (f x ^ (1 - t) * f y ^ t) ^ p := by
        rw [Real.mul_rpow (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hf0 y) _),
          ← Real.rpow_mul (hf0 x), ← Real.rpow_mul (hf0 y), ← Real.rpow_mul (hf0 x),
          ← Real.rpow_mul (hf0 y), mul_comm p (1 - t), mul_comm p t]
    _ ≤ f ((1 - t) * x + t * y) ^ p :=
        Real.rpow_le_rpow
          (mul_nonneg (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hf0 y) _))
          (hf x y t ht0 ht1) hp

end Arlib
