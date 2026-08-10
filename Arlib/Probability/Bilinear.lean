/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Cauchy–Schwarz for a positive semidefinite symmetric bilinear form

The spectral arguments in the local-to-global machinery repeatedly need the
following completely elementary fact: a symmetric bilinear form `B` on a real
vector space which satisfies `0 ≤ B u u` also satisfies

  `B u v ^ 2 ≤ B u u * B v v`.

The usual textbook route is via eigenvalues; the route taken here is the
discriminant of the nonnegative quadratic `t ↦ B (u + t • v) (u + t • v)`, which
needs no spectral theory at all and hence transfers verbatim to Lean.

We state it for a form on functions `ι → ℝ`, which is the only setting used
downstream (`L²(μ)` inner products, and the forms `⟪·, P ·⟫_μ` attached to a
reversible chain).  Two consequences are packaged for direct use:

* `psd_cauchy_schwarz` — the inequality itself;
* `norm_sq_le_of_psd_le` — if `B` is PSD and `B u u ≤ c * Q u u` for a PSD `Q`,
  then the "operator norm" bound `Q (Bop u) (Bop u) ≤ c ^ 2 * Q u u` follows.
  (Stated concretely at the point of use; here we only supply the core lemma.)

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Prelude
import Mathlib.Algebra.QuadraticDiscriminant

namespace Arlib.Probability

/-- A real-valued form `B` on functions `ι → ℝ` is *bilinear* if it is additive
and homogeneous in each argument. -/
structure IsBilin {ι : Type*} (B : (ι → ℝ) → (ι → ℝ) → ℝ) : Prop where
  add_left : ∀ u v w, B (u + v) w = B u w + B v w
  smul_left : ∀ (c : ℝ) u v, B (c • u) v = c * B u v
  add_right : ∀ u v w, B u (v + w) = B u v + B u w
  smul_right : ∀ (c : ℝ) u v, B u (c • v) = c * B u v

/-- **Cauchy–Schwarz for a positive semidefinite symmetric bilinear form.**

If `B` is bilinear, symmetric, and `0 ≤ B u u` for every `u`, then
`B u v ^ 2 ≤ B u u * B v v`.

The proof is the discriminant of the nonnegative quadratic
`t ↦ B (u + t • v) (u + t • v) = B v v * t ^ 2 + 2 * B u v * t + B u u`. -/
theorem psd_cauchy_schwarz {ι : Type*} {B : (ι → ℝ) → (ι → ℝ) → ℝ}
    (hbil : IsBilin B) (hsymm : ∀ u v, B u v = B v u) (hpsd : ∀ u, 0 ≤ B u u)
    (u v : ι → ℝ) : B u v ^ 2 ≤ B u u * B v v := by
  -- Expand the quadratic.
  have hexp : ∀ t : ℝ, B (u + t • v) (u + t • v)
      = B v v * (t * t) + (2 * B u v) * t + B u u := by
    intro t
    rw [hbil.add_left, hbil.add_right, hbil.add_right,
      hbil.smul_left, hbil.smul_right, hbil.smul_right, hbil.smul_left]
    have : B v u = B u v := hsymm v u
    rw [this]
    ring
  have hquad : ∀ t : ℝ, 0 ≤ B v v * (t * t) + (2 * B u v) * t + B u u := by
    intro t; rw [← hexp t]; exact hpsd _
  have hdisc : discrim (B v v) (2 * B u v) (B u u) ≤ 0 := discrim_le_zero hquad
  -- `discrim a b c = b ^ 2 - 4 * a * c`
  simp only [discrim] at hdisc
  nlinarith [hdisc]

/-- The `L²(μ)`-style form `B u v = ∑ x, w x * u x * v x` with nonnegative
weights `w` is bilinear. -/
theorem isBilin_weighted {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    IsBilin (fun u v => ∑ x, w x * u x * v x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v z; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring
  · intro c u v; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro u v z; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring
  · intro c u v; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability (IsBilin psd_cauchy_schwarz isBilin_weighted)

end Arlib.MarkovChains

namespace Arlib.MarkovChains.IsBilin

export Arlib.Probability.IsBilin (mk add_left smul_left add_right smul_right)

end Arlib.MarkovChains.IsBilin
