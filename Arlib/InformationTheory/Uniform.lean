/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Entropy

/-!
# The uniform distribution and its entropy

`Arlib.InformationTheory.Entropy` proves the maximum-entropy bound
`Hdist p ≤ log (card α)` for every distribution `p`. This file supplies the
matching *equality* case: the uniform distribution on a nonempty finite type has
entropy exactly `log (card α)`, so the bound is sharp.

The motivation is Fano's inequality, which is applied to a hidden parameter `X`
drawn uniformly from a finite range. Fano bounds the error probability in terms
of `H P X`, and `H_of_dist_eq_unif` turns that into the concrete quantity
`log (card α)` whenever the law of `X` is uniform.

The uniform distribution itself, `Arlib.Probability.unifDist`, is a law with no
information-theoretic content and lives in `Arlib.Probability.Law`; it is
re-exported by `Arlib.InformationTheory.Basic` under its old spelling
`Arlib.InformationTheory.unifDist`, together with
`Arlib.InformationTheory.isProbDist_unifDist`.

## Main results

* `Arlib.InformationTheory.Hdist_unifDist` — its entropy is `log (card α)`.
* `Arlib.InformationTheory.H_of_dist_eq_unif` — a random variable with uniform
  law has entropy `log (card α)`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-- On a nonempty finite type the cardinality is nonzero as a real number; this
is the side condition every computation below needs. -/
private theorem card_ne_zero (α : Type) [Fintype α] [Nonempty α] :
    ((Fintype.card α : ℝ)) ≠ 0 := by
  have h : 0 < Fintype.card α := Fintype.card_pos
  exact Nat.cast_ne_zero.mpr h.ne'

/-- **The uniform distribution has maximal entropy**, exactly `log (card α)`. -/
theorem Hdist_unifDist {α : Type} [Fintype α] [Nonempty α] :
    Hdist (unifDist α) = Real.log (Fintype.card α) := by
  have hN : ((Fintype.card α : ℝ)) ≠ 0 := card_ne_zero α
  show ∑ _a : α, Real.negMulLog ((Fintype.card α : ℝ))⁻¹ = _
  have hterm : Real.negMulLog ((Fintype.card α : ℝ))⁻¹
      = ((Fintype.card α : ℝ))⁻¹ * Real.log (Fintype.card α) := by
    simp only [Real.negMulLog, Real.log_inv]
    ring
  rw [Finset.sum_congr rfl fun _ _ => hterm, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

/-- A random variable with uniform law has entropy `log (card α)`. -/
theorem H_of_dist_eq_unif {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {P : FinProb} (X : P.Ω → α) (hX : dist P X = unifDist α) :
    H P X = Real.log (Fintype.card α) := by
  show Hdist (dist P X) = _
  rw [hX]
  exact Hdist_unifDist

end InformationTheory
end Arlib
