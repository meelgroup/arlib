/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The measure-preserving per-coordinate swap underpinning symmetrization

The symmetrization step of Cohen–Peng's `momentreduct` argument needs to insert
*independent Rademacher signs* into a sum of iid Lewis draws.  The formal engine
for that is the observation that, on the product of two independent copies of the
`m`-fold Lewis sampler, swapping the two draws at a coordinate `r` — for any fixed
sign pattern `σ : Fin m → Bool` deciding at which coordinates to swap — leaves the
joint law untouched.

Concretely, `swapPair σ` maps a pair of outcomes `(ω, ω')` to the pair that keeps
`(ω r, ω' r)` where `σ r` is `true` and swaps them where `σ r` is `false`.  Because
the sampler mass factorises over coordinates and each coordinate contributes the
symmetric factor `w(ω r)·w(ω' r)`, the joint mass is preserved.  The swap is an
involution, hence a bijection, so reindexing the product-space expectation by it
changes nothing:

* `swapPair` / `swapPair_involutive` / `swapPairEquiv` — the swap and its packaging
  as an involutive equivalence.
* `Ex_prodFinProb_swapPair` — **the product-space expectation is invariant under
  `swapPair`.**  This is exactly what licenses "insert independent signs" in the
  symmetrization step.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Sampler
import Arlib.Probability.FinProbProd

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset
open Arlib.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Per-coordinate swap of two sample outcomes, gated by `σ`: at coordinate `r`,
keep `(p.1 r, p.2 r)` if `σ r`, else swap them. -/
def swapPair {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → ι) × (Fin m → ι)) :
    (Fin m → ι) × (Fin m → ι) :=
  (fun r => if σ r then p.1 r else p.2 r, fun r => if σ r then p.2 r else p.1 r)

omit [Fintype ι] [DecidableEq ι] in
/-- `swapPair σ` is an involution (hence a bijection). -/
theorem swapPair_involutive {m : ℕ} (σ : Fin m → Bool) :
    Function.Involutive (swapPair (ι := ι) σ) := by
  intro p; ext r <;> · simp only [swapPair]; by_cases h : σ r <;> simp [h]

/-- `swapPair σ` packaged as an equivalence. -/
def swapPairEquiv {m : ℕ} (σ : Fin m → Bool) :
    ((Fin m → ι) × (Fin m → ι)) ≃ ((Fin m → ι) × (Fin m → ι)) :=
  (swapPair_involutive σ).toPerm

/-- The expectation over a `FinProb` product spelled as an explicit sum over pairs,
with the mass factorised over the two coordinates. -/
theorem prodFinProb_Ex_eq_sum (P Q : FinProb) (F : P.Ω × Q.Ω → ℝ) :
    (prodFinProb P Q).Ex F = ∑ p : P.Ω × Q.Ω, P.mass p.1 * Q.mass p.2 * F p := rfl

/-- **Mass invariance under `swapPair`.**  The joint sampler mass of a pair of
outcomes is unchanged by `swapPair σ`, because the mass factorises over coordinates
and the swap only reorders the two coordinate factors `w(p.1 r)/W` and `w(p.2 r)/W`. -/
theorem mass_swapPair (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (m : ℕ)
    (σ : Fin m → Bool) (p : (Fin m → ι) × (Fin m → ι)) :
    (sampleSpace w hw m).mass (swapPair σ p).1
        * (sampleSpace w hw m).mass (swapPair σ p).2
      = (sampleSpace w hw m).mass p.1 * (sampleSpace w hw m).mass p.2 := by
  show (∏ r, (sampleCoin w hw m).coinMass r ((swapPair σ p).1 r))
        * ∏ r, (sampleCoin w hw m).coinMass r ((swapPair σ p).2 r)
      = (∏ r, (sampleCoin w hw m).coinMass r (p.1 r))
        * ∏ r, (sampleCoin w hw m).coinMass r (p.2 r)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [swapPair]
  by_cases h : σ r <;> simp [h]
  ring

/-- **The product-space expectation is invariant under `swapPair`.**  Because the
sampler mass factorises over coordinates and `swapPair` only permutes the pair of
coins at each coordinate (`w(p.1 r)·w(p.2 r) = w(p.2 r)·w(p.1 r)`), the joint mass
of `(ω, ω')` is preserved, so reindexing the expectation by the involution changes
nothing. -/
theorem Ex_prodFinProb_swapPair (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (m : ℕ)
    (σ : Fin m → Bool) (X : ((Fin m → ι) × (Fin m → ι)) → ℝ) :
    (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex (fun p => X (swapPair σ p))
      = (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex X := by
  refine (prodFinProb_Ex_eq_sum _ _ _).trans
    (Eq.trans ?_ (prodFinProb_Ex_eq_sum _ _ _).symm)
  -- Reindex the sum by the involution `swapPairEquiv σ`.  The per-summand obligation
  -- is exactly mass invariance (`mass_swapPair`); `swapPairEquiv σ p = swapPair σ p`
  -- holds definitionally.
  refine Fintype.sum_equiv (swapPairEquiv σ)
    (fun p => (sampleSpace w hw m).mass p.1 * (sampleSpace w hw m).mass p.2
      * X (swapPair σ p))
    (fun p => (sampleSpace w hw m).mass p.1 * (sampleSpace w hw m).mass p.2 * X p)
    (fun p => ?_)
  show (sampleSpace w hw m).mass p.1 * (sampleSpace w hw m).mass p.2 * X (swapPair σ p)
      = (sampleSpace w hw m).mass (swapPair σ p).1
          * (sampleSpace w hw m).mass (swapPair σ p).2 * X (swapPair σ p)
  rw [mass_swapPair w hw m σ p]

end Arlib.Approximation.LewisWeights
