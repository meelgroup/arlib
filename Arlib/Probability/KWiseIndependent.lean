/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.Independence
import Arlib.Combinatorics.BigOperators

/-!
# `k`-wise independent families of indicators, and the second-moment bound

Lower-bound arguments of the "second moment method" kind need only a *limited*
amount of independence: for a family of `{0,1}`-valued random variables it is
enough that every **pair** has product expectation to conclude

  `Var[∑ᵢ Zᵢ] ≤ Ex[∑ᵢ Zᵢ]`,

which is exactly the shape Chebyshev (`ProbSpace.chebyshev`) is applied to.

This file introduces `KWiseIndep P k Z` — every subfamily of size at most `k`
has product expectation — stated for a general `k` so that the stronger
concentration bounds built on higher moments can reuse it, together with
`IsIndicatorFamily` and the variance bound `var_sum_le_ex_sum` at `k = 2`.

## Implementation notes

The statements are phrased over `P.toProbSpace.Ex` / `P.toProbSpace.Var` for a
`P : FinProb`, so they plug directly into the abstract `ProbSpace` surface
(`markov`, `chebyshev`).  Over a `FinProb` the two carriers agree
*definitionally* (`FinProb.toProbSpace` sets `Ex := P.Ex`), so the proofs go
through the concrete `FinProb` algebra (`FinProb.Ex_sum`, `FinProb.Var_eq`) with
no admissibility bookkeeping: the bridging lemmas `toProbSpace_Ex` and
`toProbSpace_Var` below are both `rfl`.

Everything here is proved with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset
open Arlib.Combinatorics

/-! ## Bridging the `FinProb` and `ProbSpace` expectations (both `rfl`) -/

namespace FinProb

/-- The abstract expectation of `P.toProbSpace` *is* the concrete `FinProb`
expectation of `P`. -/
theorem toProbSpace_Ex (P : FinProb) (X : P.Ω → ℝ) :
    P.toProbSpace.Ex X = P.Ex X := rfl

/-- The abstract variance of `P.toProbSpace` *is* the concrete `FinProb`
variance of `P`. -/
theorem toProbSpace_Var (P : FinProb) (X : P.Ω → ℝ) :
    P.toProbSpace.Var X = P.Var X := rfl

end FinProb

/-! ## `k`-wise independence and indicator families -/

/-- A family of `{0,1}`-valued random variables is `k`-wise independent if every
subfamily of size at most `k` has product expectation. -/
def KWiseIndep {ι : Type} [Fintype ι] [DecidableEq ι] (P : FinProb) (k : ℕ)
    (Z : ι → P.Ω → ℝ) : Prop :=
  ∀ s : Finset ι, s.card ≤ k →
    P.toProbSpace.Ex (fun ω => ∏ i ∈ s, Z i ω)
      = ∏ i ∈ s, P.toProbSpace.Ex (Z i)

/-- Indicator-valued: each `Z i` takes only the values `0` and `1`. -/
def IsIndicatorFamily {ι : Type} [Fintype ι] {P : FinProb} (Z : ι → P.Ω → ℝ) : Prop :=
  ∀ i ω, Z i ω = 0 ∨ Z i ω = 1

/-- An indicator is idempotent: `Zᵢ ω * Zᵢ ω = Zᵢ ω`. -/
theorem IsIndicatorFamily.mul_self {ι : Type} [Fintype ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hZ : IsIndicatorFamily Z) (i : ι) (ω : P.Ω) :
    Z i ω * Z i ω = Z i ω := by
  rcases hZ i ω with h | h <;> rw [h] <;> ring

/-- Pairwise product rule extracted from `2`-wise independence: for `i ≠ j`,
`Ex[Zᵢ Zⱼ] = Ex[Zᵢ] · Ex[Zⱼ]`.  Obtained by instantiating `KWiseIndep` at the
two-element `Finset` `{i, j}`. -/
theorem KWiseIndep.ex_mul {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hind : KWiseIndep P 2 Z) {i j : ι} (hij : i ≠ j) :
    P.Ex (fun ω => Z i ω * Z j ω) = P.Ex (Z i) * P.Ex (Z j) := by
  have hcard : ({i, j} : Finset ι).card ≤ 2 := by
    rw [Finset.card_pair hij]
  have h := hind {i, j} hcard
  simp only [Finset.prod_pair hij] at h
  exact h

/-! ## The second-moment (variance) bound -/

/-- For a pairwise independent family of indicators, the variance of the sum is at
most its expectation. This is the bound Chebyshev is applied to. -/
theorem var_sum_le_ex_sum {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hind : KWiseIndep P 2 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) :
    P.toProbSpace.Var (fun ω => ∑ i ∈ s, Z i ω)
      ≤ P.toProbSpace.Ex (fun ω => ∑ i ∈ s, Z i ω) := by
  show P.Var (fun ω => ∑ i ∈ s, Z i ω) ≤ P.Ex (fun ω => ∑ i ∈ s, Z i ω)
  -- Linearity: the expectation of the sum is the sum of the expectations.
  have hEx : P.Ex (fun ω => ∑ i ∈ s, Z i ω) = ∑ i ∈ s, P.Ex (Z i) := P.Ex_sum s Z
  -- Pointwise expansion of the square into diagonal + off-diagonal.
  have hsq : ∀ ω : P.Ω, (∑ i ∈ s, Z i ω) ^ 2
      = (∑ i ∈ s, Z i ω) + ∑ i ∈ s, ∑ j ∈ s.erase i, Z i ω * Z j ω := by
    intro ω
    have h1 : (∑ i ∈ s, Z i ω) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω := by
      rw [sq, Finset.sum_mul_sum]
    have hsplit : ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω
        = (∑ i ∈ s, Z i ω * Z i ω) + ∑ i ∈ s, ∑ j ∈ s.erase i, Z i ω * Z j ω :=
      sum_matrix_diag_offdiag s (fun i j => Z i ω * Z j ω)
    have hdiag : (∑ i ∈ s, Z i ω * Z i ω) = ∑ i ∈ s, Z i ω :=
      Finset.sum_congr rfl (fun i _ => hZ.mul_self i ω)
    rw [h1, hsplit, hdiag]
  -- Off-diagonal expectations factor by pairwise independence.
  have hoff : P.Ex (fun ω => ∑ i ∈ s, ∑ j ∈ s.erase i, Z i ω * Z j ω)
      = ∑ i ∈ s, ∑ j ∈ s.erase i, P.Ex (Z i) * P.Ex (Z j) := by
    rw [P.Ex_sum s (fun i ω => ∑ j ∈ s.erase i, Z i ω * Z j ω)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [P.Ex_sum (s.erase i) (fun j ω => Z i ω * Z j ω)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact hind.ex_mul (Ne.symm (Finset.ne_of_mem_erase hj))
  -- Second moment of the sum.
  have hsq2 : P.Ex (fun ω => (∑ i ∈ s, Z i ω) ^ 2)
      = (∑ i ∈ s, P.Ex (Z i))
        + ∑ i ∈ s, ∑ j ∈ s.erase i, P.Ex (Z i) * P.Ex (Z j) := by
    have hfun : (fun ω => (∑ i ∈ s, Z i ω) ^ 2)
        = fun ω => (∑ i ∈ s, Z i ω) + ∑ i ∈ s, ∑ j ∈ s.erase i, Z i ω * Z j ω :=
      funext hsq
    rw [hfun, P.Ex_add (fun ω => ∑ i ∈ s, Z i ω)
      (fun ω => ∑ i ∈ s, ∑ j ∈ s.erase i, Z i ω * Z j ω), hEx, hoff]
  -- The same diagonal / off-diagonal split for the square of the expectation.
  have hmsq : (∑ i ∈ s, P.Ex (Z i)) ^ 2
      = (∑ i ∈ s, (P.Ex (Z i)) ^ 2)
        + ∑ i ∈ s, ∑ j ∈ s.erase i, P.Ex (Z i) * P.Ex (Z j) := by
    have h1 : (∑ i ∈ s, P.Ex (Z i)) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, P.Ex (Z i) * P.Ex (Z j) := by
      rw [sq, Finset.sum_mul_sum]
    have hsplit : ∑ i ∈ s, ∑ j ∈ s, P.Ex (Z i) * P.Ex (Z j)
        = (∑ i ∈ s, P.Ex (Z i) * P.Ex (Z i))
          + ∑ i ∈ s, ∑ j ∈ s.erase i, P.Ex (Z i) * P.Ex (Z j) :=
      sum_matrix_diag_offdiag s (fun i j => P.Ex (Z i) * P.Ex (Z j))
    have hdiag : (∑ i ∈ s, P.Ex (Z i) * P.Ex (Z i)) = ∑ i ∈ s, (P.Ex (Z i)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => (sq (P.Ex (Z i))).symm)
    rw [h1, hsplit, hdiag]
  -- The off-diagonal contributions cancel, leaving `Var = Ex - ∑ (Ex Zᵢ)²`.
  have hVar : P.Var (fun ω => ∑ i ∈ s, Z i ω)
      = (∑ i ∈ s, P.Ex (Z i)) - ∑ i ∈ s, (P.Ex (Z i)) ^ 2 := by
    rw [P.Var_eq, hsq2, hEx, hmsq]
    ring
  have hnn : 0 ≤ ∑ i ∈ s, (P.Ex (Z i)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [hVar, hEx]
  linarith

end Arlib.Probability
