/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Products of finite distributions on a common outcome type

`ProductSpace.CoinSpace` already models a family of independent coins whose
outcome types may differ.  The overwhelmingly common case — and the one an
*empirical estimator* needs — is that every coordinate draws from the **same**
type `X`, with a coordinate-dependent law `μ j`.  Specialising to it buys a
great deal: outcomes are honest functions `ω : ι → X` rather than dependent
ones, so coordinate reads `ω j` need no transport, and the two identities below
can be stated without a single cast.

* `prodSpace μ` — the product space, as a `CoinSpace`.
* `Ex_prod_apply` — **the factorization identity**, and the only real content of
  the file:

    `E[∏_{j ∈ s} f j (ω j)] = ∏_{j ∈ s} (∑ x, μ j x · f j x)`.

  It is `Fintype.prod_sum` in disguise: the mass is a product over *all*
  coordinates, so absorbing `f j` into the `j`-th factor (and `1` into the
  others) turns a sum-of-products into a product-of-sums.
* `Ex_apply` — the `s = {j}` case: the marginal law of one coordinate.
* `kwiseIndep_coord` — coordinate functions are `k`-wise independent **for every
  `k`**, which is what unlocks `KWiseChernoff`'s exponential tail bounds for
  sums of coordinate indicators.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.KWiseChernoff
import Arlib.Probability.ProductSpace
import Arlib.Probability.Markov

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-! ## The product space -/

/-- The product of the finite distributions `μ j` on a common outcome type `X`.
Outcomes are functions `ω : ι → X`, with `mass ω = ∏ j, μ j (ω j)`. -/
def prodSpace (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1) :
    CoinSpace where
  ι := ι
  ιFin := inferInstance
  ιDec := inferInstance
  Coin := fun _ => X
  coinFin := fun _ => inferInstance
  coinDec := fun _ => inferInstance
  coinMass := μ
  coinMass_nonneg := h0
  coinMass_sum := h1

variable {μ : ι → X → ℝ} {h0 : ∀ j x, 0 ≤ μ j x} {h1 : ∀ j, ∑ x, μ j x = 1}

@[simp] theorem prodSpace_mass (ω : ∀ _ : ι, X) :
    (prodSpace μ h0 h1).toFinProb.mass ω = ∏ j, μ j (ω j) := rfl

/-! ## The factorization identity -/

/-- **The product-space factorization.**  For coordinate-wise factors,

  `E[∏_{j ∈ s} f j (ω j)] = ∏_{j ∈ s} (∑ x, μ j x · f j x)`.

Everything else in this file and in `EmpiricalFrequency` is a corollary. -/
theorem Ex_prod_apply (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)
    (s : Finset ι) (f : ι → X → ℝ) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ j ∈ s, f j (ω j))
      = ∏ j ∈ s, ∑ x, μ j x * f j x := by
  classical
  -- absorb `f j` into the `j`-th mass factor (and `1` into the others)
  set g : ι → X → ℝ := fun j x => μ j x * (if j ∈ s then f j x else 1) with hgdef
  have hstep : ∀ ω : ∀ _ : ι, X,
      (∏ j, μ j (ω j)) * (∏ j ∈ s, f j (ω j)) = ∏ j, g j (ω j) := by
    intro ω
    rw [hgdef]
    simp only
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
  have hEx : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ j ∈ s, f j (ω j))
      = ∑ ω : ∀ _ : ι, X, ∏ j, g j (ω j) := by
    simp only [FinProb.Ex, prodSpace_mass]
    exact Finset.sum_congr rfl (fun ω _ => hstep ω)
  rw [hEx, ← Fintype.prod_sum]
  have hin : ∀ j ∈ s, (∑ x, g j x) = ∑ x, μ j x * f j x := by
    intro j hj; simp [hgdef, hj]
  have hout : ∀ j ∈ (Finset.univ : Finset ι), j ∉ s → (∑ x, g j x) = 1 := by
    intro j _ hj; simp [hgdef, hj, h1 j]
  rw [← Finset.prod_subset (Finset.subset_univ s) hout, Finset.prod_congr rfl hin]

/-- The marginal law of a single coordinate. -/
theorem Ex_apply (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)
    (j : ι) (f : X → ℝ) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => f (ω j)) = ∑ x, μ j x * f x := by
  simpa using Ex_prod_apply μ h0 h1 {j} (fun _ => f)

/-! ## `k`-wise independence of the coordinates -/

/-- **Coordinate functions are `k`-wise independent, for every `k`.**  This is
`Ex_prod_apply` read as an independence statement, and it is what lets a sum of
coordinate indicators be fed to the `k`-wise Chernoff bounds of
`Arlib.Probability.KWiseChernoff` at *any* budget `k`. -/
theorem kwiseIndep_coord (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)
    (f : ι → X → ℝ) (k : ℕ) :
    KWiseIndep (prodSpace μ h0 h1).toFinProb k (fun j ω => f j (ω j)) := by
  intro s _
  simp only [FinProb.toProbSpace_Ex]
  refine (Ex_prod_apply μ h0 h1 s f).trans ?_
  refine Finset.prod_congr rfl ?_
  intro j _
  exact (Ex_apply μ h0 h1 j (f j)).symm

end Arlib.Probability
