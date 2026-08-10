/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The ℓ₁ Lewis importance sampler and per-query unbiasedness

An ℓ₁ Lewis-weight coreset is built by sampling rows `i` of a point set with
probability proportional to their Lewis weight `wᵢ`, and reweighting each drawn
row by the inverse of `m` times its draw probability.  This file models exactly
that sampler over the finite-probability-space machinery and proves the estimator
is **unbiased for every query `y`**: the expected value of the reduced functional
equals the exact functional `∑ᵢ |⟨y, aᵢ⟩|`.

* `drawSpace w hw` — a single draw: the outcome type is the index `ι`, with
  `mass i = wᵢ / (∑ⱼ wⱼ)` (draw `i` with probability `∝ wᵢ`).
* `single_draw_unbiased` — the one-draw estimator `(∑w / wᵢ)·|aᵢ·y|` has
  expectation `∑ᵢ |aᵢ·y|`.
* `sampleCoin` / `sampleSpace w hw m` — `m` iid draws, as a product of `m` copies
  of `drawSpace` (encoded as a `CoinSpace` over `Fin m`).
* `sampleSpace_marginal` — the marginal of any single coordinate `k` of the
  product is `drawSpace`.
* `sampledWPS w hw a m ω` — the reduced weighted point set for outcome `ω`:
  index `Fin m`, feature `a (ω k)`, weight `1 / (m · p (ω k))`.
* `estimator_unbiased` — **the m-fold unbiasedness**: for `m > 0`,
  `E_ω[(sampledWPS … ω).E y] = (WPS.exact ι a).E y = ∑ⱼ |⟨y, aⱼ⟩|`.

No `sorry`.
-/
import Arlib.Probability.ProductSpace
import Arlib.Probability.Markov
import Arlib.Approximation.Coresets.Basic
import Mathlib.Data.Matrix.Mul

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset
open Arlib.Probability

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-! ## A single draw -/

/-- **A single importance draw.**  The outcome is the drawn index `i : ι`, drawn
with probability `mass i = wᵢ / (∑ⱼ wⱼ) ∝ wᵢ`. -/
noncomputable def drawSpace (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) : FinProb where
  Ω := ι
  μ :=
    { p := fun i => w i / (∑ j, w j)
      p_nonneg := fun i =>
        div_nonneg (hw i).le (Finset.sum_nonneg fun j _ => (hw j).le)
      p_sum := by
        rw [← Finset.sum_div]
        exact div_self (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty).ne' }

omit [DecidableEq d] in
/-- **Per-query unbiasedness of a single draw.**  Reweighting the drawn row `i` by
`(∑w) / wᵢ` makes `(∑w / wᵢ)·|aᵢ·y|` an unbiased estimator of `∑ᵢ |aᵢ·y|`. -/
theorem single_draw_unbiased (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (y : d → ℝ) :
    (drawSpace w hw).Ex (fun i => ((∑ j, w j) / w i) * |a i ⬝ᵥ y|)
      = ∑ i, |a i ⬝ᵥ y| := by
  unfold FinProb.Ex
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hwi : w i ≠ 0 := (hw i).ne'
  have hW : (∑ j, w j) ≠ 0 := (Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty).ne'
  show (w i / (∑ j, w j)) * ((∑ j, w j) / w i * |a i ⬝ᵥ y|) = |a i ⬝ᵥ y|
  field_simp
  ring

/-! ## The m-fold product of iid draws -/

/-- **`m` iid draws** as a `CoinSpace` over `Fin m`, each coin a copy of the draw
distribution `mass i = wᵢ / (∑ⱼ wⱼ)`. -/
noncomputable def sampleCoin (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (m : ℕ) :
    CoinSpace where
  ι := Fin m
  Coin := fun _ => ι
  coinMass := fun _ i => w i / (∑ j, w j)
  coinMass_nonneg := fun _ i =>
    div_nonneg (hw i).le (Finset.sum_nonneg fun j _ => (hw j).le)
  coinMass_sum := fun _ => by
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty).ne'

/-- The product probability space of `m` iid draws.  An outcome `ω : Fin m → ι`
records the index drawn at each of the `m` rounds. -/
noncomputable def sampleSpace (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (m : ℕ) :
    FinProb :=
  (sampleCoin w hw m).toFinProb

/-- **The single-coordinate marginal is a single draw.**  For any coordinate `k`
and any test function `X`, the expectation over the product of `X` applied to the
`k`-th draw equals the single-draw expectation of `X`. -/
theorem sampleSpace_marginal (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (m : ℕ)
    (X : ι → ℝ) (k : Fin m) :
    (sampleSpace w hw m).Ex (fun ω => X (ω k)) = (drawSpace w hw).Ex X := by
  unfold sampleSpace
  have hpos : ∀ (i : (sampleCoin w hw m).ι) (c : (sampleCoin w hw m).Coin i),
      0 < (sampleCoin w hw m).coinMass i c :=
    fun _ c => div_pos (hw c) (Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty)
  rw [← FinProb.condCE_Ex (P := (sampleCoin w hw m).toFinProb)
    ((sampleCoin w hw m).forget k) (fun ω => X (ω k))]
  have hmass : ∀ c : ι, (sampleCoin w hw m).coinMass k c = (drawSpace w hw).mass c :=
    fun _ => rfl
  have hconst : FinProb.condCE (sampleCoin w hw m).toFinProb
      ((sampleCoin w hw m).forget k) (fun ω => X (ω k))
      = fun _ => (drawSpace w hw).Ex X := by
    funext ω'
    rw [(sampleCoin w hw m).condCE_forget hpos k]
    show (∑ c : ι, (sampleCoin w hw m).coinMass k c * X (Function.update ω' k c k))
        = (drawSpace w hw).Ex X
    unfold FinProb.Ex
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Function.update_self, hmass c]
  rw [hconst, FinProb.Ex_const]

/-! ## The reduced weighted point set -/

/-- **The reduced weighted point set for an outcome `ω`.**  Its `m` points are the
drawn rows `a (ω k)`, each reweighted by `1 / (m · p (ω k))` where
`p i = wᵢ / (∑ⱼ wⱼ)` is the draw probability. -/
noncomputable def sampledWPS (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (m : ℕ) (ω : Fin m → ι) : WPS (Fin m) d where
  wt := fun k => 1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))
  wt_nonneg := fun k => one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg m)
    (div_nonneg (hw (ω k)).le (Finset.sum_nonneg fun j _ => (hw j).le)))
  feat := fun k => a (ω k)

omit [DecidableEq ι] [DecidableEq d] in
/-- The functional of the reduced weighted point set:
`(sampledWPS … ω).E y = ∑ₖ (1 / (m · p (ω k)))·|⟨y, a (ω k)⟩|`. -/
theorem sampledWPS_E (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (m : ℕ) (ω : Fin m → ι) (y : d → ℝ) :
    (sampledWPS w hw a m ω).E y
      = ∑ k, (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |dot y (a (ω k))| :=
  rfl

/-! ## m-fold unbiasedness -/

omit [DecidableEq d] in
/-- **Per-query unbiasedness of the m-fold Lewis sampler.**  For `m > 0` and every
query `y`, the expected reduced functional equals the exact functional
`(WPS.exact ι a).E y = ∑ⱼ |⟨y, aⱼ⟩|`.  Each coordinate's marginal is a single
draw (`sampleSpace_marginal`), which contributes `(1/m)·∑ⱼ |⟨y, aⱼ⟩|`; summing the
`m` coordinates recovers the exact functional. -/
theorem estimator_unbiased (w : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (m : ℕ) (hm : 0 < m) (y : d → ℝ) :
    (sampleSpace w hw m).Ex (fun ω => (sampledWPS w hw a m ω).E y)
      = (WPS.exact ι a).E y := by
  show (sampleSpace w hw m).Ex
      (fun ω => ∑ k : Fin m,
        (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |dot y (a (ω k))|)
      = (WPS.exact ι a).E y
  rw [FinProb.Ex_sum (sampleSpace w hw m) (Finset.univ : Finset (Fin m))
    (fun (k : Fin m) ω => (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |dot y (a (ω k))|)]
  calc ∑ k : Fin m, (sampleSpace w hw m).Ex
          (fun ω => (1 / ((m : ℝ) * (w (ω k) / (∑ j, w j)))) * |dot y (a (ω k))|)
      = ∑ _k : Fin m, (drawSpace w hw).Ex
          (fun c => (1 / ((m : ℝ) * (w c / (∑ j, w j)))) * |dot y (a c)|) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact sampleSpace_marginal w hw m
          (fun c => (1 / ((m : ℝ) * (w c / (∑ j, w j)))) * |dot y (a c)|) k
    _ = ∑ _k : Fin m, (1 / (m : ℝ)) * ∑ c, |dot y (a c)| := by
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        unfold FinProb.Ex
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        have hwc : w c ≠ 0 := (hw c).ne'
        have hW : (∑ j, w j) ≠ 0 :=
          (Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty).ne'
        have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
        show (w c / (∑ j, w j))
            * ((1 / ((m : ℝ) * (w c / (∑ j, w j)))) * |dot y (a c)|)
            = (1 / (m : ℝ)) * |dot y (a c)|
        field_simp
        ring
    _ = (m : ℝ) * ((1 / (m : ℝ)) * ∑ c, |dot y (a c)|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ c, |dot y (a c)| := by
        have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
        rw [← mul_assoc, mul_one_div, div_self hm', one_mul]
    _ = (WPS.exact ι a).E y := (WPS.E_exact ι a y).symm

end Arlib.Approximation.LewisWeights
