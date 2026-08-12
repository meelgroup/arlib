/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The linear algebra of ℓ₁ Lewis weights

The elementary concentration proof (Cohen–Peng, §6) runs on one weighted
Gram matrix and its inverse.  For a family of rows `a : ι → (d → ℝ)` and positive
weights `w : ι → ℝ`, the (`p = 1`) Lewis Gram matrix is

`gram w a = ∑ᵢ wᵢ⁻¹ · aᵢ aᵢᵀ = Aᵀ W⁻¹ A`,

a positive-semidefinite `d × d` matrix.  The argument only ever touches it
through its quadratic form `x ⬝ᵥ gram w a *ᵥ y = ∑ᵢ wᵢ⁻¹ (aᵢ·x)(aᵢ·y)` and,
once it is positive definite, through the leverage-like quantity
`lev = aᵢ ⬝ᵥ (gram w a)⁻¹ *ᵥ aᵢ`.

Mathlib has none of the rank-1 ↔ `mulVec` bridging lemmas, nor `Finset`-sum
closure of `PosSemidef`, nor `mulVec`/`dotProduct` distributing over sums, so all
of that is proved here.

No `sorry`.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-! ## Sum-distribution helpers (absent from Mathlib) -/

/-- `mulVec` distributes over a finite sum of matrices. -/
theorem sum_mulVec (s : Finset ι) (M : ι → Matrix d d ℝ) (x : d → ℝ) :
    (∑ i ∈ s, M i) *ᵥ x = ∑ i ∈ s, M i *ᵥ x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Matrix.add_mulVec, ih]

/-- `dotProduct` distributes over a finite sum in its second argument. -/
theorem dotProduct_sum (s : Finset ι) (y : d → ℝ) (F : ι → d → ℝ) :
    y ⬝ᵥ (∑ i ∈ s, F i) = ∑ i ∈ s, y ⬝ᵥ F i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, dotProduct_add, ih]

/-- Positive semidefiniteness is closed under finite sums. -/
theorem posSemidef_sum (s : Finset ι) (f : ι → Matrix d d ℝ)
    (hf : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Matrix.PosSemidef.zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A nonnegative scalar multiple of a positive-semidefinite matrix is
positive semidefinite. -/
theorem posSemidef_smul {M : Matrix d d ℝ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show (c • M)ᴴ = c • M
    rw [Matrix.conjTranspose_smul, star_trivial, hM.1]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hc (hM.dotProduct_mulVec_nonneg x)

/-! ## Rank-one outer products -/

/-- The outer product `v vᵀ` as a `d × d` matrix. -/
def outer (v : d → ℝ) : Matrix d d ℝ := Matrix.vecMulVec v v

@[simp] theorem outer_apply (v : d → ℝ) (i j : d) : outer v i j = v i * v j := rfl

/-- `(v vᵀ) x = (v · x) • v`. -/
theorem outer_mulVec (v x : d → ℝ) : outer v *ᵥ x = (v ⬝ᵥ x) • v := by
  funext i
  simp only [Matrix.mulVec, outer, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of a rank-one outer product: `y ⬝ᵥ (v vᵀ) x = (v·y)(v·x)`. -/
theorem dotProduct_outer_mulVec (v x y : d → ℝ) :
    y ⬝ᵥ (outer v *ᵥ x) = (v ⬝ᵥ y) * (v ⬝ᵥ x) := by
  rw [outer_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm y v]
  ring

/-- The outer product is symmetric. -/
theorem outer_isHermitian (v : d → ℝ) : (outer v).IsHermitian := by
  show (outer v)ᴴ = outer v
  ext i j
  simp [Matrix.conjTranspose_apply, outer_apply, mul_comm]

/-- A rank-one outer product is positive semidefinite. -/
theorem outer_posSemidef (v : d → ℝ) : (outer v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (outer_isHermitian v) fun x => ?_
  have hstar : (star x : d → ℝ) = x := by funext i; simp
  rw [hstar, dotProduct_outer_mulVec]
  exact mul_self_nonneg _

/-! ## The Lewis Gram matrix -/

/-- The (`p = 1`) **Lewis Gram matrix** `∑ᵢ wᵢ⁻¹ · aᵢ aᵢᵀ = Aᵀ W⁻¹ A`. -/
noncomputable def gram (w : ι → ℝ) (a : ι → d → ℝ) : Matrix d d ℝ :=
  ∑ i, (w i)⁻¹ • outer (a i)

/-- `gram w a *ᵥ x = ∑ᵢ (wᵢ⁻¹ (aᵢ·x)) • aᵢ`. -/
theorem gram_mulVec (w : ι → ℝ) (a : ι → d → ℝ) (x : d → ℝ) :
    gram w a *ᵥ x = ∑ i, ((w i)⁻¹ * (a i ⬝ᵥ x)) • a i := by
  unfold gram
  rw [sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, outer_mulVec, smul_smul]

/-- The quadratic form of the Gram matrix:
`y ⬝ᵥ gram w a *ᵥ x = ∑ᵢ wᵢ⁻¹ (aᵢ·y)(aᵢ·x)`. -/
theorem dotProduct_gram_mulVec (w : ι → ℝ) (a : ι → d → ℝ) (x y : d → ℝ) :
    y ⬝ᵥ (gram w a *ᵥ x) = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ y) * (a i ⬝ᵥ x) := by
  rw [gram_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm y (a i)]
  ring

/-- The Gram matrix is symmetric. -/
theorem gram_isHermitian (w : ι → ℝ) (a : ι → d → ℝ) : (gram w a).IsHermitian := by
  show (gram w a)ᴴ = gram w a
  unfold gram
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, star_trivial, outer_isHermitian (a i)]

/-- With nonnegative reciprocal weights the Gram matrix is positive semidefinite. -/
theorem gram_posSemidef (w : ι → ℝ) (a : ι → d → ℝ) (hw : ∀ i, 0 ≤ (w i)⁻¹) :
    (gram w a).PosSemidef := by
  unfold gram
  exact posSemidef_sum _ _ fun i _ => posSemidef_smul (outer_posSemidef (a i)) (hw i)

/-! ## The leverage quantity and the moment identity -/

variable {w : ι → ℝ} {a : ι → d → ℝ}

/-- The **leverage-like quantity** `aᵢ ⬝ᵥ (gram w a)⁻¹ *ᵥ aᵢ`, i.e. `aᵢᵀ M⁻¹ aᵢ`.
When `w` are the ℓ₁ Lewis weights this equals `wᵢ²`. -/
noncomputable def lev (w : ι → ℝ) (a : ι → d → ℝ) (i : ι) : ℝ :=
  a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)

/-- `M (M⁻¹ aᵢ) = aᵢ` when `M = gram w a` is positive definite. -/
theorem gram_mulVec_inv (hPD : (gram w a).PosDef) (i : ι) :
    gram w a *ᵥ ((gram w a)⁻¹ *ᵥ a i) = a i := by
  have hdet : IsUnit (gram w a).det := isUnit_iff_ne_zero.mpr (Matrix.PosDef.det_pos hPD).ne'
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **The moment identity** at the heart of Cohen–Peng's `momBound`:
`∑ⱼ wⱼ⁻¹ (aⱼ ⬝ᵥ M⁻¹ aᵢ)² = aᵢ ⬝ᵥ M⁻¹ aᵢ`.  Writing `z = M⁻¹ aᵢ`, the left side
is the Gram quadratic form `z ⬝ᵥ (M z)`, and `M z = aᵢ` since `M M⁻¹ = 1`. -/
theorem sum_sq_lev (hPD : (gram w a).PosDef) (i : ι) :
    ∑ j, (w j)⁻¹ * (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2 = lev w a i := by
  rw [lev]
  calc ∑ j, (w j)⁻¹ * (a j ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i)) ^ 2
      = ((gram w a)⁻¹ *ᵥ a i) ⬝ᵥ (gram w a *ᵥ ((gram w a)⁻¹ *ᵥ a i)) := by
        rw [dotProduct_gram_mulVec]
        exact Finset.sum_congr rfl fun j _ => by rw [sq]; ring
    _ = ((gram w a)⁻¹ *ᵥ a i) ⬝ᵥ a i := by rw [gram_mulVec_inv hPD]
    _ = a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a i) := dotProduct_comm _ _

/-- The **ℓ₁ Lewis-weight defining property** (`p = 1`): the leverage of each row
equals the square of its weight, `aᵢᵀ M⁻¹ aᵢ = wᵢ²`. -/
def IsLewis (w : ι → ℝ) (a : ι → d → ℝ) : Prop :=
  (gram w a).PosDef ∧ ∀ i, lev w a i = (w i) ^ 2

end Arlib.Approximation.LewisWeights
