/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.LewisWeights.Net
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt

/-
# ε-nets in the metric of a positive-definite matrix

For a positive-definite `M : Matrix d d ℝ` we build a finite `ε`-net of the
`M`-unit ball `{ y : Mq M y ≤ 1 }`, where `Mq M y = yᵀ M y` is the associated
quadratic form.  The net is obtained by transporting the Euclidean sup-norm net
of `Arlib.Approximation.LewisWeights.Net` through the matrix square root
`R = M^{1/2}`: since `Mq M y = ∑ i, (R *ᵥ y) i ^ 2 = ‖R *ᵥ y‖₂²`, the map
`y ↦ R *ᵥ y` is an isometry from the `M`-metric to the Euclidean ℓ₂-metric, and
`R⁻¹` pulls the Euclidean net back.

Main results:
* `Mq`               : the quadratic form `y ⬝ᵥ (M *ᵥ y)`.
* `Mq_eq_sqSum`      : `Mq M y = ∑ i, (M^{1/2} *ᵥ y) i ^ 2`.
* `sqSum_le`         : `∑ i, z i ^ 2 ≤ (card d) * ‖z‖²` for the sup-norm `‖·‖`.
* `exists_Mnet`      : a finite `ε`-net of the `M`-unit ball of cardinality at
  most `(3 * √(card d) / ε) ^ (card d)`.
-/

open Finset
open scoped Matrix

namespace Arlib.Approximation.LewisWeights

-- `CFC.sqrt` on matrices lives behind the scoped `MatrixOrder` partial order.
open scoped MatrixOrder

/-- The quadratic form `y ↦ yᵀ M y` associated to `M`. -/
def Mq {d : Type*} [Fintype d] (M : Matrix d d ℝ) (y : d → ℝ) : ℝ := y ⬝ᵥ (M *ᵥ y)

/-- Sum of squares of the coordinates, i.e. the squared Euclidean ℓ₂-norm,
kept as a plain real sum to avoid dragging in the ℓ₂ norm instance. -/
def sqSum {d : Type*} [Fintype d] (z : d → ℝ) : ℝ := ∑ i, z i ^ 2

/-- **Key isometry identity.**  Writing `R = M^{1/2}` for the p.s.d. square root
of `M`, the `M`-quadratic form of `y` equals the squared Euclidean length of
`R *ᵥ y`. -/
theorem Mq_eq_sqSum {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) (hM : M.PosDef) (y : d → ℝ) :
    Mq M y = sqSum (CFC.sqrt M *ᵥ y) := by
  set R := CFC.sqrt M with hR
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M
  have hRsymm : Rᵀ = R := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).1
  unfold Mq sqSum
  have h1 : M *ᵥ y = R *ᵥ (R *ᵥ y) := by rw [Matrix.mulVec_mulVec, hRR]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRsymm]
  unfold dotProduct
  exact Finset.sum_congr rfl (fun i _ => (pow_two _).symm)

/-- The sum of squares is bounded by `(card d)` times the squared sup-norm,
since each coordinate square is at most `‖z‖²`. -/
theorem sqSum_le {d : Type*} [Fintype d] (z : d → ℝ) :
    sqSum z ≤ (Fintype.card d : ℝ) * ‖z‖ ^ 2 := by
  unfold sqSum
  calc ∑ i, z i ^ 2 ≤ ∑ _i : d, ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |z i| ≤ ‖z‖ := by
          have := norm_le_pi_norm z i; rwa [Real.norm_eq_abs] at this
        calc z i ^ 2 = |z i| ^ 2 := (sq_abs _).symm
          _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (Fintype.card d : ℝ) * ‖z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`ε`-net in the `M`-metric.**  For a positive-definite `M` and `0 < ε ≤ 1`,
the `M`-unit ball `{ y : Mq M y ≤ 1 }` admits a finite set `S` of size at most
`(3 * √(card d) / ε) ^ (card d)` such that every ball point is within squared
`M`-distance `ε²` of some `s ∈ S`. -/
theorem exists_Mnet {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℝ) (hM : M.PosDef) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ S : Finset (d → ℝ),
      (S.card : ℝ) ≤ (3 * Real.sqrt (Fintype.card d) / ε) ^ (Fintype.card d) ∧
      ∀ y : d → ℝ, Mq M y ≤ 1 → ∃ s ∈ S, Mq M (y - s) ≤ ε ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card d) with h0 | hpos
  · -- `d` is empty: the quadratic form is identically `0`.
    have : IsEmpty d := Fintype.card_eq_zero_iff.mp h0
    refine ⟨{0}, ?_, ?_⟩
    · rw [Finset.card_singleton]
      simp only [h0, pow_zero]; norm_num
    · intro y _
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      have hz : Mq M (y - 0) = 0 := by
        unfold Mq dotProduct
        rw [Finset.univ_eq_empty, Finset.sum_empty]
      rw [hz]; positivity
  · -- positive dimension: transport the Euclidean net through `R = M^{1/2}`.
    set n := Fintype.card d with hn
    set R := CFC.sqrt M with hR
    have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M
    -- `R` is invertible since `det R * det R = det M > 0`.
    have hdetM : 0 < M.det := hM.det_pos
    have hRRdet : R.det * R.det = M.det := by rw [← Matrix.det_mul, hRR]
    have hRdet : R.det ≠ 0 := by
      intro h; rw [h, mul_zero] at hRRdet; exact (ne_of_lt hdetM) hRRdet
    have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
    have hRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRunit
    -- positivity facts for `√n` and the scaled radius `ε'`.
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hpos
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1
    set ε' : ℝ := ε / Real.sqrt n with hε'
    have hε'pos : 0 < ε' := div_pos hε hsqrtpos
    have hε'1 : ε' ≤ 1 := (div_le_one hsqrtpos).mpr (le_trans hε1 hsqrt1)
    -- the Euclidean sup-norm net at the finer radius `ε'`.
    obtain ⟨S₀, -, hS₀card, hS₀cover⟩ := exists_net_unit_ball (ι := d) hε'pos hε'1
    refine ⟨S₀.image (fun s => R⁻¹ *ᵥ s), ?_, ?_⟩
    · -- cardinality: `#S ≤ #S₀ ≤ (3/ε')^n = (3 √n / ε)^n`.
      have h1 : ((S₀.image (fun s => R⁻¹ *ᵥ s)).card : ℝ) ≤ (S₀.card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      have h3 : (3 : ℝ) / ε' = 3 * Real.sqrt n / ε := by
        rw [hε', div_div_eq_mul_div]
      calc ((S₀.image (fun s => R⁻¹ *ᵥ s)).card : ℝ)
          ≤ (S₀.card : ℝ) := h1
        _ ≤ (3 / ε') ^ n := hS₀card
        _ = (3 * Real.sqrt n / ε) ^ n := by rw [h3]
    · -- covering.
      intro y hy
      set z := R *ᵥ y with hz
      have hMqy : Mq M y = sqSum z := Mq_eq_sqSum M hM y
      have hsqSumz : sqSum z ≤ 1 := by rw [← hMqy]; exact hy
      -- `‖z‖ ≤ 1` in sup-norm, since each `z i² ≤ ∑ z j² ≤ 1`.
      have hznorm : ‖z‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num)]
        intro i
        rw [Real.norm_eq_abs]
        have hzi2 : z i ^ 2 ≤ 1 :=
          le_trans (Finset.single_le_sum (f := fun j => z j ^ 2)
            (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)) hsqSumz
        have h := hzi2
        rw [← sq_abs] at h
        nlinarith [abs_nonneg (z i), h, sq_nonneg (|z i| - 1)]
      -- the Euclidean net supplies `s` within `ε'` of `z`.
      obtain ⟨s, hsS₀, hs⟩ := hS₀cover z hznorm
      refine ⟨R⁻¹ *ᵥ s, Finset.mem_image_of_mem _ hsS₀, ?_⟩
      rw [Mq_eq_sqSum M hM]
      have hvec : R *ᵥ (y - R⁻¹ *ᵥ s) = z - s := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec]
      rw [show CFC.sqrt M = R from rfl, hvec]
      have hn0' : (n : ℝ) ≠ 0 := by positivity
      calc sqSum (z - s) ≤ (n : ℝ) * ‖z - s‖ ^ 2 := sqSum_le (z - s)
        _ ≤ (n : ℝ) * ε' ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hnR
            exact pow_le_pow_left₀ (norm_nonneg _) hs 2
        _ = ε ^ 2 := by
            rw [hε', div_pow, Real.sq_sqrt hnR]
            field_simp

end Arlib.Approximation.LewisWeights
