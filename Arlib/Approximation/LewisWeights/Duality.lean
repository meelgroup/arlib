/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ℓ₁/ℓ∞ duality and its even-power form

The analytic heart of the Route-A "sup-bridge".  Two elementary real-analysis
facts, free of any Lewis-weight content:

* `dot_le_sup_abs` — the ℓ₁/ℓ∞ duality **upper bound**: for a test vector `y`
  with `∑ᵢ |yᵢ| ≤ 1`, the linear form `∑ᵢ cᵢ yᵢ` never exceeds the ℓ∞ norm
  `maxᵢ |cᵢ|`.

* `dot_pow_le_sum_abs_pow` — the **even-power sup-bridge**: composing the duality
  bound (applied through `|·|`) with the order-theoretic step
  `max_abs_pow_le_sum_pow`, the `2k`-th power of the linear form is dominated by
  the sum of `2k`-th powers `∑ᵢ |cᵢ|^{2k}` — the exact shape the moment method
  consumes.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.HighProb

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι]

/-! ## ℓ₁/ℓ∞ duality (upper bound) -/

/-- **ℓ₁/ℓ∞ duality, upper bound.**  For any test vector `y` with `∑ᵢ |yᵢ| ≤ 1`,
the linear form `∑ᵢ cᵢ yᵢ` is at most the ℓ∞ norm `maxᵢ |cᵢ|`.

`∑ᵢ cᵢyᵢ ≤ ∑ᵢ |cᵢ||yᵢ| ≤ ∑ᵢ (maxⱼ|cⱼ|)|yᵢ| = (maxⱼ|cⱼ|)·∑ᵢ|yᵢ| ≤ maxⱼ|cⱼ|`. -/
theorem dot_le_sup_abs [Nonempty ι] (c y : ι → ℝ) (hy : ∑ i, |y i| ≤ 1) :
    ∑ i, c i * y i ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := by
  have hMnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    exact le_trans (abs_nonneg (c i₀))
      (Finset.le_sup' (fun i => |c i|) (Finset.mem_univ i₀))
  calc ∑ i, c i * y i
      ≤ ∑ i, (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * |y i| := by
        apply Finset.sum_le_sum
        intro i _
        calc c i * y i ≤ |c i * y i| := le_abs_self _
          _ = |c i| * |y i| := abs_mul _ _
          _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * |y i| :=
              mul_le_mul_of_nonneg_right
                (Finset.le_sup' (fun i => |c i|) (Finset.mem_univ i)) (abs_nonneg _)
    _ = (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * ∑ i, |y i| := by
        rw [Finset.mul_sum]
    _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * 1 :=
        mul_le_mul_of_nonneg_left hy hMnn
    _ = Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := mul_one _

/-! ## Even-power sup-bridge -/

/-- **Even-power sup-bridge.**  For a test vector `y` with `∑ᵢ |yᵢ| ≤ 1`, the
`2k`-th power of the linear form `∑ᵢ cᵢ yᵢ` is bounded by the sum of `2k`-th
powers `∑ᵢ |cᵢ|^{2k}`.

Since `2k` is even, `(∑ᵢ cᵢyᵢ)^{2k} = |∑ᵢ cᵢyᵢ|^{2k}`, and `|∑ᵢ cᵢyᵢ| ≤ maxᵢ|cᵢ|`
by the duality bound (here applied directly through `|·|`); the final step
`(maxᵢ|cᵢ|)^{2k} ≤ ∑ᵢ|cᵢ|^{2k}` is `max_abs_pow_le_sum_pow`. -/
theorem dot_pow_le_sum_abs_pow [Nonempty ι] (c y : ι → ℝ) (hy : ∑ i, |y i| ≤ 1)
    (k : ℕ) :
    (∑ i, c i * y i) ^ (2 * k) ≤ ∑ i, |c i| ^ (2 * k) := by
  have hMnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    exact le_trans (abs_nonneg (c i₀))
      (Finset.le_sup' (fun i => |c i|) (Finset.mem_univ i₀))
  have habs : |∑ i, c i * y i|
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := by
    calc |∑ i, c i * y i|
        ≤ ∑ i, |c i * y i| :=
          Finset.abs_sum_le_sum_abs (fun i => c i * y i) Finset.univ
      _ = ∑ i, |c i| * |y i| := by simp only [abs_mul]
      _ ≤ ∑ i, (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * |y i| := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right
            (Finset.le_sup' (fun i => |c i|) (Finset.mem_univ i)) (abs_nonneg _)
      _ = (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * ∑ i, |y i| := by
          rw [Finset.mul_sum]
      _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) * 1 :=
          mul_le_mul_of_nonneg_left hy hMnn
      _ = Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|) := mul_one _
  have hev : Even (2 * k) := ⟨k, two_mul k⟩
  calc (∑ i, c i * y i) ^ (2 * k)
      = |∑ i, c i * y i| ^ (2 * k) := (hev.pow_abs _).symm
    _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) ^ (2 * k) :=
        pow_le_pow_left₀ (abs_nonneg _) habs (2 * k)
    _ ≤ ∑ i, |c i| ^ (2 * k) := max_abs_pow_le_sum_pow c (2 * k)

end Arlib.Approximation.LewisWeights
