/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Route-A sup-bridge (`lem:lewlinf`)

The linchpin that removes the ε-net from Cohen–Peng's argument and delivers the
optimal-in-`d` bound.  It composes two already-proven purely linear pieces with
the moment bound:

* the projection identity `projT_apply` (the per-row process is a single dual
  pairing against `M⁻¹`), and
* the ℓ₁/ℓ∞ even-power duality `dot_pow_le_sum_abs_pow`,

to show that the **whole** linear sign-process `∑ⱼ σⱼ (aⱼ·x)` against any test
`x` with `‖Ax‖₁ ≤ 1` has its `2k`-th moment controlled by the sum of the per-row
moments — hence by `n·(2ekU)^k` via `avg_sum_row_pow_le`.

The crux is `process_eq_sum_rowProc`: for every sign pattern `σ` and test `x`,
`∑ⱼ σⱼ (aⱼ·x) = ∑ᵢ (Πᵀσ)ᵢ (aᵢ·x)`, i.e. the linear process equals the projected
process paired with `Ax`.  This is the statement that `Π A = A` on the column
space, unwound through the Gram form.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Projection
import Arlib.Approximation.LewisWeights.Duality
import Arlib.Approximation.LewisWeights.Concentration

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
  {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## The per-row process -/

/-- The `i`-th coordinate of the projected Rademacher process `Πᵀσ`, i.e. the
per-row process bounded by `Concentration.avg_sum_row_pow_le`:
`(Πᵀσ)ᵢ = ∑ⱼ σⱼ · wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ)`. -/
noncomputable def rowProc (w : ι → ℝ) (a : ι → d → ℝ) (s : ι → Bool) (i : ι) : ℝ :=
  ∑ j, Sgn (s j) * ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))

/-! ## The key algebraic identity: `Π A = A` on the column space -/

/-- **The crux.**  For any test `x` and sign pattern `σ`, the linear sign-process
`∑ⱼ σⱼ (aⱼ·x)` equals the projected process `∑ᵢ (Πᵀσ)ᵢ (aᵢ·x)`.

Writing `c := ∑ⱼ σⱼ aⱼ` and `u := M⁻¹ c`, `projT_apply` turns each `rowProc σ i`
into `wᵢ⁻¹ (aᵢ·u)`, so `∑ᵢ rowProc σ i (aᵢ·x) = ∑ᵢ wᵢ⁻¹ (aᵢ·u)(aᵢ·x) = u ⬝ᵥ (M x)`
by the Gram quadratic form.  Moving the symmetric `M⁻¹` across the dot product
(`dotProduct_mulVec_symm` with `gram_inv_transpose`) gives `c ⬝ᵥ (M⁻¹ (M x)) =
c ⬝ᵥ x` (`gram_inv_mulVec_gram_mulVec`), which distributes back to
`∑ⱼ σⱼ (aⱼ·x)`. -/
theorem process_eq_sum_rowProc (hL : IsLewis w a) (s : ι → Bool) (x : d → ℝ) :
    ∑ j, Sgn (s j) * (a j ⬝ᵥ x) = ∑ i, rowProc w a s i * (a i ⬝ᵥ x) := by
  symm
  calc ∑ i, rowProc w a s i * (a i ⬝ᵥ x)
      = ∑ i, (w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ (∑ j, Sgn (s j) • a j)))
            * (a i ⬝ᵥ x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [rowProc]
        rw [projT_apply]
    _ = ((gram w a)⁻¹ *ᵥ (∑ j, Sgn (s j) • a j)) ⬝ᵥ (gram w a *ᵥ x) :=
        (dotProduct_gram_mulVec w a x _).symm
    _ = (gram w a *ᵥ x) ⬝ᵥ ((gram w a)⁻¹ *ᵥ (∑ j, Sgn (s j) • a j)) :=
        dotProduct_comm _ _
    _ = (∑ j, Sgn (s j) • a j) ⬝ᵥ ((gram w a)⁻¹ *ᵥ (gram w a *ᵥ x)) :=
        dotProduct_mulVec_symm (gram_inv_transpose w a) (gram w a *ᵥ x) _
    _ = (∑ j, Sgn (s j) • a j) ⬝ᵥ x := by rw [gram_inv_mulVec_gram_mulVec hL x]
    _ = ∑ j, Sgn (s j) * (a j ⬝ᵥ x) := by
        rw [dotProduct_comm, dotProduct_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]

/-! ## The pointwise sup-bridge -/

/-- **The pointwise sup-bridge.**  For a test `x` with `‖Ax‖₁ = ∑ⱼ|aⱼ·x| ≤ 1`,
the `2k`-th power of the linear sign-process is bounded by the sum of the `2k`-th
powers of the per-row processes.  Rewriting the base by `process_eq_sum_rowProc`
and applying the ℓ₁/ℓ∞ even-power duality `dot_pow_le_sum_abs_pow` (test vector
`yᵢ = aᵢ·x`), then `|·|^{2k} = ·^{2k}` since `2k` is even. -/
theorem process_pow_le_sum_rowProc_pow [Nonempty ι] (hL : IsLewis w a) (s : ι → Bool)
    (x : d → ℝ) (hx : ∑ j, |a j ⬝ᵥ x| ≤ 1) (k : ℕ) :
    (∑ j, Sgn (s j) * (a j ⬝ᵥ x)) ^ (2 * k) ≤ ∑ i, (rowProc w a s i) ^ (2 * k) := by
  have hev : Even (2 * k) := ⟨k, two_mul k⟩
  rw [process_eq_sum_rowProc hL s x]
  calc (∑ i, rowProc w a s i * (a i ⬝ᵥ x)) ^ (2 * k)
      ≤ ∑ i, |rowProc w a s i| ^ (2 * k) :=
        dot_pow_le_sum_abs_pow (rowProc w a s) (fun i => a i ⬝ᵥ x) hx k
    _ = ∑ i, (rowProc w a s i) ^ (2 * k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hev.pow_abs]

/-! ## The moment bound on the full process -/

/-- **The sup-bridge moment bound.**  Under the Lewis property with all weights
`≤ U`, the `2k`-th Rademacher moment of the full linear sign-process against any
test `x` with `‖Ax‖₁ ≤ 1` is at most `n·(2ekU)^k`.

`avg` is monotone, the integrand is dominated pointwise by the sum of per-row
powers (`process_pow_le_sum_rowProc_pow`), and that average is `avg_sum_row_pow_le`. -/
theorem avg_process_pow_le [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) (x : d → ℝ) (hx : ∑ j, |a j ⬝ᵥ x| ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    avg (fun s => (∑ j, Sgn (s j) * (a j ⬝ᵥ x)) ^ (2 * k))
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k := by
  have hmono : avg (fun s => (∑ j, Sgn (s j) * (a j ⬝ᵥ x)) ^ (2 * k))
      ≤ avg (fun s => ∑ i, (rowProc w a s i) ^ (2 * k)) :=
    avg_mono fun s => process_pow_le_sum_rowProc_pow hL s x hx k
  refine hmono.trans ?_
  exact avg_sum_row_pow_le hL hw hU hk

end Arlib.Approximation.LewisWeights
