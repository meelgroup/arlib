/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Markov's inequality and linearity of expectation over finite sums

Two elementary but pervasively used facts, proved from first principles over
`FinProb`:

* **Linearity over a finite index** (`Ex_sum`): `Ex[∑_i X_i] = ∑_i Ex[X_i]`.
* **Markov's inequality** (`markov`): `Pr[X ≥ a] ≤ Ex[X]/a` for `X ≥ 0`, `a > 0`.

No `sorry`.
-/
import Arlib.Probability.CondExp

namespace Arlib.Probability

open Finset

namespace FinProb

variable (P : FinProb)

/-- **Linearity of expectation over a finite index set.**
`Ex[∑_{i∈s} X_i] = ∑_{i∈s} Ex[X_i]`. -/
theorem Ex_sum {ι : Type*} (s : Finset ι) (X : ι → P.Ω → ℝ) :
    P.Ex (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, P.Ex (X i) := by
  unfold Ex
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]

/-- **Markov's inequality.**  For a nonnegative random variable `X` and `a > 0`,
the probability that `X ≥ a` is at most `Ex[X]/a`. -/
theorem markov (X : P.Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    P.Pr (univ.filter (fun ω => a ≤ X ω)) ≤ P.Ex X / a := by
  rw [le_div_iff₀ ha, Pr]
  calc (∑ ω ∈ univ.filter (fun ω => a ≤ X ω), P.mass ω) * a
      = ∑ ω ∈ univ.filter (fun ω => a ≤ X ω), P.mass ω * a := by
        rw [Finset.sum_mul]
    _ ≤ ∑ ω ∈ univ.filter (fun ω => a ≤ X ω), P.mass ω * X ω := by
        apply Finset.sum_le_sum
        intro ω hω
        rw [Finset.mem_filter] at hω
        exact mul_le_mul_of_nonneg_left hω.2 (P.mass_nonneg ω)
    _ ≤ ∑ ω, P.mass ω * X ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω _ _
        exact mul_nonneg (P.mass_nonneg ω) (hX ω)
    _ = P.Ex X := rfl

/-- The variance `Var[X] = Ex[(X - Ex[X])²]`. -/
def Var (X : P.Ω → ℝ) : ℝ := P.Ex (fun ω => (X ω - P.Ex X) ^ 2)

theorem Var_nonneg (X : P.Ω → ℝ) : 0 ≤ P.Var X :=
  P.Ex_nonneg (fun _ => sq_nonneg _)

/-- **Computational form of the variance.**  `Var[X] = Ex[X²] - (Ex[X])²`. -/
theorem Var_eq (X : P.Ω → ℝ) :
    P.Var X = P.Ex (fun ω => (X ω) ^ 2) - (P.Ex X) ^ 2 := by
  unfold Var
  have hexp : (fun ω => (X ω - P.Ex X) ^ 2)
      = (fun ω => (X ω) ^ 2 + ((-2 * P.Ex X) * X ω + (P.Ex X) ^ 2)) := by
    funext ω; ring
  rw [hexp, P.Ex_add (fun ω => (X ω) ^ 2)
        (fun ω => (-2 * P.Ex X) * X ω + (P.Ex X) ^ 2),
    P.Ex_add (fun ω => (-2 * P.Ex X) * X ω) (fun _ => (P.Ex X) ^ 2),
    P.Ex_smul (-2 * P.Ex X) X, P.Ex_const]
  ring

/-- **Chebyshev's inequality.**  `Pr[|X - Ex X| ≥ a] ≤ Var[X]/a²` for `a > 0`.
Obtained from Markov applied to the nonnegative variable `(X - Ex X)²`. -/
theorem chebyshev (X : P.Ω → ℝ) {a : ℝ} (ha : 0 < a) :
    P.Pr (univ.filter (fun ω => a ≤ |X ω - P.Ex X|)) ≤ P.Var X / a ^ 2 := by
  have hev : (univ.filter (fun ω => a ≤ |X ω - P.Ex X|))
      = (univ.filter (fun ω => a ^ 2 ≤ (X ω - P.Ex X) ^ 2)) := by
    apply Finset.filter_congr
    intro ω _
    rw [← sq_abs (X ω - P.Ex X),
      pow_le_pow_iff_left₀ ha.le (abs_nonneg _) (by norm_num)]
  rw [hev]
  have hmk := P.markov (fun ω => (X ω - P.Ex X) ^ 2) (fun ω => sq_nonneg _)
    (a := a ^ 2) (by positivity)
  exact hmk

end FinProb
end Arlib.Probability
