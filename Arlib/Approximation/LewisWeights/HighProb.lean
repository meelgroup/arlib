/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The high-probability form of the ℓ₁ concentration bound

`Concentration.avg_sum_row_pow_le` bounds the `2k`-th Rademacher moment of the
finite process

`Q(σ) = ∑ᵢ (∑ⱼ σⱼ · wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ))^{2k}`   (`M = gram w a`)

by `n · (2 e k U)^k`.  Feeding that moment bound through Markov's inequality
(`Probability.avg_markov`, the moment method being already discharged since `Q`
is *itself* the sum of `2k`-th powers) yields the tail bound this file records:

* `finiteProcess_tail` — `Pr[Q ≥ t] ≤ n · (2 e k U)^k / t`.
* `momBound_highProb` — the complementary "with probability ≥ 1 − δ, `Q < t`"
  form, via `FinProb.Pr_compl`.

A small order-theoretic helper `max_abs_pow_le_sum_pow` — that the `l`-th power
of a finite max of absolute values is dominated by the sum of the `l`-th powers —
is included; it is the elementary step by which an `ℓ∞`-style maximum is absorbed
into the `∑ᵢ (…)^{2k}` shape of `Q`.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Probability
import Arlib.Probability.UnionBound

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset

/-! ## An elementary max/sum power inequality -/

/-- The `l`-th power of a finite maximum of absolute values is at most the sum of
the `l`-th powers: `(maxᵢ |cᵢ|)^l ≤ ∑ᵢ |cᵢ|^l`.  The maximiser `i₀` attains the
`sup'`, and its term `|c i₀|^l` is one nonnegative summand of the right-hand
sum. -/
theorem max_abs_pow_le_sum_pow {κ : Type*} [Fintype κ] [Nonempty κ]
    (c : κ → ℝ) (l : ℕ) :
    (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) ^ l ≤ ∑ i, |c i| ^ l := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |c i|)
  calc (Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)) ^ l
      = |c i₀| ^ l := by rw [hi₀]
    _ ≤ ∑ i, |c i| ^ l :=
        Finset.single_le_sum (f := fun i => |c i| ^ l)
          (fun i _ => pow_nonneg (abs_nonneg _) l) (Finset.mem_univ i₀)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## The finite-process high-probability bound -/

/-- **The finite-process tail bound.**  Under the Lewis property with all weights
`≤ U`, the finite process

`Q(σ) = ∑ᵢ (∑ⱼ σⱼ · wᵢ⁻¹ (aᵢ ⬝ᵥ M⁻¹ aⱼ))^{2k}`

exceeds any threshold `t > 0` with probability at most `n · (2 e k U)^k / t`.

Since `Q` is already the sum of `2k`-th powers, its expectation is bounded
directly by `avg_sum_row_pow_le`, and plain Markov (`avg_markov`) delivers the
tail. -/
theorem finiteProcess_tail (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    (radProb ι).Pr (Finset.univ.filter (fun s => t ≤
        ∑ i, (∑ j, Sgn (s j) *
          ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k)))
      ≤ ((Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k) / t := by
  have hQnn : ∀ s : ι → Bool, 0 ≤
      ∑ i, (∑ j, Sgn (s j) *
        ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k) := by
    intro s
    refine Finset.sum_nonneg fun i _ => ?_
    rw [pow_mul]; positivity
  have havg : avg (fun s => ∑ i, (∑ j, Sgn (s j) *
      ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k))
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k :=
    avg_sum_row_pow_le hL hw hU hk
  exact (avg_markov _ hQnn ht).trans (div_le_div_of_nonneg_right havg ht.le)

/-- **High-probability ("`Q < t` whp") form of the finite-process bound.**  With
probability at least `1 − n · (2 e k U)^k / t`, the finite process `Q` stays
below the threshold `t`.  This is `finiteProcess_tail` read through the
complement rule `FinProb.Pr_compl`. -/
theorem momBound_highProb (hL : IsLewis w a) (hw : ∀ i, 0 < w i) {U : ℝ}
    (hU : ∀ i, w i ≤ U) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    1 - ((Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k) / t
      ≤ (radProb ι).Pr (Finset.univ \ Finset.univ.filter (fun s => t ≤
          ∑ i, (∑ j, Sgn (s j) *
            ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j)))) ^ (2 * k))) := by
  rw [(radProb ι).Pr_compl]
  linarith [finiteProcess_tail hL hw hU hk ht]

end Arlib.Approximation.LewisWeights
