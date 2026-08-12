/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Route A: the optimal-in-`d` concentration of the Rademacher process

The mathematical heart of Cohen–Peng's optimal ℓ₁ row-sampling bound, reached by
an **elementary moment method on the supremum** — no ε-net, and no matrix
Chernoff.

The finite moment bound `Concentration.avg_sum_row_pow_le` controls
`𝔼_σ[∑ᵢ (Πᵀσ)ᵢ^{2k}] ≤ n (2 e k U)^k`, and the sup-bridge
`SupBridge.process_pow_le_sum_rowProc_pow` (`lem:lewlinf`) shows, *pointwise in
`σ`*, that the whole family of query processes is dominated by that single finite
sum:

    `(∑ⱼ σⱼ (aⱼ·x))^{2k} ≤ ∑ᵢ (Πᵀσ)ᵢ^{2k}`   for every `x` with `‖Ax‖₁ ≤ 1`.

Because the right-hand side does not depend on `x`, the deviation event
`{σ : ∃ x, ‖Ax‖₁ ≤ 1 ∧ |σᵀAx| ≥ c}` is contained in
`{σ : ∑ᵢ (Πᵀσ)ᵢ^{2k} ≥ c^{2k}}`, so Markov on that *single* nonnegative variable
bounds the probability that **any** query deviates — in one shot, with no union
bound over a net.  This is exactly what removes the `Θ(d log d)` net-entropy
factor that costs Route B (`Embed.lean`) its extra power of `d`.

    `Pr_σ[∃ x, ‖Ax‖₁ ≤ 1 ∧ |σᵀAx| ≥ c] ≤ n (2 e k U)^k / c^{2k}`
    (`process_uniform_tail`).

With the Lewis-weight cap `U = Θ(ε²/k)` this is `< 1`, and — via the trace
identity `∑ w̄ᵢ = d` (`Trace.sum_lewis_eq_card`), which fixes the sample count at
`N = ∑ pᵢ = (1/U)·∑ w̄ᵢ = Θ(d k / ε²)` — gives the optimal dependence on `d`.

What remains to reach the *sampling* statement (as opposed to this Rademacher-
process statement) is the classical `momentreduct` reduction — subtract an
independent copy, random-sign-swap, and strip the `|·|` by the Ledoux–Talagrand
`comparison` contraction — none of which uses matrix Chernoff; see
`docs/dev/LewisWeights-ROUTE_A_PLAN.md`.  This file proves the concentration core those steps feed.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.SupBridge
import Arlib.Approximation.LewisWeights.Probability

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix Classical
open Finset Arlib

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

omit [DecidableEq ι] in
/-- The finite sum of squared row processes is nonnegative (each term is an even
power). -/
theorem sum_rowProc_pow_nonneg (s : ι → Bool) (k : ℕ) :
    0 ≤ ∑ i, (rowProc w a s i) ^ (2 * k) :=
  Finset.sum_nonneg fun i _ => by rw [pow_mul]; positivity

/-- **The uniform tail of the Rademacher process over all queries** (the Route-A
concentration core).  For ℓ₁ Lewis weights capped by `U`, the probability that the
sign process `σᵀAx = ∑ⱼ σⱼ (aⱼ·x)` exceeds `c` in absolute value for *some* query
`x` in the ℓ₁ ball is at most `n (2 e k U)^k / c^{2k}` — a single moment-method
bound over the supremum, with no net.  `n = Fintype.card ι` is the number of
rows. -/
theorem process_uniform_tail [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {U : ℝ} (hU : ∀ i, w i ≤ U) {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) :
    (radProb ι).Pr (Finset.univ.filter (fun s => ∃ x : d → ℝ,
        (∑ j, |a j ⬝ᵥ x| ≤ 1) ∧ c ≤ |∑ j, Sgn (s j) * (a j ⬝ᵥ x)|))
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k / c ^ (2 * k) := by
  classical
  have hck : (0 : ℝ) < c ^ (2 * k) := by positivity
  -- The deviation event is contained in `{ ∑ᵢ (Πᵀσ)ᵢ^{2k} ≥ c^{2k} }`.
  have hsub : (Finset.univ.filter (fun s => ∃ x : d → ℝ,
        (∑ j, |a j ⬝ᵥ x| ≤ 1) ∧ c ≤ |∑ j, Sgn (s j) * (a j ⬝ᵥ x)|))
      ⊆ Finset.univ.filter
          (fun s => c ^ (2 * k) ≤ ∑ i, (rowProc w a s i) ^ (2 * k)) := by
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨x, hx1, hxc⟩ := hs.2
    refine ⟨hs.1, ?_⟩
    have h1 : c ^ (2 * k) ≤ |∑ j, Sgn (s j) * (a j ⬝ᵥ x)| ^ (2 * k) :=
      pow_le_pow_left₀ hc.le hxc (2 * k)
    have h2 : |∑ j, Sgn (s j) * (a j ⬝ᵥ x)| ^ (2 * k)
        = (∑ j, Sgn (s j) * (a j ⬝ᵥ x)) ^ (2 * k) :=
      (Even.pow_abs ⟨k, two_mul k⟩ _)
    have h3 : (∑ j, Sgn (s j) * (a j ⬝ᵥ x)) ^ (2 * k) ≤ ∑ i, (rowProc w a s i) ^ (2 * k) :=
      process_pow_le_sum_rowProc_pow hL s x hx1 k
    rw [h2] at h1
    exact le_trans h1 h3
  calc (radProb ι).Pr (Finset.univ.filter (fun s => ∃ x : d → ℝ,
          (∑ j, |a j ⬝ᵥ x| ≤ 1) ∧ c ≤ |∑ j, Sgn (s j) * (a j ⬝ᵥ x)|))
      ≤ (radProb ι).Pr (Finset.univ.filter
          (fun s => c ^ (2 * k) ≤ ∑ i, (rowProc w a s i) ^ (2 * k))) :=
        (radProb ι).Pr_mono hsub
    _ ≤ avg (fun s => ∑ i, (rowProc w a s i) ^ (2 * k)) / c ^ (2 * k) :=
        avg_markov _ (fun s => sum_rowProc_pow_nonneg s k) hck
    _ ≤ (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k / c ^ (2 * k) := by
        gcongr
        exact avg_sum_row_pow_le hL hw hU hk

/-- **The optimal parameter choice.**  With the Lewis-weight cap driven to
`2 e² k U ≤ c²` and the moment order set to `k ≥ log(n/δ)`, the uniform tail
collapses below `δ`:

    `Pr_σ[∃ x, ‖Ax‖₁ ≤ 1 ∧ |σᵀAx| ≥ c] ≤ δ`.

The base of the moment power drops to `e⁻¹`, so `(…)^k ≤ e^{-k}`, and `n e^{-k} ≤ δ`
exactly when `k ≥ log(n/δ)`.  Reading `c = ε` and the cap `U = ε² / (2 e² k)`, and
recalling `∑ w̄ᵢ = d` (`Trace.sum_lewis_eq_card`) so the induced sample count is
`N = (1/U)·d = 2 e² k d / ε² = Θ(d · log(n/δ) · ε⁻²)`, this is the optimal-in-`d`
row count of Cohen–Peng's `thm:l1chernoff`, for the Rademacher (half-sampling)
process — no net, no matrix Chernoff. -/
theorem process_uniform_tail_le_delta [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {U c δ : ℝ} (hU : ∀ i, w i ≤ U) (hc : 0 < c) (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k)
    (hUc : 2 * Real.exp 1 ^ 2 * (k : ℝ) * U ≤ c ^ 2)
    (hklog : Real.log ((Fintype.card ι : ℝ) / δ) ≤ (k : ℝ)) :
    (radProb ι).Pr (Finset.univ.filter (fun s => ∃ x : d → ℝ,
        (∑ j, |a j ⬝ᵥ x| ≤ 1) ∧ c ≤ |∑ j, Sgn (s j) * (a j ⬝ᵥ x)|)) ≤ δ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hUpos : 0 ≤ U := le_trans (hw (Classical.arbitrary ι)).le (hU _)
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  refine le_trans (process_uniform_tail hL hw hU hc hk) ?_
  -- rewrite the tail as `n · B^k` with base `B = (2 e k U)/c²`
  have hpow : (Fintype.card ι : ℝ) * (2 * Real.exp 1 * (k : ℝ) * U) ^ k / c ^ (2 * k)
      = (Fintype.card ι : ℝ) * ((2 * Real.exp 1 * (k : ℝ) * U) / c ^ 2) ^ k := by
    rw [pow_mul, mul_div_assoc, div_pow]
  rw [hpow]
  set B : ℝ := (2 * Real.exp 1 * (k : ℝ) * U) / c ^ 2 with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  -- `B ≤ e⁻¹`
  have hBe : B ≤ Real.exp (-1) := by
    rw [hB, Real.exp_neg, ← one_div, le_div_iff₀ he1, div_mul_eq_mul_div, div_le_one hc2]
    nlinarith [hUc]
  -- `B^k ≤ e^{-k}`, hence `n·B^k ≤ n·e^{-k} ≤ δ`
  have hBk : B ^ k ≤ Real.exp (-(k : ℝ)) := by
    calc B ^ k ≤ Real.exp (-1) ^ k := pow_le_pow_left₀ hBnn hBe k
      _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfin : (Fintype.card ι : ℝ) * Real.exp (-(k : ℝ)) ≤ δ := by
    rw [← Real.exp_log hn, ← Real.exp_add]
    rw [show Real.log ((Fintype.card ι : ℝ) / δ) = Real.log (Fintype.card ι) - Real.log δ from
        Real.log_div hn.ne' hδ.ne'] at hklog
    calc Real.exp (Real.log (Fintype.card ι) + -(k : ℝ))
        ≤ Real.exp (Real.log δ) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = δ := Real.exp_log hδ
  calc (Fintype.card ι : ℝ) * B ^ k
      ≤ (Fintype.card ι : ℝ) * Real.exp (-(k : ℝ)) := by gcongr
    _ ≤ δ := hfin

end Arlib.Approximation.LewisWeights
