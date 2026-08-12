/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Rademacher space as a finite probability space, and the moment method

The `avg` functional of `Rademacher.lean` is the expectation under the uniform
measure on sign patterns.  Here that measure is packaged as an honest
`Arlib.Probability.FinProb` — the uniform mass `2^{-|ι|}` on `ι → Bool` — so that the general
tools of `Arlib.Probability` (Markov's inequality) apply.

* `radProb ι` — the uniform Rademacher probability space.
* `radProb_Ex` — its expectation is exactly `avg`.
* `avg_markov` — Markov's inequality read through `avg`.
* `avg_pow_tail` — the **moment method**: a bound `avg (Y ^ (2k)) ≤ B` on the
  `2k`-th moment turns into the tail bound `Pr[Y ≥ c] ≤ B / c^{2k}`, the shape in
  which Cohen–Peng's `momBound` is consumed.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Concentration
import Arlib.Probability.Markov

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset

/-- The **uniform Rademacher probability space** on sign patterns `ι → Bool`:
every one of the `2^{|ι|}` patterns has mass `2^{-|ι|}`. -/
@[reducible] noncomputable def radProb (ι : Type) [Fintype ι] [DecidableEq ι] :
    Arlib.Probability.FinProb where
  Ω := ι → Bool
  μ :=
    { p := fun _ => ((2 : ℝ) ^ Fintype.card ι)⁻¹
      p_nonneg := fun _ => by positivity
      p_sum := by
        have hcard : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by
          rw [Fintype.card_fun, Fintype.card_bool]
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        push_cast
        rw [mul_inv_cancel₀ (by positivity)] }

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The expectation on `radProb` is exactly the Rademacher average `avg`. -/
theorem radProb_Ex (f : (ι → Bool) → ℝ) : (radProb ι).Ex f = avg f := by
  simp only [Arlib.Probability.FinProb.Ex, radProb, avg, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- **Markov's inequality**, read through `avg`. -/
theorem avg_markov (Y : (ι → Bool) → ℝ) (hY : ∀ ω, 0 ≤ Y ω) {c : ℝ} (hc : 0 < c) :
    (radProb ι).Pr (Finset.univ.filter (fun ω => c ≤ Y ω)) ≤ avg Y / c := by
  rw [← radProb_Ex]
  exact (radProb ι).markov Y hY hc

/-- **The moment method.**  If the `2k`-th moment of a nonnegative `Y` is at most
`B`, then `Y` exceeds `c > 0` with probability at most `B / c^{2k}`.  The event
`{Y ≥ c}` is contained in `{Y^{2k} ≥ c^{2k}}`, to which Markov applies. -/
theorem avg_pow_tail (Y : (ι → Bool) → ℝ) (_hY : ∀ ω, 0 ≤ Y ω) {c B : ℝ} (hc : 0 < c)
    {k : ℕ} (hB : avg (fun ω => Y ω ^ (2 * k)) ≤ B) :
    (radProb ι).Pr (Finset.univ.filter (fun ω => c ≤ Y ω)) ≤ B / c ^ (2 * k) := by
  have hck : (0 : ℝ) < c ^ (2 * k) := by positivity
  have hsub : (Finset.univ.filter (fun ω => c ≤ Y ω))
      ⊆ Finset.univ.filter (fun ω => c ^ (2 * k) ≤ Y ω ^ (2 * k)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, pow_le_pow_left₀ hc.le hω.2 (2 * k)⟩
  calc (radProb ι).Pr (Finset.univ.filter (fun ω => c ≤ Y ω))
      ≤ (radProb ι).Pr (Finset.univ.filter (fun ω => c ^ (2 * k) ≤ Y ω ^ (2 * k))) :=
        (radProb ι).Pr_mono hsub
    _ ≤ avg (fun ω => Y ω ^ (2 * k)) / c ^ (2 * k) :=
        avg_markov _ (fun ω => by rw [pow_mul]; positivity) hck
    _ ≤ B / c ^ (2 * k) := by gcongr
