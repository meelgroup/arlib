/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Concentration of an empirical frequency

The estimator behind every "learn a distribution from samples" argument: draw
independent samples and count how often each outcome appears.

Given a product space `prodSpace μ` over a common outcome type `X` and a block
`s` of coordinates that all draw `x` with the *same* probability `p`, the count

  `countEq s x ω = #{ j ∈ s : ω j = x }`

is a sum of `|s|` independent `{0,1}` indicators with mean `|s|·p`.  Two facts
follow, and they are the whole file:

* `Ex_countEq` — the mean is `∑_{j ∈ s} μ j x`, i.e. `|s|·p` in the identically
  distributed case;
* `Pr_countEq_deviation_le` — an **exponential** tail:

    `Pr[ |countEq s x ω − |s|·p| ≥ |s|·ε ] ≤ exp(−b/35)`

  whenever `100 ≤ b ≤ |s|·ε²` and `ε ≤ 1`.

The tail is `KWiseChernoff.exp_tail_of_budget` instantiated at `a = |s|·ε`, using
`IIDProduct.kwiseIndep_coord` to discharge the independence hypothesis at budget
`k = |s|` — which is legitimate precisely because product coordinates are `k`-wise
independent for *every* `k`, not merely for small `k`.

`Pr_countEq_deviation_le_delta` repackages it in the form a sample-complexity
argument wants: to make the failure probability at most `δ`, take
`|s|·ε² ≥ max 100 (35·log(1/δ))` — a sample count growing like **`log(1/δ)`**, not
`1/δ`.  (Chebyshev would give the weaker `1/δ`; the exponential tail is what
makes the budget logarithmic in the confidence.)

* `sum_countEq` — the counts over all outcomes partition the block, `∑ x, countEq
  s x ω = |s|`.  This is what makes an empirical frequency vector a genuine
  probability distribution.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.IIDProduct

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-! ## The empirical count -/

/-- The number of coordinates in the block `s` whose outcome is `x`. -/
def countEq (s : Finset ι) (x : X) (ω : ι → X) : ℕ :=
  (s.filter fun j => ω j = x).card

omit [Fintype ι] [DecidableEq ι] [Fintype X] in
theorem countEq_eq_sum (s : Finset ι) (x : X) (ω : ι → X) :
    ((countEq s x ω : ℕ) : ℝ) = ∑ j ∈ s, (if ω j = x then (1 : ℝ) else 0) := by
  rw [countEq, Finset.sum_boole]

omit [Fintype ι] [DecidableEq ι] [Fintype X] in
theorem countEq_le (s : Finset ι) (x : X) (ω : ι → X) : countEq s x ω ≤ s.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- **The counts partition the block.**  Summing over all outcomes recovers the
block size — so the empirical frequencies `countEq s x ω / |s|` really are a
probability distribution on `X`. -/
theorem sum_countEq (s : Finset ι) (ω : ι → X) :
    ∑ x, countEq s x ω = s.card := by
  exact (Finset.card_eq_sum_card_fiberwise
    (f := ω) (s := s) (t := (Finset.univ : Finset X))
    (fun j _ => Finset.mem_univ _)).symm

/-! ## The mean -/

theorem Ex_countEq (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)
    (s : Finset ι) (x : X) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ((countEq s x ω : ℕ) : ℝ))
      = ∑ j ∈ s, μ j x := by
  have hrw : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ((countEq s x ω : ℕ) : ℝ))
      = (prodSpace μ h0 h1).toFinProb.Ex
          (fun ω => ∑ j ∈ s, (fun (y : X) => if y = x then (1:ℝ) else 0) (ω j)) := by
    congr 1
    funext ω
    exact countEq_eq_sum s x ω
  rw [hrw, FinProb.Ex_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Ex_apply μ h0 h1 j (fun y => if y = x then (1:ℝ) else 0)]
  simp

/-! ## The exponential tail -/

/-- **Concentration of an empirical frequency.**  If every coordinate of the
block `s` produces the outcome `x` with the same probability `p`, then the count
deviates from its mean `|s|·p` by `|s|·ε` with probability at most `exp(-b/35)`,
for any budget `b` with `100 ≤ b ≤ |s|·ε²`.

The `1/35` is `KWiseChernoff`'s absolute constant, not the sharp one; only its
being absolute matters. -/
theorem Pr_countEq_deviation_le (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (s : Finset ι) (x : X) {p : ℝ}
    (hp : ∀ j ∈ s, μ j x = p) (hp1 : p ≤ 1)
    {ε b : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s.card)
    (hb : 100 ≤ b) (hbm : b ≤ (s.card : ℝ) * ε ^ 2) :
    (prodSpace μ h0 h1).toFinProb.Pr (Finset.univ.filter fun ω =>
        (s.card : ℝ) * ε ≤ |((countEq s x ω : ℕ) : ℝ) - (s.card : ℝ) * p|)
      ≤ Real.exp (-b / 35) := by
  classical
  set N : ℝ := (s.card : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast hs
  -- the indicator family
  set Z : ι → (prodSpace μ h0 h1).toFinProb.Ω → ℝ :=
    fun j ω => (if ω j = x then (1 : ℝ) else 0) with hZdef
  have hind : KWiseIndep (prodSpace μ h0 h1).toFinProb s.card Z :=
    kwiseIndep_coord μ h0 h1 (fun _ y => if y = x then (1 : ℝ) else 0) s.card
  have hZ : IsIndicatorFamily Z := by
    intro j ω; rw [hZdef]; dsimp only; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- the mean
  have hsum : ∀ ω, (∑ j ∈ s, Z j ω) = ((countEq s x ω : ℕ) : ℝ) :=
    fun ω => (countEq_eq_sum s x ω).symm
  have hmean : (prodSpace μ h0 h1).toFinProb.Ex (fun ω' => ∑ j ∈ s, Z j ω') = N * p := by
    have h1' : (prodSpace μ h0 h1).toFinProb.Ex (fun ω' => ∑ j ∈ s, Z j ω')
        = (prodSpace μ h0 h1).toFinProb.Ex (fun ω' => ((countEq s x ω' : ℕ) : ℝ)) := by
      congr 1; funext ω; exact hsum ω
    rw [h1', Ex_countEq μ h0 h1 s x,
      Finset.sum_congr rfl (fun j hj => hp j hj), Finset.sum_const, nsmul_eq_mul, hN]
  -- `0 ≤ p`
  have hp0 : 0 ≤ p := by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hs
    rw [← hp j hj]; exact h0 j x
  have hbmN : b ≤ N * ε ^ 2 := by rw [hN]; exact hbm
  have hb0 : (0:ℝ) < b := by linarith
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  -- the three numeric side conditions
  have ha : 0 < N * ε := mul_pos hN0 hε0
  have hbmu : b * ((prodSpace μ h0 h1).toFinProb.Ex (fun ω' => ∑ j ∈ s, Z j ω'))
      ≤ (N * ε) ^ 2 := by
    rw [hmean]
    nlinarith [mul_le_mul_of_nonneg_left hp1 hb0.le, mul_le_mul_of_nonneg_right hbmN hN0.le]
  have hb2 : b ^ 2 ≤ (N * ε) ^ 2 := by
    have hbNe : b ≤ N * ε := le_trans hbmN (by nlinarith)
    nlinarith
  have hK : b ≤ ((s.card : ℕ) : ℝ) := by
    rw [← hN]
    nlinarith
  -- match the events
  have hev : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        N * ε ≤ |((countEq s x ω : ℕ) : ℝ) - N * p|)
      = (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        N * ε ≤ |(∑ j ∈ s, Z j ω)
          - (prodSpace μ h0 h1).toFinProb.Ex (fun ω' => ∑ j ∈ s, Z j ω')|) := by
    refine Finset.filter_congr (fun ω _ => ?_)
    rw [hmean, hsum ω]
  rw [hev]
  exact exp_tail_of_budget hind hZ s ha hb hbmu hb2 hK

/-- The same in the form a sample-complexity argument consumes: a block of
`|s| ≥ max 100 (35·log(1/δ)) / ε²` coordinates estimates the frequency of `x` to
within `ε` with confidence `1 - δ`.

The budget is **logarithmic** in `1/δ`. -/
theorem Pr_countEq_deviation_le_delta (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (s : Finset ι) (x : X) {p : ℝ}
    (hp : ∀ j ∈ s, μ j x = p) (hp1 : p ≤ 1)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hbudget : max 100 (35 * Real.log (1 / δ)) ≤ (s.card : ℝ) * ε ^ 2) :
    (prodSpace μ h0 h1).toFinProb.Pr (Finset.univ.filter fun ω =>
        (s.card : ℝ) * ε ≤ |((countEq s x ω : ℕ) : ℝ) - (s.card : ℝ) * p|)
      ≤ δ := by
  set b : ℝ := max 100 (35 * Real.log (1 / δ)) with hbdef
  have hb : (100 : ℝ) ≤ b := le_max_left _ _
  have hblog : 35 * Real.log (1 / δ) ≤ b := le_max_right _ _
  have hs : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · exfalso
      rw [h] at hbudget
      simp only [Nat.cast_zero, zero_mul] at hbudget
      linarith
    · exact h
  have hmain := Pr_countEq_deviation_le μ h0 h1 s x hp hp1 hε0 hε1 hs hb hbudget
  refine hmain.trans ?_
  have hlog : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one]; ring
  have hexpo : -b / 35 ≤ Real.log δ := by
    rw [hlog] at hblog; linarith
  calc Real.exp (-b / 35) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hexpo
    _ = δ := Real.exp_log hδ0

end Arlib.Probability
