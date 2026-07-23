/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Tootsie Pop Algorithm: the law of its counter

The Tootsie Pop Algorithm (Huber, 2010) estimates a ratio of measures
`μ(B)/μ(B')` by repeatedly drawing from a *shell* and contracting it until the
draw lands in the *centre*.  Its entire analysis rests on one distributional
fact: **the number of contractions a run needs is Poisson** with parameter
`A = ln(μ(B)/μ(B'))`.  This file proves that fact in the elementary form it
actually takes.

## The reduction to a product of uniforms

TPA's ingredients — a nested family `A(β)` whose measure `μ(A(β))` is continuous
in `β` — exist precisely so that one contraction multiplies the measure by an
independent `Uniform(0,1)` factor: if `X` is drawn from `A(β)` and `β'` is the
least index whose set still contains `X`, then `μ(A(β'))/μ(A(β)) ∼ Uniform(0,1)`.
Establishing that for a particular family is the *user's* obligation.

Granting it, a run stops once the running product `U₁ ⋯ U_m` of independent
uniforms drops to `c = μ(B')/μ(B)`.  Write `N = min {m : U₁ ⋯ U_m ≤ c}` for the
number of contractions the run performs, *including* the last one — the one that
lands in the centre — so that `N ≥ 1` always.  Then

  `P(N − 1 ≥ m) = P(U₁ ⋯ U_m > c)`,

and everything reduces to computing that one number.

Note the offset: it is `N − 1`, not `N`, that is Poisson.  That is exactly the
algorithm's bookkeeping — Algorithm 1 does `k ← k − 1` before the loop and
`k ← k + 1` inside it, so a run contributes `N − 1` to the counter `k`.  Getting
this wrong shifts the estimate by a factor of `e`.  Sanity check at `m = 0`:
`tpaTail 0 c = 1 = P(N − 1 ≥ 0)`, whereas the offset-free reading would claim
`P(N ≥ 1) = 1 − c`, which is false since `N ≥ 1` always.

## What is proved

`tpaTail m c` is the closed form

  `tpaTail m c = 1 - c · ∑_{j < m} (ln(1/c))^j / j!`.

* `tpaTail_succ` — it satisfies the recursion `F_{m+1}(c) = ∫_c^1 F_m(c/u) du`
  obtained by conditioning `P(U₁ ⋯ U_{m+1} > c)` on `U₁`.  This is the only
  analysis in the file, and it is a single application of the fundamental theorem
  of calculus: the integrand has the explicit antiderivative `tpaAntideriv`.
  Note the integrand needs no truncation — for `u ≤ c` we would have `c/u ≥ 1`
  and `F_m` would vanish, which is why the integral runs from `c` rather than `0`.

* `tpaTail_sub` — consecutive tails differ by `c · (ln(1/c))^m / m!`.  Since
  `P(N − 1 = m) = P(N − 1 ≥ m) − P(N − 1 ≥ m+1)` and `c = e^{-A}`, this *is* the
  Poisson mass
  `e^{-A} A^m / m!`.  Given the closed form it is one `Finset.sum_range_succ`:
  the Poisson law falls out as pure algebra.

* `tendsto_tpaTail_atTop` — the tail tends to `0`, i.e. a run terminates almost
  surely, so `N` is a genuine random variable.

The point of routing through `tpaTail` is that the *hard* object — an `m`-fold
integral over `[0,1]^m` — is replaced by an induction each of whose steps is
one-dimensional.  No product measure appears anywhere in this file.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral

namespace Arlib.Algorithms.TPA

open scoped BigOperators
open MeasureTheory

/-! ## The closed form -/

/-- `tpaTail m c` is the probability that a product of `m` independent
`Uniform(0,1)` variables still exceeds `c` — equivalently, that a TPA run whose
centre-to-shell measure ratio is `c` performs **more than** `m` contractions, so
that its counter contribution `N - 1` is at least `m`.  The TPA index is
`A = -Real.log c = ln(1/c)`. -/
noncomputable def tpaTail (m : ℕ) (c : ℝ) : ℝ :=
  1 - c * ∑ j ∈ Finset.range m, (-Real.log c) ^ j / (Nat.factorial j)

@[simp] theorem tpaTail_zero (c : ℝ) : tpaTail 0 c = 1 := by
  simp [tpaTail]

/-- **The Poisson law, as pure algebra.**  Consecutive tails differ by
`c · (ln(1/c))^m / m!`.  Writing `c = e^{-A}` this is exactly the Poisson mass
`e^{-A} A^m / m!`, so the TPA counter contribution `N - 1` is `Poisson(A)`. -/
theorem tpaTail_sub (m : ℕ) (c : ℝ) :
    tpaTail m c - tpaTail (m + 1) c = c * (-Real.log c) ^ m / (Nat.factorial m) := by
  simp only [tpaTail, Finset.sum_range_succ]
  ring

/-- **A TPA run terminates almost surely.**  The probability of performing more
than `m` contractions tends to `0`, because the partial sums of `∑ A^j/j!`
converge to `e^A = 1/c`. -/
theorem tendsto_tpaTail_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m => tpaTail m c) Filter.atTop (nhds 0) := by
  have hser : HasSum (fun j : ℕ => (-Real.log c) ^ j / (Nat.factorial j))
      (Real.exp (-Real.log c)) := by
    have := NormedSpace.expSeries_div_hasSum_exp ℝ (-Real.log c)
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hpart := hser.tendsto_sum_nat
  have hexp : Real.exp (-Real.log c) = c⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hc]
  rw [hexp] at hpart
  have hlim : Filter.Tendsto (fun m => 1 - c * ∑ j ∈ Finset.range m,
      (-Real.log c) ^ j / (Nat.factorial j)) Filter.atTop (nhds (1 - c * c⁻¹)) :=
    tendsto_const_nhds.sub (hpart.const_mul c)
  rw [mul_inv_cancel₀ (ne_of_gt hc), sub_self] at hlim
  exact hlim

/-! ## The antiderivative -/

/-- The explicit antiderivative of `u ↦ tpaTail m (c/u)` on `(0, ∞)`.
Differentiating the `j`-th summand contributes `(ln u - ln c)^j / (u · j!)`, and
`c` times the sum of those is exactly what `tpaTail m (c/u)` subtracts from `1`. -/
noncomputable def tpaAntideriv (m : ℕ) (c u : ℝ) : ℝ :=
  u - c * ∑ j ∈ Finset.range m,
    (Real.log u - Real.log c) ^ (j + 1) / (Nat.factorial (j + 1))

/-- The antiderivative works: on `u > 0` its derivative is the integrand. -/
theorem hasDerivAt_tpaAntideriv (m : ℕ) {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    HasDerivAt (tpaAntideriv m c) (tpaTail m (c / u)) u := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hsum : HasDerivAt
      (fun x => ∑ j ∈ Finset.range m,
        (Real.log x - Real.log c) ^ (j + 1) / (Nat.factorial (j + 1)))
      (∑ j ∈ Finset.range m, (Real.log u - Real.log c) ^ j / (u * Nat.factorial j)) u := by
    apply HasDerivAt.sum
    intro j _
    have hlog : HasDerivAt (fun x => Real.log x - Real.log c) u⁻¹ u :=
      (Real.hasDerivAt_log hu0).sub_const _
    have hd := (hlog.pow (j + 1)).div_const ((Nat.factorial (j + 1) : ℝ))
    convert hd using 1
    have hfac : ((Nat.factorial (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℕ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfacpos : (0 : ℝ) < (Nat.factorial j : ℕ) := by
      exact_mod_cast Nat.factorial_pos j
    rw [hfac]
    field_simp
    ring
  have hmain : HasDerivAt (tpaAntideriv m c)
      (1 - c * ∑ j ∈ Finset.range m,
        (Real.log u - Real.log c) ^ j / (u * Nat.factorial j)) u := by
    simpa [tpaAntideriv] using (hasDerivAt_id u).sub (hsum.const_mul c)
  convert hmain using 1
  rw [tpaTail, Real.log_div (ne_of_gt hc) hu0, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_sub]
  have hfacpos : (0 : ℝ) < (Nat.factorial j : ℕ) := by
    exact_mod_cast Nat.factorial_pos j
  field_simp

/-! ## The recursion -/

/-- Every point of `[c, 1]` is positive when `c` is. -/
theorem pos_of_mem_uIcc {c u : ℝ} (hc : 0 < c) (hu : u ∈ Set.uIcc c 1) : 0 < u := by
  rcases Set.mem_uIcc.mp hu with h | h
  · exact lt_of_lt_of_le hc h.1
  · exact lt_of_lt_of_le zero_lt_one h.1

theorem continuousOn_tpaTail_div (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun u => tpaTail m (c / u)) (Set.uIcc c 1) := by
  have hne : ∀ u ∈ Set.uIcc c 1, u ≠ 0 := fun u hu => ne_of_gt (pos_of_mem_uIcc hc hu)
  have hdiv : ContinuousOn (fun u : ℝ => c / u) (Set.uIcc c 1) :=
    continuousOn_const.div continuousOn_id hne
  have hlog : ContinuousOn (fun u : ℝ => Real.log (c / u)) (Set.uIcc c 1) := by
    apply Real.continuousOn_log.comp hdiv
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero (ne_of_gt hc) (hne u hu)
  unfold tpaTail
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.mul hdiv
  apply continuousOn_finset_sum
  intro j _
  exact ((hlog.neg).pow j).div_const _

/-- **The recursion.**  `∫_c^1 tpaTail m (c/u) du = tpaTail (m+1) c`.

This is the identity obtained by conditioning `P(U₁ ⋯ U_{m+1} > c)` on the first
factor `U₁ = u`: the remaining `m` factors must exceed `c/u`, and for `u ≤ c` that
is impossible, which is why the integral starts at `c`.

The identity holds for every `c > 0`; the probabilistic reading needs
`c ∈ (0, 1]`. -/
theorem tpaTail_succ (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ u in c..1, tpaTail m (c / u)) = tpaTail (m + 1) c := by
  have hderiv : ∀ u ∈ Set.uIcc c 1,
      HasDerivAt (tpaAntideriv m c) (tpaTail m (c / u)) u := fun u hu =>
    hasDerivAt_tpaAntideriv m hc (pos_of_mem_uIcc hc hu)
  have hint : IntervalIntegrable (fun u => tpaTail m (c / u)) MeasureTheory.volume c 1 :=
    (continuousOn_tpaTail_div m hc).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : tpaAntideriv m c 1
      = 1 - c * ∑ j ∈ Finset.range m,
          (-Real.log c) ^ (j + 1) / (Nat.factorial (j + 1)) := by
    simp only [tpaAntideriv, Real.log_one, zero_sub]
  have h2 : tpaAntideriv m c c = c := by
    simp only [tpaAntideriv, sub_self]
    have hz : ∀ j ∈ Finset.range m,
        (0 : ℝ) ^ (j + 1) / (Nat.factorial (j + 1)) = 0 := by
      intro j _
      rw [zero_pow (Nat.succ_ne_zero j), zero_div]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, mul_zero, sub_zero]
  rw [h1, h2, tpaTail, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one]
  ring

end Arlib.Algorithms.TPA
