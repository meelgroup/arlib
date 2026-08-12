/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Amplification
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hoeffding for `PMF` products: discharging `MajorityConcentration`

`Arlib.Approximation.Amplification` proves median amplification — confidence
`3/4` becomes `1 - δ` at a `Θ(log(1/δ))` multiplicative cost — conditional on one
named hypothesis bundle, `MajorityConcentration`: *if each of `m` independent
runs lands in `S` with probability at least `3/4`, a strict majority of them do,
except with probability `exp(-m/8)`.*  This module **proves that bundle**
(`majorityConcentration`), so every theorem in `Amplification` — in particular
`IsFPRAS.amplify` and `IsFPRAS.amplify_isFPRAS` — is now unconditional, with
nothing imported and no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`.

## Why this is not a transport from `Arlib.Probability.Chernoff`

`Arlib.Probability.Chernoff` proves the multiplicative Chernoff bounds, but for
`Arlib.ProbSpace`/`FinProb` product spaces over a *finite* sample space, with the
count presented as `indicCount`.  A run here is a `PMF (ℝ × ℕ)`: the sample space
is uncountable and the `m`-fold product is the `PMF.bind` tower `repeatPMF`.  The
obvious bridge — push the product forward onto `Bool ^ m`, identify the count's
law with `PMF.binomial`, then match the binomial with a `FinProb` and quote a
Chernoff bound — is a long detour, and it does not even reach the target: the
*multiplicative* Chernoff lower tail at mean `3m/4` and threshold `m/2` gives
only `exp(-m/24)`, whereas `MajorityConcentration` fixes the sharp Hoeffding
constant `exp(-m/8)`.  Nothing weaker closes it.

So the argument here is run from first principles, directly on the `PMF` tower,
and it is short because it never leaves the monad.

## The argument

Write `N v = #{i | v i ∈ S}` for the good count and `p = P[X ∈ S] ≥ 3/4`.

1. **The moment generating function factors** (`pexp_repeatPMF_pow`).  For every
   `c : ℝ≥0∞`,
   `E_{repeatPMF μ m} [ c ^ N ] = (P[X ∉ S] + c · P[X ∈ S]) ^ m`.
   This is the only place independence is used, and it is used exactly as
   `repeatPMF` writes it: the proof is an induction along `repeatPMF`'s own
   recursion, with `pexp_bind` for the two `bind`s and `card_filter_cons` for the
   effect of `Fin.cons` on the count.  No product measure, no independence side
   condition, and — the point — **no binomial distribution**: the count's law is
   never named, only its generating function is, and that is all a Chernoff
   argument ever consumes.

2. **Markov at the Chernoff parameter `s = 1`** (`outProb_minority_le_mgf`).  A
   failed majority means `2N ≤ m`, hence `e^{m/2} · e^{-N} ≥ 1`, so the indicator
   of failure is dominated pointwise by `e^{m/2} · (e^{-1})^N`.  Taking
   expectations and applying step 1 at `c = e^{-1}` bounds the failure
   probability by `e^{m/2} · (P[X ∉ S] + e^{-1} p)^m`.

3. **The one-draw factor** (`mgf_step_le`).  `P[X ∉ S] + e^{-1} p` equals
   `e^{-1} + (1 - p)(1 - e^{-1})`, which is decreasing in `p`; at `p ≥ 3/4` it is
   at most `1/4 + (3/4)e^{-1}`.

4. **The constant** (`exp_half_mul_quarter_le`).  Everything now reduces to the
   single real inequality
   `e^{1/2} · (1/4 + (3/4)e^{-1}) ≤ e^{-1/8}`.
   Raising both sides to the eighth power clears every fractional exponent and
   leaves the polynomial inequality `(e + 3)^8 ≤ 65536 · e^3` in `e = exp 1`
   alone, which `2.718 < e < 2.719` settles with roughly `13%` of room.  Taking
   `m`-th powers (`exp_pow_bound`) turns this into `exp(-m/8)`.

The parameter `s = 1` is not arbitrary: it is exactly the value at which the
Chernoff exponent for a `3/4`-biased Bernoulli hits the Hoeffding constant
`2 · (1/4)² = 1/8`.  A different `s` would give a different — and, for the
statement of `MajorityConcentration`, a useless — constant.

## The supporting `PMF` expectation API

`pexp ν g = ∑' b, ν b * g b` is the expectation of an `ℝ≥0∞`-valued function
under a `PMF`.  Working in `ℝ≥0∞` rather than `ℝ` is deliberate: every
rearrangement below is a `tsum` manipulation, and in `ℝ≥0∞` those are
unconditional — there is no summability side goal anywhere, and
`ENNReal.tsum_comm` swaps the
two sums of `pexp_bind` for free.  Reality is restored once, at the very end, by
`ENNReal.ofReal`/`toReal`, where the quantities involved are already known to be
at most `1`.

`outProb_le_pexp` is Markov's inequality in the form the event algebra of
`Arlib.Approximation.Counting` wants (the event is read off the first coordinate,
the step count marginalised out), and `outProb_add_compl` is the complementation
identity that turns a bound on the failure probability into the `1 - exp(-m/8)`
lower bound the statement asks for.  Neither needs the sample space to be
measurable in any sense: a `PMF` is a `tsum`, and both are proved as such.

## Main results

* `pexp_repeatPMF_pow` — the moment generating function of the good count over
  an `m`-fold `PMF` product factors as an `m`-th power.  Reusable for any
  Chernoff-style bound on `repeatPMF`, at any parameter `c`.
* `exp_half_mul_quarter_le` — the numeric inequality that pins the constant `8`
  in `exp(-m/8)`, reduced to `(e + 3)^8 ≤ 65536 e^3`.
* `outProb_minority_le` — the Hoeffding bound itself, in `ℝ≥0∞`.
* `majorityConcentration` — `MajorityConcentration`, proved.  **Nothing in this
  file, or in `Amplification`, is imported or assumed any more.**
-/

namespace Arlib.Approximation

open scoped ENNReal Classical

/-! ## Expectations of `ℝ≥0∞`-valued functions under a `PMF` -/

/-- The expectation of an `ℝ≥0∞`-valued function under a `PMF`. -/
noncomputable def pexp {β : Type*} (ν : PMF β) (g : β → ℝ≥0∞) : ℝ≥0∞ := ∑' b, ν b * g b

/-- The expectation under a point mass is the value at the point. -/
theorem pexp_pure {β : Type*} (b : β) (g : β → ℝ≥0∞) : pexp (PMF.pure b) g = g b := by
  rw [pexp, tsum_eq_single b]
  · simp
  · intro b' hb'
    simp [PMF.pure_apply, hb']

/-- The expectation under a `bind` is the iterated expectation. -/
theorem pexp_bind {β γ : Type*} (ν : PMF β) (κ : β → PMF γ) (g : γ → ℝ≥0∞) :
    pexp (ν.bind κ) g = pexp ν fun b => pexp (κ b) g := by
  simp only [pexp, PMF.bind_apply]
  rw [show (∑' c, (∑' b, ν b * κ b c) * g c) = ∑' c, ∑' b, ν b * (κ b c * g c) by
        refine tsum_congr fun c => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun b => by rw [mul_assoc]]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun _ => ENNReal.tsum_mul_left

/-- Expectation is monotone in the integrand. -/
theorem pexp_mono {β : Type*} (ν : PMF β) {g h : β → ℝ≥0∞} (hgh : ∀ b, g b ≤ h b) :
    pexp ν g ≤ pexp ν h :=
  ENNReal.tsum_le_tsum fun b => mul_le_mul_right (hgh b) _

/-- Constants pull out of an expectation. -/
theorem pexp_const_mul {β : Type*} (ν : PMF β) (c : ℝ≥0∞) (g : β → ℝ≥0∞) :
    (pexp ν fun b => c * g b) = c * pexp ν g := by
  rw [pexp, pexp, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun b => by ring

/-- Constants pull out of an expectation, on the right. -/
theorem pexp_mul_const {β : Type*} (ν : PMF β) (c : ℝ≥0∞) (g : β → ℝ≥0∞) :
    (pexp ν fun b => g b * c) = pexp ν g * c := by
  simp only [mul_comm _ c]
  exact pexp_const_mul ν c g

/-! ## Markov's inequality and complementation for `outProb` -/

variable {β : Type*}

/-- **Markov's inequality.**  If `g ≥ 1` on the event `{p | p.1 ∈ T}`, the
probability of the event is at most the expectation of `g`. -/
theorem outProb_le_pexp (ν : PMF (β × ℕ)) (T : Set β) (g : β × ℕ → ℝ≥0∞)
    (hg : ∀ x : β × ℕ, x.1 ∈ T → 1 ≤ g x) : outProb ν T ≤ pexp ν g := by
  rw [outProb, PMF.toOuterMeasure_apply, pexp]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x.1 ∈ T
  · rw [Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T} from hx)]
    exact le_mul_of_one_le_right' (hg x hx)
  · rw [Set.indicator_of_notMem (show x ∉ {p : β × ℕ | p.1 ∈ T} from hx)]
    exact zero_le

/-- An event and its complement have output probabilities summing to `1`. -/
theorem outProb_add_compl (ν : PMF (β × ℕ)) (T : Set β) :
    outProb ν T + outProb ν Tᶜ = 1 := by
  rw [outProb, outProb, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add,
    ← PMF.tsum_coe ν]
  refine tsum_congr fun x => ?_
  by_cases hx : x.1 ∈ T <;>
    simp [Set.indicator_apply, hx]

/-- The real form of `outProb_add_compl`. -/
theorem outProbR_compl (ν : PMF (β × ℕ)) (T : Set β) :
    outProbR ν Tᶜ = 1 - outProbR ν T := by
  have h := outProb_add_compl ν T
  have := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (outProb_ne_top ν T) (outProb_ne_top ν Tᶜ), ENNReal.toReal_one] at this
  simp only [outProbR]
  linarith

/-! `outProbR_le_one` and `outProbR_nonneg` were proved here and, independently
and identically, in `Arlib.Approximation.Sampling`.  Both now live in
`Arlib.Approximation.Counting`, the common ancestor — keeping either copy made
the area root `Arlib.Approximation` fail to elaborate, since it imports both. -/

/-- An output probability is recovered from its real shadow by `ENNReal.ofReal`. -/
theorem ofReal_outProbR (ν : PMF (β × ℕ)) (T : Set β) :
    ENNReal.ofReal (outProbR ν T) = outProb ν T :=
  ENNReal.ofReal_toReal (outProb_ne_top ν T)

/-! ## The count of good coordinates, and how it splits under `Fin.cons` -/

/-- Consing one more draw onto a vector adds the new draw's indicator to the
count of coordinates landing in `S`.  This is the combinatorial content of the
`repeatPMF` recursion. -/
theorem card_filter_cons {m : ℕ} (S : Set ℝ) (a : ℝ) (v : Fin m → ℝ) :
    (Finset.univ.filter fun i : Fin (m + 1) => (Fin.cons a v : Fin (m + 1) → ℝ) i ∈ S).card
      = (if a ∈ S then 1 else 0) + (Finset.univ.filter fun i : Fin m => v i ∈ S).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

/-! ## The moment generating function of the good count

The whole probabilistic content of `MajorityConcentration` is this one identity:
the expectation of `c ^ (number of good coordinates)` over the `m`-fold
independent product factors into the `m`-th power of its one-draw value. -/

/-- The one-draw moment generating function: `E[c ^ [X ∈ S]]` splits into the
failure probability plus `c` times the success probability. -/
theorem pexp_pow_indicator (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (c : ℝ≥0∞) :
    (pexp μ fun p => c ^ (if p.1 ∈ S then 1 else 0))
      = outProb μ Sᶜ + outProb μ S * c := by
  rw [pexp, outProb, outProb, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x.1 ∈ S <;> simp [Set.indicator_apply, hx]

/-- **The moment generating function of the good count factors.**

For every `c : ℝ≥0∞`, the expectation of `c ^ #{i | v i ∈ S}` over the `m`-fold
independent product `repeatPMF μ m` is the `m`-th power of the one-draw value
`P[X ∉ S] + c · P[X ∈ S]`.

This is the *only* place independence is used, and it is used exactly as
`repeatPMF` presents it: the proof is an induction along the same recursion,
with `pexp_bind` for the `bind`s, `card_filter_cons` for the count, and
`pexp_const_mul` to pull the new factor out of the inner expectation.  No
product measure, no independence side condition, and no appeal to the binomial
distribution is needed. -/
theorem pexp_repeatPMF_pow (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (c : ℝ≥0∞) : ∀ m : ℕ,
    (pexp (repeatPMF μ m) fun q => c ^ (Finset.univ.filter fun i => q.1 i ∈ S).card)
      = (outProb μ Sᶜ + outProb μ S * c) ^ m := by
  intro m
  induction m with
  | zero => rw [repeatPMF, pexp_pure]; simp
  | succ n ih =>
    rw [repeatPMF, pexp_bind]
    have key : ∀ p : ℝ × ℕ,
        (pexp ((repeatPMF μ n).bind fun q =>
            PMF.pure (Fin.cons p.1 q.1, p.2 + q.2))
          fun q => c ^ (Finset.univ.filter fun i => q.1 i ∈ S).card)
          = c ^ (if p.1 ∈ S then 1 else 0) * (outProb μ Sᶜ + outProb μ S * c) ^ n := by
      intro p
      rw [pexp_bind]
      have : ∀ q : (Fin n → ℝ) × ℕ,
          (pexp (PMF.pure ((Fin.cons p.1 q.1 : Fin (n+1) → ℝ), p.2 + q.2))
            fun r => c ^ (Finset.univ.filter fun i => r.1 i ∈ S).card)
            = c ^ (if p.1 ∈ S then 1 else 0)
              * c ^ (Finset.univ.filter fun i => q.1 i ∈ S).card := by
        intro q
        rw [pexp_pure, ← pow_add, card_filter_cons]
      simp only [this]
      rw [pexp_const_mul, ih]
    simp only [key]
    rw [pexp_mul_const, pexp_pow_indicator, pow_succ']

/-! ## The numeric heart of the Hoeffding constant -/

/-- **The one numeric inequality the whole bound rests on.**

At the Chernoff parameter `s = 1`, one draw contributes a factor
`e^{1/2} · (1/4 + (3/4)e^{-1})` to the tail bound, and the target `exp(-m/8)`
asks for that factor to be at most `e^{-1/8}`.  Raising both sides to the eighth
power clears every fractional exponent and turns the claim into the polynomial
inequality `(e + 3)^8 ≤ 65536 · e^3` in `e = exp 1` alone, which the rational
bounds `2.718 < e < 2.719` settle with about `13%` to spare.

This is exactly where the constant `8` in `exp(-m/8)` — and hence the
`m = ⌈8 log(1/δ)⌉₊` of `IsFPRAS.amplify` — is decided. -/
theorem exp_half_mul_quarter_le : Real.exp (1/2) * (1/4 + 3/4 * Real.exp (-1))
    ≤ Real.exp (-(1:ℝ)/8) := by
  set E := Real.exp 1 with hEdef
  have hEpos : 0 < E := Real.exp_pos 1
  have hE1 : (2.718 : ℝ) < E := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hE2 : E < (2.719 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexpneg : Real.exp (-1) = E⁻¹ := by rw [Real.exp_neg]
  -- the polynomial inequality in `e`
  have hmain : (E + 3) ^ 8 ≤ 65536 * E ^ 3 := by
    have h1 : (E + 3) ^ 8 ≤ (5.719 : ℝ) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 8
    have h2 : (2.718 : ℝ) ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ (by norm_num) hE1.le 3
    have h3 : (5.719 : ℝ) ^ 8 ≤ 65536 * (2.718 : ℝ) ^ 3 := by norm_num
    linarith
  refine le_of_pow_le_pow_left₀ (n := 8) (by norm_num) (Real.exp_nonneg _) ?_
  have hlhs : (Real.exp (1/2) * (1/4 + 3/4 * Real.exp (-1))) ^ 8
      = (E + 3) ^ 8 / (65536 * E ^ 4) := by
    rw [mul_pow, hexpneg, ← Real.exp_nat_mul]
    have h4 : ((8 : ℕ) : ℝ) * (1/2) = 4 := by norm_num
    rw [h4, show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul, ← hEdef]
    field_simp
    ring
  have hrhs : (Real.exp (-(1:ℝ)/8)) ^ 8 = E⁻¹ := by
    rw [← Real.exp_nat_mul]
    have h5 : ((8 : ℕ) : ℝ) * (-(1:ℝ)/8) = -1 := by norm_num
    rw [h5, hexpneg]
  rw [hlhs, hrhs, div_le_iff₀ (by positivity)]
  have h6 : E⁻¹ * (65536 * E ^ 4) = 65536 * E ^ 3 := by field_simp
  rw [h6]
  exact hmain

/-- Raising the one-draw bound to the `m`-th power: this is where `exp(-1/8)`
per draw becomes `exp(-m/8)` for the whole run. -/
theorem exp_pow_bound {x : ℝ} (hx0 : 0 ≤ x)
    (hx : Real.exp (1/2) * x ≤ Real.exp (-(1:ℝ)/8)) (m : ℕ) :
    Real.exp ((m : ℝ)/2) * x ^ m ≤ Real.exp (-(m : ℝ)/8) := by
  have h1 : Real.exp ((m : ℝ)/2) = Real.exp (1/2) ^ m := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp (-(m : ℝ)/8) = Real.exp (-(1:ℝ)/8) ^ m := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hx m

/-! ## The tail bound -/

/-- **Markov's inequality at the Chernoff parameter `s = 1`.**

On the event that a strict majority *fails*, the good count `N` satisfies
`2N ≤ m`, hence `e^{m/2} · e^{-N} ≥ 1`; so the indicator of that event is
dominated by `e^{m/2} · (e^{-1})^N`, whose expectation `pexp_repeatPMF_pow`
evaluates in closed form. -/
theorem outProb_minority_le_mgf (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (m : ℕ) :
    outProb (repeatPMF μ m)
        {v : Fin m → ℝ | ¬ m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}
      ≤ ENNReal.ofReal (Real.exp ((m : ℝ)/2))
        * (outProb μ Sᶜ + outProb μ S * ENNReal.ofReal (Real.exp (-1))) ^ m := by
  rw [← pexp_repeatPMF_pow μ S (ENNReal.ofReal (Real.exp (-1))) m, ← pexp_const_mul]
  refine outProb_le_pexp _ _ _ ?_
  intro x hx
  have hle : 2 * (Finset.univ.filter fun i => x.1 i ∈ S).card ≤ m := not_lt.mp hx
  have hNR : (((Finset.univ.filter fun i => x.1 i ∈ S).card : ℕ) : ℝ) ≤ (m : ℝ)/2 := by
    have h2 : ((2 * (Finset.univ.filter fun i => x.1 i ∈ S).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hle
    push_cast at h2
    linarith
  rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← Real.exp_nat_mul, ← Real.exp_add, ENNReal.one_le_ofReal]
  exact Real.one_le_exp (by linarith)

/-- **The one-draw factor, bounded using the success probability `p ≥ 3/4`.**

`P[X ∉ S] + e^{-1} · P[X ∈ S] = e^{-1} + (1 - p)(1 - e^{-1})` is decreasing in
`p`, so `p ≥ 3/4` caps it at `1/4 + (3/4)e^{-1}`. -/
theorem mgf_step_le (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (h : 3/4 ≤ outProbR μ S) :
    outProb μ Sᶜ + outProb μ S * ENNReal.ofReal (Real.exp (-1))
      ≤ ENNReal.ofReal (1/4 + 3/4 * Real.exp (-1)) := by
  have hp1 : outProbR μ S ≤ 1 := outProbR_le_one μ S
  have hexp0 : (0 : ℝ) ≤ Real.exp (-1) := Real.exp_nonneg _
  have hexp1 : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  rw [← ofReal_outProbR, ← ofReal_outProbR, ← ENNReal.ofReal_mul (outProbR_nonneg μ S),
    ← ENNReal.ofReal_add (outProbR_nonneg μ _) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [outProbR_compl]
  nlinarith [h, hp1, hexp0, hexp1]

/-- **The Hoeffding bound for `repeatPMF`, in `ℝ≥0∞`.**  A strict majority of `m`
independent runs fails to land in `S` with probability at most `exp(-m/8)`. -/
theorem outProb_minority_le (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (m : ℕ)
    (h : 3/4 ≤ outProbR μ S) :
    outProb (repeatPMF μ m)
        {v : Fin m → ℝ | ¬ m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}
      ≤ ENNReal.ofReal (Real.exp (-(m : ℝ)/8)) := by
  have hstep := mgf_step_le μ S h
  refine le_trans (outProb_minority_le_mgf μ S m) ?_
  refine le_trans (mul_le_mul_right (pow_le_pow_left' hstep m) _) ?_
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (exp_pow_bound (by positivity) exp_half_mul_quarter_le m)

/-! ## The theorem -/

/-- **The concentration bound behind median amplification, proved.**

If each of `m` independent trials lands in `S` with probability at least `3/4`,
then a strict majority of them do, except with probability `exp(-m/8)`.

This discharges the `MajorityConcentration` hypothesis of
`Arlib.Approximation.Amplification`, so every theorem there — in particular
`IsFPRAS.amplify` and `IsFPRAS.amplify_isFPRAS` — becomes unconditional. -/
theorem majorityConcentration : MajorityConcentration where
  majority_ge := by
    intro μ S m h
    have hcompl : {v : Fin m → ℝ | m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}
        = {v : Fin m → ℝ | ¬ m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}ᶜ := by
      ext v; simp
    have hbad : outProbR (repeatPMF μ m)
        {v : Fin m → ℝ | ¬ m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}
        ≤ Real.exp (-(m : ℝ)/8) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) (outProb_minority_le μ S m h)
    rw [hcompl, outProbR_compl]
    linarith

end Arlib.Approximation
