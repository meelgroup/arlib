/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Pinsker's inequality: `2‖ν − μ‖²_TV ≤ D(ν ‖ μ)`

Every entropy estimate in this development is stated in relative entropy rather
than total variation, and both `Techniques/EntropyVariational.lean` and
`Techniques/EntropyDecay.lean` say so in as many words: the latter names the
missing conversion as the one thing standing between its mixing bound
`D(P^t(x, ·) ‖ μ) ≤ ε` and a `MixesWithin` statement.  The conversion is
Pinsker's inequality, and this module supplies it, **with the sharp constant**:

  `2 ‖ν − μ‖²_TV ≤ D(ν ‖ μ)`,  equivalently  `‖ν − μ‖_TV ≤ √(D(ν ‖ μ)/2)`.

The proof is the classical one — reduce to a scalar inequality, then integrate
it against `μ` — but arranged so that the reduction is *pointwise* rather than
through the two-point marginalisation, which is what keeps it short.  The engine
is a single scalar estimate,

  `(3/2)·(t − 1)² ≤ (t log t − t + 1)·(t + 2)`,   (★)

the division-free form of the Padé bound `t log t − t + 1 ≥ (3/2)(t−1)²/(t+2)`.
Both `(3/2)` and the `+2` are forced: they are exactly the choice for which (★)
agrees with `t log t − t + 1` to *third* order at `t = 1`, and any smaller shift
than `+2` makes (★) false near `t = 1`.  Linearising (★) with the tangent-line
trick at the slope `c = (2/3)‖ν − μ‖_TV` turns it into a bound that is *additive*
in `x`, so summing needs no Cauchy–Schwarz and no square roots — the optimal `c`
is written down rather than obtained from an inequality.

## Main declarations

* `one_sub_inv_le_log` — `1 − 1/t ≤ log t`, the elementary bound in the
  direction opposite to `Real.log_le_sub_one_of_pos`.
* **`two_mul_sub_le_add_one_mul_log`** / `add_one_mul_log_le_two_mul_sub` — the
  **Padé bound** `log t ≥ 2(t−1)/(t+1)` for `t ≥ 1`, and its reversal for
  `t ≤ 1`, in division-free form.  This is the sharpest bound on `log` that is
  needed anywhere below, and the reason a first-order bound such as
  `log t ≤ t − 1` cannot suffice: Pinsker's constant is second-order tight at
  `t = 1`.
* `klTerm a b = a(log a − log b) − a + b` — the pointwise relative-entropy term,
  with `klDiv_eq_sum_klTerm` identifying `D(ν ‖ μ)` with its sum.
* **`three_div_two_mul_sq_le_klTerm_mul`** — (★), in the homogeneous two-variable
  form `(3/2)(a − b)² ≤ klTerm a b · (a + 2b)`.
* **`lin_le_klTerm`** — its linearisation: for *every* real `c`,
  `3c|a − b| − (3/2)c²(a + 2b) ≤ klTerm a b`.  Summing this over `x` with
  `c` a constant is the whole of the reduction.
* **`two_mul_tvDist_sq_le_klDiv`** — **Pinsker's inequality**,
  `2‖ν − μ‖²_TV ≤ D(ν ‖ μ)`, and `tvDist_le_sqrt_klDiv` in root form.
* `two_mul_sub_sq_le_klTerm_add_klTerm` — the **two-point case** as a corollary
  of the same linearisation: `2(p − q)² ≤ p log(p/q) + (1−p) log((1−p)/(1−q))`.
  It is the form Pinsker is usually stated in, and it is recorded separately
  because it is reusable outside this development.
* **`mixesWithin_of_klDiv_le`**, `mixesWithin_of_klDiv_le_two_mul_sq` — the
  payoff: a bound on the relative entropy of the `t`-step law is a
  `MixesWithin` statement.  `Techniques/EntropyDecay.lean`'s
  `EntropyContraction.klDiv_iter_row_le_of_log_le` composes with the first of
  these in one line.

## Absolute continuity is not optional

Every statement about distributions carries `hac : ∀ x, μ x = 0 → ν x = 0`.  It
cannot be dropped: with `Real.log 0 = 0` and the guarded `relDensity`, the
divergence `klDiv ν μ` of a point mass from a *disjoint* point mass evaluates to
`0` while the total variation distance is `1`.  The hypothesis is the same one
`tvDist_sq_le_chiSq` carries, and in the mixing applications it is discharged by
`μ` being fully supported.

## Which chain to use

There are now two routes from an `L²`/entropy estimate to total variation, and
they are not interchangeable:

* `TotalVariation.tvDist_sq_le_chiSq` — `‖ν − μ‖_TV ≤ ½√(D_{χ²})`;
* this module — `‖ν − μ‖_TV ≤ √(D_KL/2)`.

Since `EntropyVariational.klDiv_le_chiSq` gives `D_KL ≤ D_{χ²}`, chaining
Pinsker after it yields `‖ν − μ‖_TV ≤ √(D_{χ²}/2)`, which is **worse than
`tvDist_sq_le_chiSq` by a factor of `√2`**.  So: if the bound in hand is a χ²
bound, use `tvDist_sq_le_chiSq` and do not pass through relative entropy.
Pinsker earns its place only on divergence bounds that are *not* obtained from
χ² — that is, on `EntropyDecay`'s entropy-contraction bounds, whose whole point
is that the initial divergence of a point mass is `log(1/μ_min)` rather than
`1/μ_min`.  The `√2` lost here is a constant; the gain there is a logarithm.

## Sharpness

The constant `2` is optimal: `D(ν ‖ μ) / ‖ν − μ‖²_TV → 2` for two-point
distributions with `p, q → 1/2`, where (★) and the tangent-line step are both
tight.  No claim of sharpness is *proved* here — that would need a limit — but
no constant larger than `2` is claimed either.

Everything here is proved from first principles with no `sorry`.  No eigenvalue
appears.  The one departure from the area's usual diet is the pair of imports
`Mathlib.Analysis.Calculus.MeanValue` and
`Mathlib.Analysis.SpecialFunctions.Log.Deriv`: two derivatives are computed and
three monotonicity arguments are run, all on explicit one-variable functions of
`Real.log`, and nothing else analytic is used.  That departure is not avoidable
— see the note opening the next section for why `log t ≤ t − 1`, the sole
analytic input of `Techniques/Entropy.lean`, provably cannot reach the constant
`2`.
-/
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.TotalVariation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Two scalar bounds on the logarithm

`Techniques/Entropy.lean` is built entirely on `log t ≤ t − 1`.  That bound is
first-order tight at `t = 1` and no better, and Pinsker's inequality is
*second-order* tight there, so it cannot be reached from `log t ≤ t − 1` by any
amount of rearrangement.  (Concretely: iterating `log t = 2 log √t ≥ 2(1 − 1/√t)`
converges to `log t`, but every finite iterate has a second-order defect at
`t = 1`, which is precisely the order at which Pinsker is tight.)

What is needed instead is the Padé bound `log t ≥ 2(t−1)/(t+1)`, whose defect at
`t = 1` is of third order.  It is proved here by a mean-value argument — the
derivative of `(t+1) log t − 2(t−1)` is `log t + 1/t − 1 ≥ 0`, which is the
*elementary* bound again — and it is the only place in this file where anything
is differentiated other than the function of `three_div_two_mul_sq_le_mul_log`. -/

/-- `1 − 1/t ≤ log t` for `t > 0`: the elementary logarithm bound in the
direction opposite to `Real.log_le_sub_one_of_pos`, obtained from it at `1/t`. -/
theorem one_sub_inv_le_log {t : ℝ} (ht : 0 < t) : 1 - 1 / t ≤ Real.log t := by
  have h : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith

/-- The derivative of `t ↦ (t + 1) log t − 2(t − 1)` is `log t + 1/t − 1`. -/
private theorem hasDerivAt_padeAux {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => (s + 1) * Real.log s - 2 * (s - 1))
      (Real.log t + 1 / t - 1) t := by
  have h1 : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht
  have h3 : HasDerivAt (fun s : ℝ => (s + 1) * Real.log s)
      (1 * Real.log t + (t + 1) * t⁻¹) t := h1.mul h2
  have h4 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 t := by
    simpa using HasDerivAt.const_mul (2 : ℝ) ((hasDerivAt_id t).sub_const 1)
  have h5 := h3.sub h4
  have he : 1 * Real.log t + (t + 1) * t⁻¹ - 2 = Real.log t + 1 / t - 1 := by
    field_simp
    ring
  rwa [he] at h5

/-- `t ↦ (t + 1) log t − 2(t − 1)` is monotone on `(0, ∞)`.

This is the *only* mean-value argument in the file that is not about the
function of `three_div_two_mul_sq_le_mul_log`, and its derivative hypothesis is
discharged by `one_sub_inv_le_log`, i.e. by the elementary bound the rest of the
area runs on. -/
private theorem monotoneOn_padeAux :
    MonotoneOn (fun s : ℝ => (s + 1) * Real.log s - 2 * (s - 1)) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_padeAux (ne_of_gt hs)).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    exact (hasDerivAt_padeAux (ne_of_gt hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    rw [(hasDerivAt_padeAux (ne_of_gt hs)).deriv]
    have := one_sub_inv_le_log hs
    linarith

/-- **The Padé bound on the logarithm, `t ≥ 1`.**  `2(t − 1) ≤ (t + 1) log t`,
i.e. `log t ≥ 2(t−1)/(t+1)`.

Unlike `log t ≥ 1 − 1/t`, this is tight to *second* order at `t = 1`, which is
what Pinsker's sharp constant needs. -/
theorem two_mul_sub_le_add_one_mul_log {t : ℝ} (ht : 1 ≤ t) :
    2 * (t - 1) ≤ (t + 1) * Real.log t := by
  have h := monotoneOn_padeAux (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos ht)) ht
  simp only [Real.log_one, mul_zero, sub_self, zero_sub, mul_one] at h
  linarith

/-- **The Padé bound on the logarithm, `t ≤ 1`.**  `(t + 1) log t ≤ 2(t − 1)`:
below `1` the inequality of `two_mul_sub_le_add_one_mul_log` reverses, both
sides being negative. -/
theorem add_one_mul_log_le_two_mul_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (t + 1) * Real.log t ≤ 2 * (t - 1) := by
  have h := monotoneOn_padeAux (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr one_pos) ht1
  simp only [Real.log_one, mul_zero, sub_self, zero_sub, mul_one] at h
  linarith

/-! ## The scalar Padé estimate for `t log t − t + 1`

The function `φ(t) = t log t − t + 1` is the pointwise relative entropy in
normalised form: `φ ≥ 0`, `φ(1) = 0`, and `φ(t) = (t−1)²/2 + O((t−1)³)`.  The
estimate below replaces it by a rational function agreeing with it to third
order at `t = 1`.

Its proof is the second and last mean-value argument: the derivative of
`φ(t)(t+2) − (3/2)(t−1)²` is exactly `2·((t+1) log t − 2(t−1))`, the Padé
quantity of the previous section, so its sign is the sign of `t − 1` and the
function has a minimum at `t = 1`, where it vanishes. -/

/-- The derivative of `t ↦ (t log t − t + 1)(t + 2) − (3/2)(t − 1)²` is
`2·((t + 1) log t − 2(t − 1))` — the Padé quantity of the previous section. -/
private theorem hasDerivAt_phiAux {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => (s * Real.log s - s + 1) * (s + 2) - 3 / 2 * (s - 1) ^ 2)
      (2 * ((t + 1) * Real.log t - 2 * (t - 1))) t := by
  have hu : HasDerivAt (fun s : ℝ => s * Real.log s - s + 1) (Real.log t) t := by
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_log ht)
    have h2 := (h1.sub (hasDerivAt_id t)).add_const 1
    have he : 1 * Real.log t + t * t⁻¹ - 1 = Real.log t := by
      field_simp
      ring
    rwa [he] at h2
  have hv : HasDerivAt (fun s : ℝ => s + 2) 1 t := (hasDerivAt_id t).add_const 2
  have hw : HasDerivAt (fun s : ℝ => 3 / 2 * (s - 1) ^ 2) (3 / 2 * (2 * (t - 1))) t := by
    have hd : HasDerivAt (fun s : ℝ => (s - 1) * (s - 1)) (1 * (t - 1) + (t - 1) * 1) t :=
      ((hasDerivAt_id t).sub_const 1).mul ((hasDerivAt_id t).sub_const 1)
    have hd2 : HasDerivAt (fun s : ℝ => (s - 1) ^ 2) (2 * (t - 1)) t := by
      have hfun : (fun s : ℝ => (s - 1) ^ 2) = fun s : ℝ => (s - 1) * (s - 1) := by
        funext s; ring
      have he2 : (1 : ℝ) * (t - 1) + (t - 1) * 1 = 2 * (t - 1) := by ring
      rw [hfun]
      rwa [he2] at hd
    exact HasDerivAt.const_mul (3 / 2 : ℝ) hd2
  have h5 := (hu.mul hv).sub hw
  have he : Real.log t * (t + 2) + (t * Real.log t - t + 1) * 1 - 3 / 2 * (2 * (t - 1))
      = 2 * ((t + 1) * Real.log t - 2 * (t - 1)) := by ring
  rwa [he] at h5

/-- **The scalar Padé estimate.**  For `t ≥ 0`,

  `(3/2)·(t − 1)² ≤ (t log t − t + 1)·(t + 2)`,

the division-free form of `t log t − t + 1 ≥ (3/2)(t−1)²/(t+2)`.

The constants are forced.  Writing `t = 1 + s`, the left side is
`(3/2)s²/(3+s) = s²/2 − s³/6 + s⁴/18 + …` after dividing by `t + 2`, while
`t log t − t + 1 = s²/2 − s³/6 + s⁴/12 − …`; the two agree through order `s³`
and the inequality is decided at order `s⁴`.  Replacing `t + 2` by `t + κ` for
`κ < 2` makes the `s³` terms disagree in the wrong direction and the statement
false near `t = 1`; and the pairing of `κ = 2` with `3/2` is exactly what makes
the summed form give Pinsker's constant `2` rather than something smaller. -/
theorem three_div_two_mul_sq_le_mul_log {t : ℝ} (ht : 0 ≤ t) :
    3 / 2 * (t - 1) ^ 2 ≤ (t * Real.log t - t + 1) * (t + 2) := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [Real.log_zero, mul_zero, zero_sub, neg_zero, zero_add, zero_sub]
    norm_num
  · -- The auxiliary function, whose value at `1` is `0`.
    set F : ℝ → ℝ := fun s => (s * Real.log s - s + 1) * (s + 2) - 3 / 2 * (s - 1) ^ 2 with hF
    have hF1 : F 1 = 0 := by
      simp only [hF, Real.log_one, mul_zero]
      norm_num
    have hkey : 0 ≤ F t := by
      rcases le_or_gt 1 t with h1 | h1
      · -- `F` is monotone on `[1, ∞)`
        have hmono : MonotoneOn F (Set.Ici 1) := by
          refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
          · intro s hs
            have hs0 : s ≠ 0 := by
              have : (1 : ℝ) ≤ s := hs
              linarith
            exact (hasDerivAt_phiAux hs0).continuousAt.continuousWithinAt
          · intro s hs
            rw [interior_Ici] at hs
            have hs0 : s ≠ 0 := by
              have : (1 : ℝ) < s := hs
              linarith
            exact (hasDerivAt_phiAux hs0).differentiableAt.differentiableWithinAt
          · intro s hs
            rw [interior_Ici] at hs
            have hs1 : (1 : ℝ) < s := hs
            have hs0 : s ≠ 0 := by linarith
            rw [(hasDerivAt_phiAux hs0).deriv]
            have := two_mul_sub_le_add_one_mul_log hs1.le
            linarith
        have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h1) h1
        rw [hF1] at this
        exact this
      · -- `F` is antitone on `[t, 1]`
        have hanti : AntitoneOn F (Set.Icc t 1) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc t 1) ?_ ?_ ?_
          · intro s hs
            have hs0 : s ≠ 0 := by
              have : t ≤ s := hs.1
              linarith
            exact (hasDerivAt_phiAux hs0).continuousAt.continuousWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hs0 : s ≠ 0 := by
              have : t < s := hs.1
              linarith
            exact (hasDerivAt_phiAux hs0).differentiableAt.differentiableWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hst : t < s := hs.1
            have hs1 : s < 1 := hs.2
            have hs0 : 0 < s := lt_trans hpos hst
            rw [(hasDerivAt_phiAux hs0.ne').deriv]
            have := add_one_mul_log_le_two_mul_sub hs0 hs1.le
            linarith
        have := hanti (Set.mem_Icc.mpr ⟨le_rfl, h1.le⟩) (Set.mem_Icc.mpr ⟨h1.le, le_rfl⟩) h1.le
        rw [hF1] at this
        exact this
    simp only [hF] at hkey
    linarith

/-! ## The pointwise relative-entropy term

`klTerm a b` is the summand of the relative entropy in its "already centred"
form: the linear correction `−a + b` sums to zero over a pair of probability
distributions, so adding it changes nothing, but it is what makes the pointwise
estimate below true for each `x` separately. -/

/-- The **pointwise relative-entropy term** `a(log a − log b) − a + b`.

The linear part `−a + b` sums to zero against two distributions
(`klDiv_eq_sum_klTerm`), so it is invisible in the divergence; pointwise it is
what makes `klTerm a b ≥ 0` and what makes the Padé estimate below hold term by
term.  The Mathlib convention `Real.log 0 = 0` makes `klTerm 0 b = b`, which is
the correct value, and `klTerm a 0 = a log a − a` — a value that is *not*
`+∞`, which is why every distributional statement below carries an
absolute-continuity hypothesis. -/
noncomputable def klTerm (a b : ℝ) : ℝ := a * (Real.log a - Real.log b) - a + b

/-- Unfolding lemma for `klTerm`. -/
theorem klTerm_apply (a b : ℝ) : klTerm a b = a * (Real.log a - Real.log b) - a + b := rfl

/-- The pointwise term vanishes where both distributions do — the case that
makes `lin_le_klTerm` degenerate, and the reason it needs no positivity. -/
@[simp] theorem klTerm_zero_zero : klTerm 0 0 = 0 := by simp [klTerm]

/-- **The Padé estimate, homogeneous form.**  For `a, b ≥ 0` with `b = 0` only
when `a = 0`,

  `(3/2)·(a − b)² ≤ klTerm a b · (a + 2b)`.

This is `three_div_two_mul_sq_le_mul_log` at `t = a/b`, multiplied by `b²`; both
sides are homogeneous of degree two, which is what makes the scaling legitimate
and what makes the summed statement scale correctly. -/
theorem three_div_two_mul_sq_le_klTerm_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) : 3 / 2 * (a - b) ^ 2 ≤ klTerm a b * (a + 2 * b) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · -- `b = 0` forces `a = 0`
    have hb0' : b = 0 := hb0.symm
    have ha0 : a = 0 := hab hb0'
    rw [ha0, hb0']
    simp
  · have hbne : b ≠ 0 := hbpos.ne'
    rcases ha.eq_or_lt with ha0 | hapos
    · -- `a = 0`: the estimate reads `(3/2)b² ≤ 2b²`
      rw [← ha0]
      simp only [klTerm, Real.log_zero, zero_mul, zero_sub, zero_add, neg_zero, sub_zero,
        zero_sub]
      nlinarith [sq_nonneg b]
    · -- the generic case: scale by `b²`
      have hlog : Real.log (a / b) = Real.log a - Real.log b := Real.log_div hapos.ne' hbne
      have key := three_div_two_mul_sq_le_mul_log (t := a / b) (by positivity)
      have e1 : a - b = b * (a / b - 1) := by field_simp
      have e2 : klTerm a b = b * (a / b * Real.log (a / b) - a / b + 1) := by
        rw [klTerm, hlog]
        field_simp
      have e3 : a + 2 * b = b * (a / b + 2) := by field_simp
      rw [e1, e2, e3]
      have el : 3 / 2 * (b * (a / b - 1)) ^ 2 = b ^ 2 * (3 / 2 * (a / b - 1) ^ 2) := by ring
      have er : b * (a / b * Real.log (a / b) - a / b + 1) * (b * (a / b + 2))
          = b ^ 2 * ((a / b * Real.log (a / b) - a / b + 1) * (a / b + 2)) := by ring
      rw [el, er]
      exact mul_le_mul_of_nonneg_left key (sq_nonneg b)

/-- **The linearised Padé estimate** — the form that sums.  For `a, b ≥ 0` with
`b = 0` only when `a = 0`, and for *every* real `c`,

  `3c·|a − b| − (3/2)c²·(a + 2b) ≤ klTerm a b`.

The left side is a linear function of the pair `(|a − b|, a + 2b)`, so summing
it over `x` needs only that `∑ |ν x − μ x| = 2‖ν − μ‖_TV` and
`∑ (ν x + 2 μ x) = 3`.  This replaces the Cauchy–Schwarz step of the textbook
proof: the optimal slope `c = (2/3)‖ν − μ‖_TV` is written down rather than
obtained from an inequality, and no square root ever appears.

The proof is `three_div_two_mul_sq_le_klTerm_mul` together with
`(|a − b| − c(a + 2b))² ≥ 0`. -/
theorem lin_le_klTerm {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    3 * c * |a - b| - 3 / 2 * c ^ 2 * (a + 2 * b) ≤ klTerm a b := by
  have hw : 0 ≤ a + 2 * b := by linarith
  rcases hw.eq_or_lt with hw0 | hwpos
  · -- degenerate: `a = b = 0`
    have hb0 : b = 0 := by linarith
    have ha0 : a = 0 := by linarith
    rw [ha0, hb0]
    simp
  · have hkey := three_div_two_mul_sq_le_klTerm_mul ha hb hab
    have habs : |a - b| ^ 2 = (a - b) ^ 2 := sq_abs _
    have hsq : 0 ≤ 3 / 2 * (|a - b| - c * (a + 2 * b)) ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hwpos
    nlinarith [hkey, habs, hsq]

/-! ## Pinsker's inequality

The divergence is the sum of the pointwise terms, and the linearised estimate is
summed at the slope `c = (2/3)‖ν − μ‖_TV`.  The two `∑`s that appear are the
definition of `tvDist` and the fact that `ν` and `μ` are probability
distributions; nothing else enters. -/

variable {Ω : Type*} [Fintype Ω]

/-- The relative entropy is the sum of the pointwise terms:

  `D(ν ‖ μ) = ∑ x, (ν x (log ν x − log μ x) − ν x + μ x)`.

The linear correction contributes `−1 + 1 = 0`, so this is the usual formula;
what it buys is a summand to which `lin_le_klTerm` applies term by term. -/
theorem klDiv_eq_sum_klTerm {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    klDiv ν μ = ∑ x, klTerm (ν x) (μ x) := by
  have hzero : ∑ x : Ω, (μ x - ν x) = 0 := by
    rw [Finset.sum_sub_distrib, μ.sum_coe, ν.sum_coe, sub_self]
  have hsplit : ∑ x, klTerm (ν x) (μ x)
      = (∑ x, ν x * (Real.log (ν x) - Real.log (μ x))) + ∑ x : Ω, (μ x - ν x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [klTerm]; ring
  rw [hsplit, hzero, add_zero, klDiv_apply, Ent_apply, Ex_relDensity hac, Real.log_one,
    mul_zero, sub_zero, Ex_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hac x hx]
    simp [relDensity, hx]
  · rcases (ν.coe_nonneg x).eq_or_lt with hν | hν
    · have hν0 : ν x = 0 := hν.symm
      have hrd : relDensity ν μ x = 0 := by simp [relDensity, hx, hν0]
      rw [hrd, hν0]
      simp
    · have hd : relDensity ν μ x = ν x / μ x := by simp [relDensity, hx]
      rw [hd, Real.log_div hν.ne' hx]
      field_simp

/-- **Pinsker's inequality**, with the sharp constant:

  `2 ‖ν − μ‖²_TV ≤ D(ν ‖ μ)`.

`hac` is essential and not a technicality — see the module docstring.

The proof sums `lin_le_klTerm` at the slope `c = (2/3)‖ν − μ‖_TV`.  Writing
`τ = ‖ν − μ‖_TV`, the summed left-hand side is
`3c·(2τ) − (3/2)c²·3 = 6cτ − (9/2)c²`, whose maximum over `c` is at
`c = (2/3)τ` with value `4τ² − 2τ² = 2τ²`.  Both the `2` and the fact that the
optimum is interior come from the constants of
`three_div_two_mul_sq_le_mul_log`. -/
theorem two_mul_tvDist_sq_le_klDiv {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    2 * tvDist ν μ ^ 2 ≤ klDiv ν μ := by
  set c : ℝ := 2 / 3 * tvDist ν μ with hc
  have hsum : ∑ x, (3 * c * |ν x - μ x| - 3 / 2 * c ^ 2 * (ν x + 2 * μ x))
      ≤ ∑ x, klTerm (ν x) (μ x) :=
    Finset.sum_le_sum fun x _ =>
      lin_le_klTerm (ν.coe_nonneg x) (μ.coe_nonneg x) fun h => hac x h
  have habs : ∑ x, |ν x - μ x| = 2 * tvDist ν μ := by
    rw [tvDist_apply]; ring
  have hmass : ∑ x : Ω, (ν x + 2 * μ x) = 3 := by
    rw [Finset.sum_add_distrib, ν.sum_coe, ← Finset.mul_sum, μ.sum_coe]
    norm_num
  have hL : ∑ x, (3 * c * |ν x - μ x| - 3 / 2 * c ^ 2 * (ν x + 2 * μ x))
      = 3 * c * (2 * tvDist ν μ) - 3 / 2 * c ^ 2 * 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, habs, hmass]
  rw [hL, ← klDiv_eq_sum_klTerm hac] at hsum
  have hval : 3 * c * (2 * tvDist ν μ) - 3 / 2 * c ^ 2 * 3 = 2 * tvDist ν μ ^ 2 := by
    rw [hc]; ring
  rw [hval] at hsum
  exact hsum

/-- **Pinsker's inequality in root form**: `‖ν − μ‖_TV ≤ √(D(ν ‖ μ)/2)`.

This is the shape a mixing-time argument consumes: an `ε`-bound on the relative
entropy is a `√(ε/2)`-bound on the total variation distance. -/
theorem tvDist_le_sqrt_klDiv {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    tvDist ν μ ≤ Real.sqrt (klDiv ν μ / 2) := by
  have h := two_mul_tvDist_sq_le_klDiv hac
  have hsq : tvDist ν μ ^ 2 ≤ klDiv ν μ / 2 := by linarith
  calc tvDist ν μ = Real.sqrt (tvDist ν μ ^ 2) := (Real.sqrt_sq (tvDist_nonneg ν μ)).symm
    _ ≤ Real.sqrt (klDiv ν μ / 2) := Real.sqrt_le_sqrt hsq

/-! ## The two-point case

The scalar inequality Pinsker is usually stated as.  It is *not* used above —
the reduction there is pointwise, not through a two-point marginalisation — but
it is the reusable core of the subject, and deriving it from the same
linearisation is a check that the pointwise route and the classical one agree.

The linear parts of the two `klTerm`s cancel, so the right-hand side below is
literally `p log(p/q) + (1−p) log((1−p)/(1−q))`. -/

/-- **Pinsker's inequality, two-point case.**  For `p, q ∈ [0, 1]` with
`q ∈ {0, 1}` only when `p` agrees,

  `2(p − q)² ≤ p log(p/q) + (1−p) log((1−p)/(1−q))`.

The right-hand side is written as `klTerm p q + klTerm (1−p) (1−q)`; the two
linear corrections `−p + q` and `−(1−p) + (1−q)` cancel exactly, so this is the
usual two-point relative entropy.

The side conditions are the absolute-continuity hypothesis for the two-point
distributions `(p, 1−p)` and `(q, 1−q)`, and they cannot be dropped: at `q = 0`,
`p = 1` the left side is `2` and the right side, with `Real.log 0 = 0`,
evaluates to `0`.

The proof applies `lin_le_klTerm` to each of the two cells at the common slope
`c = (2/3)|p − q|` and adds; the masses `p + 2q` and `(1−p) + 2(1−q)` sum to
`3`, exactly as the distributional masses do. -/
theorem two_mul_sub_sq_le_klTerm_add_klTerm {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : q = 0 → p = 0) (h1 : q = 1 → p = 1) :
    2 * (p - q) ^ 2 ≤ klTerm p q + klTerm (1 - p) (1 - q) := by
  set c : ℝ := 2 / 3 * |p - q| with hc
  have hA := lin_le_klTerm (a := p) (b := q) (c := c) hp0 hq0 h0
  have hB := lin_le_klTerm (a := 1 - p) (b := 1 - q) (c := c) (by linarith) (by linarith)
    (fun h => by rw [h1 (by linarith)]; ring)
  have hsym : |(1 - p) - (1 - q)| = |p - q| := by
    rw [show (1 - p) - (1 - q) = -(p - q) by ring, abs_neg]
  have habs2 : |p - q| ^ 2 = (p - q) ^ 2 := sq_abs _
  rw [hsym] at hB
  have hmass : (p + 2 * q) + ((1 - p) + 2 * (1 - q)) = 3 := by ring
  have hkey : 3 * c * |p - q| - 3 / 2 * c ^ 2 * (p + 2 * q)
      + (3 * c * |p - q| - 3 / 2 * c ^ 2 * ((1 - p) + 2 * (1 - q)))
      = 2 * (p - q) ^ 2 := by
    rw [hc, ← habs2]; ring
  linarith

/-! ## Cashing it: relative entropy bounds become mixing-time bounds

This is what the module exists for.  `Techniques/EntropyDecay.lean` proves
`EntropyContraction.klDiv_iter_row_le_of_log_le`:

  `D(P^t(x, ·) ‖ μ) ≤ ε`  once  `t ≥ ρ⁻¹ ln(ln(1/μ_min)/ε)`,

and remarks that converting it to total variation needs Pinsker.  Feeding that
theorem to `mixesWithin_of_klDiv_le` below does exactly that, and gives

  `MixesWithin P μ (√(ε/2)) t`,

i.e. a genuine mixing time of `ρ⁻¹ ln(ln(1/μ_min)/ε)` steps for total variation
distance `√(ε/2)` — equivalently, `T_mix(δ) ≤ ρ⁻¹ ln(ln(1/μ_min)/(2δ²))`, which
is the form `mixesWithin_of_klDiv_le_two_mul_sq` states.  Nothing in this
section is specific to entropy contraction: any source of a divergence bound
will do. -/

section Mixing

variable [DecidableEq Ω]

/-- **A relative-entropy bound is a mixing statement.**  If the law of the chain
after `t` steps is within relative entropy `ε` of a fully supported `μ` from
every start, then the chain is `√(ε/2)`-mixed after `t` steps.

`hpos` serves only to discharge absolute continuity, which is unavoidable
(module docstring). -/
theorem mixesWithin_of_klDiv_le {μ : FinDist Ω} {P : FinChain Ω} {ε : ℝ} {t : ℕ}
    (hpos : ∀ x, 0 < μ x) (h : ∀ x, klDiv ((P.iter t).row x) μ ≤ ε) :
    MixesWithin P μ (Real.sqrt (ε / 2)) t := by
  intro x
  have hac : ∀ y, μ y = 0 → ((P.iter t).row x) y = 0 := fun y hy => absurd hy (hpos y).ne'
  refine (tvDist_le_sqrt_klDiv hac).trans ?_
  exact Real.sqrt_le_sqrt (by linarith [h x])

/-- **A relative-entropy bound is a mixing statement, in `ε`-form.**  If the law
of the chain after `t` steps is within relative entropy `2ε²` of a fully
supported `μ` from every start, then the chain is `ε`-mixed after `t` steps.

This is `mixesWithin_of_klDiv_le` with the square root taken by hand; it is the
form to use when the target is a prescribed total variation accuracy `ε`, since
it says exactly how much divergence one must drive out. -/
theorem mixesWithin_of_klDiv_le_two_mul_sq {μ : FinDist Ω} {P : FinChain Ω} {ε : ℝ}
    {t : ℕ} (hpos : ∀ x, 0 < μ x) (hε : 0 ≤ ε)
    (h : ∀ x, klDiv ((P.iter t).row x) μ ≤ 2 * ε ^ 2) : MixesWithin P μ ε t := by
  intro x
  have hac : ∀ y, μ y = 0 → ((P.iter t).row x) y = 0 := fun y hy => absurd hy (hpos y).ne'
  have hsq : tvDist ((P.iter t).row x) μ ^ 2 ≤ ε ^ 2 := by
    have := two_mul_tvDist_sq_le_klDiv hac
    have hx := h x
    linarith
  nlinarith [tvDist_nonneg ((P.iter t).row x) μ, hsq]

end Mixing

end Arlib.MarkovChains

