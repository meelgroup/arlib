/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Concentration
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Failure-budget bookkeeping: union bounds, margin products, staged inductions

A randomized algorithm assembled out of several randomized parts fails when *any*
part fails, and the arithmetic of that composition is the part of a paper's
analysis that is most often waved at.  This module is the bookkeeping layer: it
proves, once, the four facts that such an analysis consumes, in the `outProbR`
vocabulary of `Arlib.Approximation.Counting`.

## What is here

1. **The union bound over a `Finset`** (`outProb_biUnion_le`, `outProbR_biUnion_le`)
   and its conjunctive shadow (`one_sub_sum_le_outProbR_biInter`):
   `Pr[⋂_{i ∈ s} E i] ≥ 1 - ∑_{i ∈ s} δ i` whenever `Pr[¬E i] ≤ δ i`.  The
   disjunctive form `Pr[⋃_{i ∈ s} ¬E i] ≤ ∑ δ i` is stated too
   (`outProbR_biUnion_compl_le`), because it is usually the more usable one: it
   chains with further union bounds without any complementation.
2. **The product of margins** (`one_sub_add_le_one_sub_mul_one_sub`,
   `one_sub_sum_le_prod_one_sub`): `(1-a)(1-b) ≥ 1-a-b`, and
   `∏ (1 - a i) ≥ 1 - ∑ a i` for `a i ∈ [0,1]`.  This is the elementary
   inequality behind every "and the induction closes" step.
3. **The geometric staged invariant** (`one_sub_geom_le_of_geom_step`,
   `one_sub_rpow_le_of_geom_step`): the exact shape of the induction in
   `theo:fpras-bta`.
4. **Budget composition** (`sum_div_card`, `one_sub_le_outProbR_biInter_of_le_div`):
   `k` sources of failure at budget `δ/k` each buy an overall `1 - δ`; `k`
   sources at budget `δ` each buy only `1 - kδ`.

## What Mathlib already had, and is reused rather than reproved

* `MeasureTheory.measure_biUnion_finset_le` — finite subadditivity for anything
  in `OuterMeasureClass`, which `PMF.toOuterMeasure` is.  `outProb_biUnion_le` is
  a two-line transport of it through `Prod.fst`, not a new proof.
* `one_add_mul_le_pow` — Bernoulli, `1 + n·a ≤ (1+a)^n` for `-2 ≤ a`.  This is
  the *constant-budget* case `(1-a)^k ≥ 1 - k·a` of item 2 above and is quoted
  as such in `one_sub_nsmul_le_one_sub_pow`.
* `Finset.prod_one_sub_ordered` is the nearest thing Mathlib has to
  `one_sub_sum_le_prod_one_sub`, but it is an *identity* with a leftover
  `∑ i, a i * ∏_{j<i} (1 - a j)`, not the inequality; the variable-budget
  inequality is not in Mathlib and is proved here.
* `ENNReal.toReal_sum`, `ENNReal.sum_ne_top` — the `ℝ≥0∞ → ℝ` transport.

## The ACJR instance

Throughout, [ACJR21] is Marcelo Arenas, Luis Alberto Croquevielle, Rajesh
Jayaram, Cristian Riveros, *#NFA Admits an FPRAS: Efficient Enumeration,
Counting, and Uniform Generation for Logspace Classes*, J. ACM 68(6), art. 48
(2021), arXiv:1906.09226, together with its conjunctive-query companion *When Is
Approximate Counting for Conjunctive Queries Tractable?*, STOC 2021,
arXiv:2005.10029.  The statements quoted below are cited by the labels they
carry in the authors' manuscript (`theo:fpras-bta`, `lem:estimatepart`,
`prop:prop1`, …); that manuscript is a private multi-file source not distributed
with this library, so no line numbers are given and the labels are the locator.

`theo:fpras-bta` carries the invariant
`Pr[⋀_{j ≤ i}(ℰ¹_j ∧ ℰ²_j)] ≥ 1 - 2^{-γ+2i}`, closed by
`(1 - 2^{-γ+1})·(1 - 2^{-γ+2(i-1)}) ≥ 1 - 2^{-γ+2i}`.  Two observations, both
formalized below.

* **The closing inequality is true**, for every real `γ` and every `i ≥ 1`, with
  one hypothesis the paper does not state: `γ ≥ 1`.  It is needed because the
  step multiplies the induction hypothesis by `1 - 2^{-γ+1}`, and multiplying an
  inequality by a *negative* number reverses it.  Everything else is
  unconditional.  Written in terms of `x = 2^{-γ}` — as
  `one_sub_geom_le_of_geom_step` is — the hypothesis reads `2x ≤ 1` and the
  invariant reads `1 - 4^{i} x`, with no `rpow` anywhere.
* **The bound is vacuous unless `γ > 2i`.**  With `γ = log₂(1/δ) + 2n` and
  `i ≤ n` that is `log₂(1/δ) > 0`, i.e. `δ < 1` — always available.  At the top
  level `i = n` the invariant evaluates to exactly `1 - δ`
  (`two_rpow_neg_failureExponent_add`).

`failureExponent` and the lemmas around it also settle the conflation in the
paper's `FAIL` bound: with `γ = log₂(1/δ) + 2n` one has `2^{-γ} = δ/4^n`, which is
*strictly smaller* than `δ` for `n ≥ 1` (`two_rpow_neg_failureExponent_lt`), so reading
the `FAIL` bound `2^{-γ}` as `δ` is a conservative misstatement, not an unsound
one.  What is unsound is the total: three budgets each spent in full sum to
`2δ + δ/4^n`, which is `< 3δ` but emphatically not `δ`
(`three_budgets_sum`, `three_budgets_sum_lt`).  Running each source at `δ/3`
is what recovers the advertised `1 - δ` (`sum_div_card`).
-/

namespace Arlib.Approximation

open scoped ENNReal

/-! ## The product of margins -/

/-- **The two-factor product of margins.**  `(1-a)(1-b) ≥ 1 - a - b`: losing `a`
and then losing `b` costs at most `a + b`.

This is the inequality every "and so the induction closes" step is really using,
including the closing step of [ACJR21, `theo:fpras-bta`]. -/
theorem one_sub_add_le_one_sub_mul_one_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - (a + b) ≤ (1 - a) * (1 - b) := by
  nlinarith [mul_nonneg ha hb]

/-- **The product of margins over a `Finset`.**  `∏ (1 - a i) ≥ 1 - ∑ a i` for
budgets `a i ∈ [0,1]`.

Both hypotheses are needed.  Without `0 ≤ a i` the sum can be made small while a
factor is huge; without `a i ≤ 1` the statement is false — three budgets equal to
`4` give `1 - ∑ = -11` on the left and `(-3)^3 = -27` on the right.

Mathlib has `Finset.prod_one_sub_ordered`, an exact expansion of the same
product, but not this inequality. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (a : ι → ℝ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert j t hjt ih =>
    intro h0 h1
    have haj0 : 0 ≤ a j := h0 j (Finset.mem_insert_self j t)
    have haj1 : a j ≤ 1 := h1 j (Finset.mem_insert_self j t)
    have ht0 : ∀ i ∈ t, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hind := ih ht0 fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hsum0 : 0 ≤ ∑ i ∈ t, a i := Finset.sum_nonneg ht0
    rw [Finset.sum_insert hjt, Finset.prod_insert hjt]
    nlinarith [mul_nonneg (sub_nonneg.2 haj1) (sub_nonneg.2 hind), mul_nonneg haj0 hsum0]

/-- **The constant-budget case**: `k` sources each at budget `a` leave a margin
of at least `1 - k·a`.

This is Mathlib's Bernoulli inequality `one_add_mul_le_pow` at `-a`, recorded
here only so that callers writing failure budgets do not have to spot the
substitution.  The hypothesis `a ≤ 2` is Bernoulli's `-2 ≤ -a`, and is far
weaker than the `a ≤ 1` that `one_sub_sum_le_prod_one_sub` needs. -/
theorem one_sub_nsmul_le_one_sub_pow {a : ℝ} (ha : a ≤ 2) (k : ℕ) :
    1 - k * a ≤ (1 - a) ^ k := by
  have h := one_add_mul_le_pow (a := -a) (by linarith) k
  simpa [sub_eq_add_neg, mul_comm] using h

/-! ## The union bound for `outProb` -/

section UnionBound

variable {β ι : Type*}

/-- **The union bound**, in `ℝ≥0∞`.  The probability that the output lands in
some `F i`, `i` ranging over a `Finset`, is at most the sum of the individual
probabilities.

This is `MeasureTheory.measure_biUnion_finset_le` for the outer measure of the
`PMF`, transported through the projection `Prod.fst` that `outProb` marginalises
over; no new probabilistic content. -/
theorem outProb_biUnion_le (μ : PMF (β × ℕ)) (s : Finset ι) (F : ι → Set β) :
    outProb μ (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, outProb μ (F i) := by
  have hset : {p : β × ℕ | p.1 ∈ ⋃ i ∈ s, F i} = ⋃ i ∈ s, {p : β × ℕ | p.1 ∈ F i} := by
    ext p; simp
  simp only [outProb, hset]
  exact MeasureTheory.measure_biUnion_finset_le (μ := μ.toOuterMeasure) s _

/-- **The union bound**, as reals.  This is the form a failure analysis is
stated in: `Pr[⋁_{i ∈ s} bad_i] ≤ ∑_{i ∈ s} δ i`. -/
theorem outProbR_biUnion_le (μ : PMF (β × ℕ)) (s : Finset ι) (F : ι → Set β) :
    outProbR μ (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, outProbR μ (F i) := by
  have hne : (∑ i ∈ s, outProb μ (F i)) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => outProb_ne_top μ (F i)
  have h := ENNReal.toReal_mono hne (outProb_biUnion_le μ s F)
  rwa [ENNReal.toReal_sum fun i _ => outProb_ne_top μ (F i)] at h

/-- **The union bound with explicit budgets.**  If each `F i` has probability at
most `δ i`, their union has probability at most `∑ δ i`. -/
theorem outProbR_biUnion_le_sum (μ : PMF (β × ℕ)) (s : Finset ι) (F : ι → Set β)
    (δ : ι → ℝ) (h : ∀ i ∈ s, outProbR μ (F i) ≤ δ i) :
    outProbR μ (⋃ i ∈ s, F i) ≤ ∑ i ∈ s, δ i :=
  (outProbR_biUnion_le μ s F).trans (Finset.sum_le_sum h)

/-- **The disjunctive form of the staged bound.**  If each stage `i` fails with
probability at most `δ i`, the probability that *some* stage fails is at most
`∑ δ i`.

This and `one_sub_sum_le_outProbR_biInter` are the same fact; this one is
usually the easier to chain, because it composes with further union bounds
without any complementation. -/
theorem outProbR_biUnion_compl_le (μ : PMF (β × ℕ)) (s : Finset ι) (E : ι → Set β)
    (δ : ι → ℝ) (h : ∀ i ∈ s, outProbR μ (E i)ᶜ ≤ δ i) :
    outProbR μ (⋃ i ∈ s, (E i)ᶜ) ≤ ∑ i ∈ s, δ i :=
  outProbR_biUnion_le_sum μ s (fun i => (E i)ᶜ) δ h

/-- **The staged conjunction bound**, from complement budgets.  If each stage `i`
fails with probability at most `δ i`, all stages succeed with probability at
least `1 - ∑ δ i`.

Stated with the failure events `(E i)ᶜ` because that is how a per-stage lemma is
usually phrased ("except with probability `δ`"); see
`one_sub_sum_le_outProbR_biInter'` for the version taking the success form. -/
theorem one_sub_sum_le_outProbR_biInter (μ : PMF (β × ℕ)) (s : Finset ι) (E : ι → Set β)
    (δ : ι → ℝ) (h : ∀ i ∈ s, outProbR μ (E i)ᶜ ≤ δ i) :
    1 - ∑ i ∈ s, δ i ≤ outProbR μ (⋂ i ∈ s, E i) := by
  have hcompl : (⋂ i ∈ s, E i)ᶜ = ⋃ i ∈ s, (E i)ᶜ := by
    simp only [Set.compl_iInter]
  have h1 : outProbR μ (⋂ i ∈ s, E i)ᶜ ≤ ∑ i ∈ s, δ i := by
    rw [hcompl]
    exact outProbR_biUnion_le_sum μ s (fun i => (E i)ᶜ) δ h
  rw [outProbR_compl] at h1
  linarith

/-- **The staged conjunction bound**, from success guarantees.  If each stage
succeeds with probability at least `1 - δ i`, all stages succeed with
probability at least `1 - ∑ δ i`. -/
theorem one_sub_sum_le_outProbR_biInter' (μ : PMF (β × ℕ)) (s : Finset ι) (E : ι → Set β)
    (δ : ι → ℝ) (h : ∀ i ∈ s, 1 - δ i ≤ outProbR μ (E i)) :
    1 - ∑ i ∈ s, δ i ≤ outProbR μ (⋂ i ∈ s, E i) := by
  refine one_sub_sum_le_outProbR_biInter μ s E δ fun i hi => ?_
  rw [outProbR_compl]
  linarith [h i hi]

/-- The staged conjunction bound over the first `k` stages, the form the
[ACJR21, `theo:fpras-bta`] induction is indexed by. -/
theorem one_sub_sum_le_outProbR_iInter_range (μ : PMF (β × ℕ)) (k : ℕ) (E : ℕ → Set β)
    (δ : ℕ → ℝ) (h : ∀ j < k, outProbR μ (E j)ᶜ ≤ δ j) :
    1 - ∑ j ∈ Finset.range k, δ j ≤ outProbR μ (⋂ j ∈ Finset.range k, E j) :=
  one_sub_sum_le_outProbR_biInter μ (Finset.range k) E δ fun j hj =>
    h j (Finset.mem_range.1 hj)

end UnionBound

/-! ## Budget composition -/

section Budget

variable {β ι : Type*}

/-- **Splitting a budget evenly.**  Spreading `δ` over the `|s|` sources of
failure gives each `δ / |s|`, and they add back up to exactly `δ`.

This is the whole content of "to advertise `1 - δ` overall, run each of the `k`
parts at `δ / k`". -/
theorem sum_div_card (s : Finset ι) (hs : s.Nonempty) (δ : ℝ) :
    ∑ _i ∈ s, δ / (s.card : ℝ) = δ := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 hs).ne'
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **Spending the same budget `δ` at every source costs `|s| · δ`, not `δ`.**
The mirror of `sum_div_card`, and the arithmetic that an analysis which "never
adds the budgets up" is implicitly getting wrong. -/
theorem sum_const_budget (s : Finset ι) (δ : ℝ) :
    ∑ _i ∈ s, δ = (s.card : ℝ) * δ := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **Budget composition, the usable form.**  `|s|` sources of failure, each run
at budget `δ / |s|`, give an overall success probability of at least `1 - δ`. -/
theorem one_sub_le_outProbR_biInter_of_le_div (μ : PMF (β × ℕ)) (s : Finset ι) (hs : s.Nonempty)
    (E : ι → Set β) (δ : ℝ) (h : ∀ i ∈ s, outProbR μ (E i)ᶜ ≤ δ / (s.card : ℝ)) :
    1 - δ ≤ outProbR μ (⋂ i ∈ s, E i) := by
  have := one_sub_sum_le_outProbR_biInter μ s E (fun _ => δ / (s.card : ℝ)) h
  rwa [sum_div_card s hs δ] at this

/-- **Budget composition, the failure form.**  `|s|` sources of failure each run
at the *full* budget `δ` give only `1 - |s| · δ`.  Compare
`one_sub_le_outProbR_biInter_of_le_div`. -/
theorem one_sub_card_mul_le_outProbR_biInter (μ : PMF (β × ℕ)) (s : Finset ι) (E : ι → Set β)
    (δ : ℝ) (h : ∀ i ∈ s, outProbR μ (E i)ᶜ ≤ δ) :
    1 - (s.card : ℝ) * δ ≤ outProbR μ (⋂ i ∈ s, E i) := by
  have := one_sub_sum_le_outProbR_biInter μ s E (fun _ => δ) h
  rwa [sum_const_budget s δ] at this

end Budget

/-! ## The geometric staged invariant

The shape of the induction in [ACJR21, `theo:fpras-bta`], stated in terms of
`x = 2^{-γ}` so that no `rpow` appears: the invariant `1 - 2^{-γ+2i}` becomes
`1 - 4^i · x` and the per-stage margin `1 - 2^{-γ+1}` becomes `1 - 2x`. -/

/-- **The closing step of the paper's induction, as pure arithmetic.**

`(1 - 2x)·(1 - 4^{k+1} x) ≥ 1 - 4^{k+2} x` for `0 ≤ x`.  The slack is
`x·(3·4^{k+1} - 2 + 2·4^{k+1} x)`, which is positive because `4^{k+1} ≥ 4`; this
is where the induction's `i ≥ 1` is used, and it is the *only* place it is used.

Note that no upper bound on `x` — hence no hypothesis on `γ` — is needed here.
The hypothesis `2x ≤ 1` enters one level up, in
`one_sub_geom_le_of_geom_step`, and for a different reason. -/
theorem one_sub_geom_step {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    1 - 4 ^ (k + 2) * x ≤ (1 - 2 * x) * (1 - 4 ^ (k + 1) * x) := by
  have h4 : (4 : ℝ) ≤ 4 ^ (k + 1) := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ (k + 1) := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 1 k)
  have hpow : (4 : ℝ) ^ (k + 2) = 4 * 4 ^ (k + 1) := by ring
  rw [hpow]
  nlinarith [mul_nonneg (sub_nonneg.2 h4) hx,
    mul_nonneg (le_trans (by norm_num) h4) (mul_nonneg hx hx)]

/-- **The staged geometric invariant.**

If a sequence of success probabilities starts at `q 0 ≥ 1 - 4x` and each step
retains at least a `(1 - 2x)` fraction of the previous one, then
`q k ≥ 1 - 4^{k+1} · x` for every `k`.

The hypothesis `2 * x ≤ 1` is the one the paper leaves implicit: the step
multiplies the induction hypothesis by `1 - 2x`, and that is only monotone when
`1 - 2x ≥ 0`.  In the paper's variables `x = 2^{-γ}`, so it says `γ ≥ 1`.

Indices are shifted by one relative to [ACJR21, `theo:fpras-bta`], whose `i` runs over
`[n]`: `q k` is the paper's `p_{k+1}` and the invariant `1 - 4^{k+1} x` is the
paper's `1 - 2^{-γ + 2i}` at `i = k + 1`. -/
theorem one_sub_geom_le_of_geom_step {x : ℝ} (hx : 0 ≤ x) (hx2 : 2 * x ≤ 1) (q : ℕ → ℝ)
    (hbase : 1 - 4 * x ≤ q 0) (hstep : ∀ k, (1 - 2 * x) * q k ≤ q (k + 1)) (k : ℕ) :
    1 - 4 ^ (k + 1) * x ≤ q k := by
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    refine le_trans ?_ (hstep k)
    refine le_trans (one_sub_geom_step hx k) ?_
    exact mul_le_mul_of_nonneg_left ih (by linarith)

/-- **The staged geometric invariant, in the paper's `2^{-γ}` notation.**

`q k ≥ 1 - 2^{-γ + 2(k+1)}`, given `q 0 ≥ 1 - 2^{-γ+2}` and
`q (k+1) ≥ (1 - 2^{-γ+1}) · q k`.  This is `theo:fpras-bta`'s invariant
verbatim, at `i = k + 1`.

`1 ≤ γ` is exactly what makes `1 - 2^{-γ+1}` nonnegative; see
`one_sub_geom_le_of_geom_step`. -/
theorem one_sub_rpow_le_of_geom_step {γ : ℝ} (hγ : 1 ≤ γ) (q : ℕ → ℝ)
    (hbase : 1 - (2 : ℝ) ^ (-γ + 2) ≤ q 0)
    (hstep : ∀ k, (1 - (2 : ℝ) ^ (-γ + 1)) * q k ≤ q (k + 1)) (k : ℕ) :
    1 - (2 : ℝ) ^ (-γ + 2 * ((k : ℝ) + 1)) ≤ q k := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set x : ℝ := (2 : ℝ) ^ (-γ) with hxdef
  have hx : 0 ≤ x := (Real.rpow_pos_of_pos h2 _).le
  -- `2^{-γ+c} = 2^c · x` for the three exponents that occur
  have hshift : ∀ c : ℝ, (2 : ℝ) ^ (-γ + c) = (2 : ℝ) ^ c * x := by
    intro c
    rw [hxdef, Real.rpow_add h2, mul_comm]
  have h1 : (2 : ℝ) ^ (-γ + 1) = 2 * x := by
    rw [hshift 1, Real.rpow_one]
  have h2' : (2 : ℝ) ^ (-γ + 2) = 4 * x := by
    rw [hshift 2, show ((2 : ℝ) : ℝ) ^ (2 : ℝ) = 4 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
  have hk : (2 : ℝ) ^ (-γ + 2 * ((k : ℝ) + 1)) = 4 ^ (k + 1) * x := by
    rw [hshift, show (2 : ℝ) * ((k : ℝ) + 1) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    norm_num
  have hx2 : 2 * x ≤ 1 := by
    rw [← h1]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rw [hk]
  refine one_sub_geom_le_of_geom_step hx hx2 q ?_ ?_ k
  · rwa [h2'] at hbase
  · intro j; rw [← h1]; exact hstep j

/-! ## The failure exponent `γ = log₂(1/δ) + 2n`

The source redefines `γ` this way at the very end of the proof of
`theo:fpras-bta`, and then reads `2^{-γ}` as `δ`.  That reading is not
unconditionally valid, which is the point of this section: the three lemmas
below say precisely what `2^{-γ}` is, where the reading is safe and where it is
not. -/

/-- The paper's rescaled parameter, `γ = log₂(1/δ) + 2n` ([ACJR21,
`theo:fpras-bta`]). -/
noncomputable def failureExponent (δ : ℝ) (n : ℕ) : ℝ := Real.logb 2 (1 / δ) + 2 * n

/-- **`2^{-γ} = δ / 4^n`, not `δ`.**  This is the identity the paper's `FAIL`
bound elides. -/
theorem two_rpow_neg_failureExponent {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (2 : ℝ) ^ (-failureExponent δ n) = δ / 4 ^ n := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog : (2 : ℝ) ^ Real.logb 2 (1 / δ) = 1 / δ :=
    Real.rpow_logb h2 (by norm_num) (by positivity)
  have hpow : (2 : ℝ) ^ (2 * (n : ℝ)) = 4 ^ n := by
    rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      pow_mul]
    norm_num
  rw [failureExponent, neg_add, Real.rpow_add h2, Real.rpow_neg h2.le, Real.rpow_neg h2.le, hlog,
    hpow]
  field_simp

/-- **The `FAIL` budget is conservative, not unsound.**  For `n ≥ 1`,
`2^{-γ} < δ`, so the paper's reading of the `FAIL` bound `2^{-γ}` as `δ`
weakens a true statement rather than asserting a false one. -/
theorem two_rpow_neg_failureExponent_lt {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (-failureExponent δ n) < δ := by
  rw [two_rpow_neg_failureExponent hδ n]
  have h4 : (4 : ℝ) ≤ 4 ^ n := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **At the top level the invariant is exactly `1 - δ`.**  With
`γ = log₂(1/δ) + 2n`, the invariant `1 - 2^{-γ+2i}` at `i = n` reads `1 - δ`: the
induction of `theo:fpras-bta` spends its whole budget, and none of the other
sources of failure has any room left inside it. -/
theorem two_rpow_neg_failureExponent_add {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (2 : ℝ) ^ (-failureExponent δ n + 2 * (n : ℝ)) = δ := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog : (2 : ℝ) ^ Real.logb 2 (1 / δ) = 1 / δ :=
    Real.rpow_logb h2 (by norm_num) (by positivity)
  have : -failureExponent δ n + 2 * (n : ℝ) = -Real.logb 2 (1 / δ) := by
    rw [failureExponent]; ring
  rw [this, Real.rpow_neg h2.le, hlog]
  field_simp

/-- **`1 ≤ γ`**, the hypothesis `one_sub_rpow_le_of_geom_step` needs, holds for
the paper's `γ` whenever `δ ≤ 1` and `n ≥ 1` — in particular for the paper's own
standing `δ ∈ (0,1/2)`.  So the missing hypothesis is free, but it is missing. -/
theorem one_le_failureExponent {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) :
    1 ≤ failureExponent δ n := by
  have hlog : 0 ≤ Real.logb 2 (1 / δ) := by
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_div_iff₀ hδ0]; linarith
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [failureExponent]; linarith

/-! ## The failure accounting of `theo:fpras-bta`

The development notes record three budgets, each spent in full: the induction
invariant of [ACJR21, `theo:fpras-bta`], which is exactly `δ`; its `FAIL` bound,
which is `2^{-γ}`; and [ACJR21, `lem:estimatepart`]'s, which is again `δ`.  These
are added here — the paper never adds them — and the sum is what the algorithm
actually delivers. -/

/-- **The exact total.**  The three budgets of `theo:fpras-bta` sum to
`2δ + δ/4^n`. -/
theorem three_budgets_sum {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    δ + (2 : ℝ) ^ (-failureExponent δ n) + δ = 2 * δ + δ / 4 ^ n := by
  rw [two_rpow_neg_failureExponent hδ n]; ring

/-- **`1 - 3δ`, and in fact slightly better.**  The development notes' "at best
`1 - 3δ`" is right as an upper bound on the loss, and is not tight: the true
total is `2δ + δ/4^n`, strictly below `3δ` for `n ≥ 1`.  What it is emphatically
not is `δ`. -/
theorem three_budgets_sum_lt {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    δ + (2 : ℝ) ^ (-failureExponent δ n) + δ < 3 * δ := by
  have := two_rpow_neg_failureExponent_lt hδ hn
  linarith

/-- **The repair.**  Three sources of failure, each run at `δ/3`, total `δ`.
This is `sum_div_card` at `s = Finset.range 3`, and is what `theo:fpras-bta`
would have to do to advertise `1 - δ` honestly. -/
theorem three_budgets_div_three (δ : ℝ) :
    ∑ _i ∈ Finset.range 3, δ / 3 = δ := by
  have h := sum_div_card (Finset.range 3) ⟨0, by simp⟩ δ
  simpa using h

end Arlib.Approximation
