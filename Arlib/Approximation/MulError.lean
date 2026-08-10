/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Two-sided multiplicative error windows

Approximation algorithms whose guarantee is *relative* accumulate their error
multiplicatively: each stage replaces a quantity `b` by something in
`[lo · b, hi · b]`, and the analysis must compose such windows, sum them over a
family, iterate them along a chain, and finally calibrate the per-stage
tolerance so that the composed window is the one the theorem promises.

`Arlib.relErr` (in `Arlib.Prelude`) already names the symmetric window
`(1 ± ε)·b`.  What is missing — and what every relative-accuracy argument needs —
is the *asymmetric* window `[lo·b, hi·b]`, because that is the shape a window
takes after composition: `(1-δ)^n` and `(1+δ)^n` are not of the form `1 ∓ ε` for
a common `ε`.

* `Between lo hi a b` — `a` lies in the window `[lo·b, hi·b]`.
* `Between.trans` — windows compose by multiplying their endpoints.
* `Between.sum` — a window shared by every member of a family is inherited by
  the sums.  This lemma itself needs no sign hypothesis, because the two
  inequalities are summed term by term; but note that *obtaining* the per-term
  windows for scaled quantities does need nonnegative coefficients
  (`Between.const_mul`), and a negative coefficient genuinely breaks the
  conclusion.
* `Between.pow_of_chain` — a per-step window `[lo, hi]` along `F 0, …, F n`
  telescopes to `[lo^n, hi^n]`.
* `one_add_div_pow_le` / `one_sub_div_pow_ge` — the calibration
  `δ = ε/(3n)`: `(1 + ε/(3n))^n ≤ 1 + ε` and `1 - ε ≤ (1 - ε/(3n))^n` for
  `ε ∈ [0,1]`, hence `Between.relErr_of_calibrated`, which turns a telescoped
  window straight into `a ∈ relErr ε b`.

The `(1+·)^n` bound is proved by the elementary induction
`(1+a)^n ≤ 1 + 2na` valid whenever `n·a ≤ 1/2` (`one_add_pow_le_one_add_two_mul`);
no exponential and no logarithm appears.

## The `(1 ± ε)` calculus

`Between.trans` composes two windows around a *chain* `a → b → c`.  Chains of
`(1 ± ε)` manipulations also need the windows of two *independent* pairs to be
combined, which is what the second half of this file supplies:

* `Between.mul` / `relErr_mul` — `(1±ε)(1±ε') ⊆ (1 ± (ε + ε' + εε'))`;
* `Between.pow` / `relErr_pow` — the honest form of the informal identity
  `(1±ε)^n = (1±nε)`.  It is **not** an identity: `(1+ε)^n > 1 + nε` whenever
  `ε > 0` and `n ≥ 2` (`one_add_pow_lt_one_add_mul_example`).  The correct
  statement needs a hypothesis `n·ε ≤ 1/2` and a factor two on the upper side;
* `Between.prod` / `relErr_prod` — the `Finset.prod` companion of `Between.sum`;
* `Between.div` / `relErr_div` — a **ratio** of two `(1±ε)` quantities is
  `(1 ± 2ε/(1-ε))`, not `(1±ε)`.  The failure of the naive form is recorded as
  `relErr_div_counterexample`;
* `compose_tol_le` and `tol_absorb` — the bookkeeping that turns a composed
  tolerance `ε + ε' + εε'` back into a named target tolerance.

Nothing here mentions any particular data structure: this is the arithmetic every
relative-error guarantee in the area runs on, which is why it sits at area level
rather than under `Coresets/`.  No `sorry`.

## Source

Three statements below (`relErr_div_same`, `relErr_div_counterexample`,
`tol_absorb`) record corrections to, and calibrations of, the analysis of
[ACJR21]: Marcelo Arenas, Luis Alberto Croquevielle, Rajesh Jayaram, Cristian
Riveros, *#NFA Admits an FPRAS: Efficient Enumeration, Counting, and Uniform
Generation for Logspace Classes*, J. ACM **68**(6), art. 48, 2021
(arXiv:1906.09226), together with its conjunctive-query companion *When Is
Approximate Counting for Conjunctive Queries Tractable?*, STOC 2021
(arXiv:2005.10029).  That work is cited here by the labels of the authors'
manuscript, which is not distributed with this library.
-/
import Arlib.Prelude
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Arlib.Approximation

open scoped BigOperators
open Finset

/-! ## The window -/

/-- `Between lo hi a b` says that `a` lies in the multiplicative window
`[lo · b, hi · b]` around `b`.  Unlike `Arlib.relErr` the window is allowed to
be asymmetric, which is what composition forces: composing `(1 ± δ)` with itself
`n` times gives `[(1-δ)^n, (1+δ)^n]`. -/
def Between (lo hi a b : ℝ) : Prop := lo * b ≤ a ∧ a ≤ hi * b

namespace Between

variable {lo hi lo' hi' a b c : ℝ}

theorem lower (h : Between lo hi a b) : lo * b ≤ a := h.1

theorem upper (h : Between lo hi a b) : a ≤ hi * b := h.2

theorem mk (h₁ : lo * b ≤ a) (h₂ : a ≤ hi * b) : Between lo hi a b := ⟨h₁, h₂⟩

/-- The trivial window: every value lies in `[1·b, 1·b]` around itself. -/
theorem refl (a : ℝ) : Between 1 1 a a := ⟨by ring_nf; exact le_refl a, by ring_nf; exact le_refl a⟩

/-- Rewriting a window along an equality of the *outer* value. -/
theorem of_eq (h : a = b) : Between 1 1 a b := by
  subst h; exact refl a

/-- **Windows compose.**  If `a` is within `[lo', hi']` of `b` and `b` is within
`[lo, hi]` of `c`, then `a` is within `[lo'·lo, hi'·hi]` of `c`.

The nonnegativity of the *outer* endpoints is needed and is exactly what makes
the two inequalities chain: a negative multiplier would reverse them. -/
theorem trans (hlo' : 0 ≤ lo') (hhi' : 0 ≤ hi')
    (hab : Between lo' hi' a b) (hbc : Between lo hi b c) :
    Between (lo' * lo) (hi' * hi) a c := by
  refine ⟨?_, ?_⟩
  · calc lo' * lo * c = lo' * (lo * c) := by ring
      _ ≤ lo' * b := by exact mul_le_mul_of_nonneg_left hbc.1 hlo'
      _ ≤ a := hab.1
  · calc a ≤ hi' * b := hab.2
      _ ≤ hi' * (hi * c) := by exact mul_le_mul_of_nonneg_left hbc.2 hhi'
      _ = hi' * hi * c := by ring

/-- A window is preserved by multiplying both sides by a nonnegative scalar. -/
theorem const_mul (hc : 0 ≤ c) (h : Between lo hi a b) :
    Between lo hi (c * a) (c * b) := by
  refine ⟨?_, ?_⟩
  · calc lo * (c * b) = c * (lo * b) := by ring
      _ ≤ c * a := mul_le_mul_of_nonneg_left h.1 hc
  · calc c * a ≤ c * (hi * b) := mul_le_mul_of_nonneg_left h.2 hc
      _ = hi * (c * b) := by ring

/-- Widening the window. -/
theorem mono (hb : 0 ≤ b) (hl : lo' ≤ lo) (hh : hi ≤ hi') (h : Between lo hi a b) :
    Between lo' hi' a b :=
  ⟨le_trans (mul_le_mul_of_nonneg_right hl hb) h.1,
   le_trans h.2 (mul_le_mul_of_nonneg_right hh hb)⟩

/-- **A shared window is inherited by sums.**  The two inequalities are summed
term by term, so this needs no sign hypothesis.

Do not read more into that than it says: a *weighted* sum `∑ cᵢ · aᵢ` inherits the
window only when the `cᵢ` are nonnegative, since that is what `Between.const_mul`
needs to produce the per-term windows in the first place.  With coefficients
`(1, -1)` the conclusion is false. -/
theorem sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, Between lo hi (f i) (g i)) :
    Between lo hi (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => (h i hi').1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => (h i hi').2

/-- **Telescoping.**  A per-step window `[lo, hi]` along `F 0, F 1, …, F n`
composes to the window `[lo^n, hi^n]` between the endpoints. -/
theorem pow_of_chain (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (F : ℕ → ℝ) (n : ℕ)
    (h : ∀ t < n, Between lo hi (F (t + 1)) (F t)) :
    Between (lo ^ n) (hi ^ n) (F n) (F 0) := by
  induction n with
  | zero => simpa using refl (F 0)
  | succ n ih =>
      have hstep : Between lo hi (F (n + 1)) (F n) := h n (Nat.lt_succ_self n)
      have hprev : Between (lo ^ n) (hi ^ n) (F n) (F 0) :=
        ih fun t ht => h t (lt_trans ht (Nat.lt_succ_self n))
      have := trans hlo hhi hstep hprev
      simpa [pow_succ, mul_comm] using this

/-- **Two independent windows multiply.**  If `a` sits in `[lo·b, hi·b]` and `a'`
sits in `[lo'·b', hi'·b']`, then `a·a'` sits in `[lo·lo'·(b·b'), hi·hi'·(b·b')]`.

This is *not* `Between.trans`: `trans` composes two windows along a chain
`a → b → c` of three values, whereas this combines windows around two unrelated
pairs.  It is the step behind `(1±ε)(1±ε') ⊆ (1 ± (ε + ε' + εε'))`.

The four nonnegativity hypotheses are what make the two inequalities multiply in
the right direction; `0 ≤ a`, `0 ≤ a'` and `0 ≤ hi·b` are *derived*, so they are
not asked for. -/
theorem mul {a' b' : ℝ} (hlo : 0 ≤ lo) (hlo' : 0 ≤ lo') (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (h : Between lo hi a b) (h' : Between lo' hi' a' b') :
    Between (lo * lo') (hi * hi') (a * a') (b * b') := by
  have ha : 0 ≤ a := le_trans (mul_nonneg hlo hb) h.1
  have ha' : 0 ≤ a' := le_trans (mul_nonneg hlo' hb') h'.1
  have hhib : 0 ≤ hi * b := le_trans ha h.2
  refine ⟨?_, ?_⟩
  · calc lo * lo' * (b * b') = lo * b * (lo' * b') := by ring
      _ ≤ a * a' := mul_le_mul h.1 h'.1 (mul_nonneg hlo' hb') ha
  · calc a * a' ≤ hi * b * (hi' * b') := mul_le_mul h.2 h'.2 ha' hhib
      _ = hi * hi' * (b * b') := by ring

/-- **Powers.**  A window `[lo·b, hi·b]` raises to the window `[lo^n·b^n, hi^n·b^n]`
around `b^n`.

Unlike `Between.pow_of_chain`, which telescopes a *per-step* window along a chain,
this raises a single window to a power; it is the `(1±ε)^n` step. -/
theorem pow (hlo : 0 ≤ lo) (hb : 0 ≤ b) (n : ℕ) (h : Between lo hi a b) :
    Between (lo ^ n) (hi ^ n) (a ^ n) (b ^ n) := by
  have ha : 0 ≤ a := le_trans (mul_nonneg hlo hb) h.1
  refine ⟨?_, ?_⟩
  · calc lo ^ n * b ^ n = (lo * b) ^ n := (mul_pow _ _ n).symm
      _ ≤ a ^ n := pow_le_pow_left₀ (mul_nonneg hlo hb) h.1 n
  · calc a ^ n ≤ (hi * b) ^ n := pow_le_pow_left₀ ha h.2 n
      _ = hi ^ n * b ^ n := mul_pow _ _ n

/-- **A shared window is inherited by products.**  The `Finset.prod` companion of
`Between.sum`.

Contrast with `Between.sum`, which needs no hypotheses at all: here the per-factor
windows have to be multiplied together, so the lower endpoint and every base must
be nonnegative — exactly the hypotheses of `Between.mul`. -/
theorem prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hlo : 0 ≤ lo)
    (hg : ∀ i ∈ s, 0 ≤ g i) (h : ∀ i ∈ s, Between lo hi (f i) (g i)) :
    Between (lo ^ s.card) (hi ^ s.card) (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  have elo : lo ^ s.card * ∏ i ∈ s, g i = ∏ i ∈ s, lo * g i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have ehi : hi ^ s.card * ∏ i ∈ s, g i = ∏ i ∈ s, hi * g i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  refine ⟨?_, ?_⟩
  · rw [elo]
    exact Finset.prod_le_prod (fun i hi' => mul_nonneg hlo (hg i hi'))
      (fun i hi' => (h i hi').1)
  · rw [ehi]
    exact Finset.prod_le_prod
      (fun i hi' => le_trans (mul_nonneg hlo (hg i hi')) (h i hi').1)
      (fun i hi' => (h i hi').2)

/-- **Quotients.**  Dividing a window by a window *crosses* the endpoints: the
smallest possible quotient is the smallest numerator over the largest denominator.

This is the shape that makes [ACJR21]'s ratio-of-estimates step wrong — see
`relErr_div` and `relErr_div_counterexample`.  The denominator window must be
bounded away from `0` (`0 < lo'`, `0 < b'`), which is what guarantees `a' > 0`. -/
theorem div {a' b' : ℝ} (hlo : 0 ≤ lo) (hb : 0 ≤ b) (hlo' : 0 < lo') (hb' : 0 < b')
    (h : Between lo hi a b) (h' : Between lo' hi' a' b') :
    Between (lo / hi') (hi / lo') (a / a') (b / b') := by
  have ha : 0 ≤ a := le_trans (mul_nonneg hlo hb) h.1
  have ha' : 0 < a' := lt_of_lt_of_le (mul_pos hlo' hb') h'.1
  refine ⟨?_, ?_⟩
  · calc lo / hi' * (b / b') = lo * b / (hi' * b') := div_mul_div_comm _ _ _ _
      _ ≤ a / a' := div_le_div₀ ha h.1 ha' h'.2
  · calc a / a' ≤ hi * b / (lo' * b') := div_le_div₀ (le_trans ha h.2) h.2 (mul_pos hlo' hb') h'.1
      _ = hi / lo' * (b / b') := (div_mul_div_comm _ _ _ _).symm

/-- The symmetric window `Between (1-ε) (1+ε)` is exactly `Arlib.relErr`. -/
theorem relErr_iff {ε : ℝ} : Between (1 - ε) (1 + ε) a b ↔ a ∈ relErr ε b := Iff.rfl

end Between

/-! ## Calibrating the per-step tolerance

The algorithm sets its per-step tolerance to `δ = ε/(3n)` and pays it `n` times.
These are the two inequalities that turn `(1 ± δ)^n` back into `1 ± ε`. -/

/-- An elementary Bernoulli-type upper bound: if `n·a ≤ 1/2` then
`(1+a)^n ≤ 1 + 2na`.

Proved by induction; the step needs `2·k·a ≤ 1` for `k < n`, which is exactly
what `n·a ≤ 1/2` supplies.  No exponential is involved. -/
theorem one_add_pow_le_one_add_two_mul {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hn : (n : ℝ) * a ≤ 1 / 2) :
    (1 + a) ^ n ≤ 1 + 2 * n * a := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : (k : ℝ) * a ≤ 1 / 2 := by
        have : (k : ℝ) * a ≤ ((k : ℝ) + 1) * a := by nlinarith
        push_cast at hn; linarith
      have ihk : (1 + a) ^ k ≤ 1 + 2 * k * a := ih hk
      have hka : 2 * (k : ℝ) * a ≤ 1 := by linarith
      have hpos : (0 : ℝ) ≤ 1 + a := by linarith
      calc (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
        _ ≤ (1 + 2 * k * a) * (1 + a) := by
              exact mul_le_mul_of_nonneg_right ihk hpos
        _ ≤ 1 + 2 * ((k : ℝ) + 1) * a := by nlinarith
        _ = 1 + 2 * ((k + 1 : ℕ) : ℝ) * a := by push_cast; ring

/-- **Upper calibration.**  For `ε ∈ [0,1]` and `n ≥ 1`,
`(1 + ε/(3n))^n ≤ 1 + ε`.

The slack is real: the bound actually obtained is `1 + 2ε/3`. -/
theorem one_add_div_pow_le {ε : ℝ} {n : ℕ} (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / (3 * n)) ^ n ≤ 1 + ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 ≤ ε / (3 * n) := div_nonneg hε (by linarith)
  have hprod : (n : ℝ) * (ε / (3 * n)) = ε / 3 := by
    field_simp
    ring
  have hn2 : (n : ℝ) * (ε / (3 * n)) ≤ 1 / 2 := by rw [hprod]; linarith
  calc (1 + ε / (3 * n)) ^ n ≤ 1 + 2 * n * (ε / (3 * n)) :=
        one_add_pow_le_one_add_two_mul ha n hn2
    _ = 1 + 2 * (ε / 3) := by rw [mul_assoc, hprod]
    _ ≤ 1 + ε := by linarith

/-- **Lower calibration.**  For `ε ∈ [0,1]` and any `n`,
`1 - ε ≤ (1 - ε/(3n))^n`.

This is Bernoulli's inequality (`one_add_mul_le_pow`) at `a = -ε/(3n)`; the
bound actually obtained is `1 - ε/3`. -/
theorem one_sub_div_pow_ge {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - ε ≤ (1 - ε / (3 * n)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simpa using hε
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : -2 ≤ -(ε / (3 * n)) := by
    have : ε / (3 * n) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hber := one_add_mul_le_pow ha n
  have hprod : (n : ℝ) * (ε / (3 * n)) = ε / 3 := by
    field_simp
    ring
  have : (1 : ℝ) - ε / 3 ≤ (1 - ε / (3 * n)) ^ n := by
    have h1 : (1 : ℝ) + (n : ℝ) * -(ε / (3 * n)) = 1 - ε / 3 := by
      rw [mul_neg, hprod]; ring
    have h2 : (1 : ℝ) + -(ε / (3 * n)) = 1 - ε / (3 * n) := by ring
    rw [h1, h2] at hber
    exact hber
  linarith

/-- **The calibration, packaged.**  A telescoped window `[(1-δ)^n, (1+δ)^n]`
with `δ = ε/(3n)` is contained in the relative-error window `(1 ± ε)`. -/
theorem Between.relErr_of_calibrated {ε a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b)
    (h : Between ((1 - ε / (3 * n)) ^ n) ((1 + ε / (3 * n)) ^ n) a b) :
    a ∈ relErr ε b :=
  Between.mono hb (one_sub_div_pow_ge hε hε1) (one_add_div_pow_le hn hε hε1) h

/-! ## Reciprocal windows

The two facts a median-of-means / reciprocal-estimator argument runs on: passing a
relative-error window through `x ↦ 1/x`, and the observation that a "loose" `(1±ε/2)`
window sits inside the "failing" reciprocal interval `[b/(1+ε), b/(1-ε)]`.  Both are
pure algebra over `ℝ`, independent of any probability model. -/

/-- **Reciprocal of a relative-error interval.**  For `x, c > 0` and `0 ≤ ε < 1`,
`1/x ∈ (1±ε)·c` iff `x ∈ [1/((1+ε)c), 1/((1-ε)c)]` — the passage between an estimate
`1/median ∈ (1±ε)/N` and the median lying in the reciprocal window `(1±ε)⁻¹·N`. -/
theorem recip_mem_relErr {x c ε : ℝ} (hx : 0 < x) (hc : 0 < c) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    1 / x ∈ relErr ε c ↔ x ∈ Set.Icc (1 / ((1 + ε) * c)) (1 / ((1 - ε) * c)) := by
  have hd1 : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  have hd2 : 0 < (1 + ε) * c := mul_pos (by linarith) hc
  rw [mem_relErr, Set.mem_Icc, le_div_iff₀ hx, div_le_iff₀ hx, div_le_iff₀ hd2,
    le_div_iff₀ hd1]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> nlinarith [ha, hb]

/-- **Failing intervals are loose.**  For `0 ≤ ε < 1` and `b ≥ 0`, the loose interval
`(1±ε/2)·b` is contained in the failing interval `[b/(1+ε), b/(1-ε)]`.  Hence a value
outside the failing interval is outside `(1±ε/2)b` — the step that lets an `(1±ε/2)`
concentration bound cap the `(1±ε)⁻¹` failure probability. -/
theorem relErr_half_subset_recip {b ε : ℝ} (hb : 0 ≤ b) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    relErr (ε / 2) b ⊆ Set.Icc (b / (1 + ε)) (b / (1 - ε)) := by
  intro y hy
  rw [mem_relErr] at hy
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have h1 : b / (1 + ε) ≤ (1 - ε / 2) * b := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hb hε0) (show (0 : ℝ) ≤ 1 - ε by linarith)]
    linarith [hy.1]
  · have h2 : (1 + ε / 2) * b ≤ b / (1 - ε) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hb hε0) (show (0 : ℝ) ≤ 1 + ε by linarith)]
    linarith [hy.2]

/-! ## The `(1 ± ε)` calculus

The four window operations above, restated in the symmetric `relErr` form that
the papers are written in, together with the two places where the symmetric form
that a paper *would* write is simply false. -/

/-- `a ∈ (1 ± ε)·b` says exactly `|a - b| ≤ ε·b`.

The equivalence is unconditional: no sign hypothesis on `b` or on `ε` is needed,
because both sides unfold to the same pair of linear inequalities. -/
theorem mem_relErr_iff_abs {ε a b : ℝ} : a ∈ relErr ε b ↔ |a - b| ≤ ε * b := by
  rw [mem_relErr, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The `linarith`-friendly extraction: membership in `(1 ± ε)·b` unpacked into
its two bounds.  Definitionally `Iff.rfl`, provided so that callers can write
`obtain ⟨h₁, h₂⟩ := h.bounds` without recalling how `relErr` is defined. -/
theorem relErr.bounds {ε a b : ℝ} (h : a ∈ relErr ε b) :
    (1 - ε) * b ≤ a ∧ a ≤ (1 + ε) * b := h

/-! ### Products -/

/-- **Products.**  `(1±ε)·b` times `(1±ε')·b'` lands in `(1 ± (ε + ε' + εε'))·(b·b')`.

The composed tolerance really is `ε + ε' + εε'` and not `ε + ε'`: the upper bound
`(1+ε)(1+ε') = 1 + ε + ε' + εε'` is attained. -/
theorem relErr_mul {ε ε' a b a' b' : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hε' : 0 ≤ ε') (hε1' : ε' ≤ 1) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (h : a ∈ relErr ε b) (h' : a' ∈ relErr ε' b') :
    a * a' ∈ relErr (ε + ε' + ε * ε') (b * b') := by
  have hw := Between.mul (by linarith) (by linarith) hb hb'
    (Between.relErr_iff.2 h) (Between.relErr_iff.2 h')
  refine Between.relErr_iff.1 (Between.mono (mul_nonneg hb hb') ?_ ?_ hw)
  · nlinarith [mul_nonneg hε hε']
  · nlinarith

/-- **Chaining.**  If `a` is a `(1±ε)`-estimate of `b` and `b` is a
`(1±ε')`-estimate of `c`, then `a` is a `(1 ± (ε + ε' + εε'))`-estimate of `c`.

This is the `relErr` face of `Between.trans`, and is the workhorse of every
"`(1±ε)` chain": errors compose, they do not merely add. -/
theorem relErr_trans {ε ε' a b c : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hε' : 0 ≤ ε')
    (hc : 0 ≤ c) (h : a ∈ relErr ε b) (h' : b ∈ relErr ε' c) :
    a ∈ relErr (ε + ε' + ε * ε') c := by
  have hw := Between.trans (by linarith) (by linarith)
    (Between.relErr_iff.2 h) (Between.relErr_iff.2 h')
  refine Between.relErr_iff.1 (Between.mono hc ?_ ?_ hw)
  · nlinarith [mul_nonneg hε hε']
  · nlinarith

/-- **Sums.**  A tolerance shared by every summand is inherited by the sums.
No sign hypothesis is needed; this is `Between.sum` read through `relErr_iff`. -/
theorem relErr_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {ε : ℝ}
    (h : ∀ i ∈ s, f i ∈ relErr ε (g i)) :
    (∑ i ∈ s, f i) ∈ relErr ε (∑ i ∈ s, g i) :=
  Between.relErr_iff.1 (Between.sum s f g fun i hi => Between.relErr_iff.2 (h i hi))

/-! ### Powers

The informal step `(1 ± ε)^n = (1 ± nε)` is **not** an identity, and neither of
its two halves is free.  The lower half is Bernoulli's inequality and is true as
stated; the upper half is false, and needs both a hypothesis relating `n` and `ε`
and a factor two.  See `one_add_pow_lt_one_add_mul_example`. -/

/-- **The upper half of `(1 ± ε)^n = (1 ± nε)` is false.**  A witness at `n = 2`,
`ε = 1/10`: `1 + 2·(1/10) = 1.2` but `(1 + 1/10)^2 = 1.21`.

Recorded because a chain of `(1±ε)` manipulations that uses `(1+ε)^n ≤ 1 + nε`
is unsound; the correct bound is `one_add_pow_le_one_add_two_mul`, which costs a
factor two and the hypothesis `n·ε ≤ 1/2`. -/
theorem one_add_pow_lt_one_add_mul_example :
    (1 : ℝ) + 2 * (1 / 10) < (1 + 1 / 10) ^ 2 := by norm_num

/-- **The lower half**, which *is* true with the naive constant: `1 - nε ≤ (1-ε)^n`,
hence a fortiori `1 - 2nε ≤ (1-ε)^n`.

Stated with the factor two so that it pairs with `one_add_pow_le_one_add_two_mul`
into a single symmetric window.  The hypothesis `n·ε ≤ 1/2` is used only to
supply `ε ≤ 2` for Bernoulli when `n ≥ 1`. -/
theorem one_sub_two_mul_le_one_sub_pow {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε)
    (hn : (n : ℝ) * ε ≤ 1 / 2) : 1 - 2 * n * ε ≤ (1 - ε) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · norm_num
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hstep : 0 ≤ ((n : ℝ) - 1) * ε := mul_nonneg (by linarith) hε
  have hber : 1 + (n : ℝ) * -ε ≤ (1 + -ε) ^ n := one_add_mul_le_pow (by linarith) n
  rw [show (1 : ℝ) + -ε = 1 - ε by ring] at hber
  have hnε : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  linarith

/-- **The honest `(1 ± ε)^n` calibration.**  A window `[(1-ε)^n, (1+ε)^n]` sits
inside the symmetric window `(1 ± 2nε)` as soon as `0 ≤ ε` and `n·ε ≤ 1/2`.

The hypothesis `n·ε ≤ 1/2` is the one the informal identity omits: without it the
upper endpoint `(1+ε)^n` grows without any linear bound. -/
theorem Between.relErr_of_pow_calibrated {ε a b : ℝ} {n : ℕ} (hε : 0 ≤ ε)
    (hn : (n : ℝ) * ε ≤ 1 / 2) (hb : 0 ≤ b)
    (h : Between ((1 - ε) ^ n) ((1 + ε) ^ n) a b) : a ∈ relErr (2 * n * ε) b :=
  Between.mono hb (one_sub_two_mul_le_one_sub_pow hε hn)
    (one_add_pow_le_one_add_two_mul hε n hn) h

/-- **Powers of a `(1±ε)` estimate.**  If `a = (1±ε)b` then `a^n = (1 ± 2nε)b^n`,
under the hypothesis `n·ε ≤ 1/2`.

This is the sound replacement for the informal `(1±ε)^i = (1±iε)`.  Two things
differ from the informal version and both matter: the constant is `2n`, not `n`
(`one_add_pow_lt_one_add_mul_example`), and `n·ε ≤ 1/2` is a genuine hypothesis,
not a consequence of `ε` merely being "small" — it constrains `ε` *relative to*
`n`.  A bound of the form `ε < c` with `c` independent of `n` does not suffice. -/
theorem relErr_pow {ε a b : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2)
    (hb : 0 ≤ b) (h : a ∈ relErr ε b) : a ^ n ∈ relErr (2 * n * ε) (b ^ n) := by
  refine Between.relErr_of_pow_calibrated hε hn (pow_nonneg hb n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simpa using Between.refl (1 : ℝ)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hstep : 0 ≤ ((n : ℝ) - 1) * ε := mul_nonneg (by linarith) hε
  exact Between.pow (by linarith) hb n (Between.relErr_iff.2 h)

/-- **Products over a `Finset`.**  The `Finset.prod` companion of `relErr_sum`:
a shared tolerance `ε` over `s.card` factors composes to `2·|s|·ε`, provided
`|s|·ε ≤ 1/2`.

Contrast `relErr_sum`, which is free: summation preserves the tolerance, whereas
multiplication multiplies it by the number of factors. -/
theorem relErr_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hcard : (s.card : ℝ) * ε ≤ 1 / 2) (hg : ∀ i ∈ s, 0 ≤ g i)
    (h : ∀ i ∈ s, f i ∈ relErr ε (g i)) :
    (∏ i ∈ s, f i) ∈ relErr (2 * s.card * ε) (∏ i ∈ s, g i) := by
  refine Between.relErr_of_pow_calibrated hε hcard (Finset.prod_nonneg hg) ?_
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simpa using Between.refl (1 : ℝ)
  have hn1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hstep : 0 ≤ ((s.card : ℝ) - 1) * ε := mul_nonneg (by linarith) hε
  exact Between.prod s f g (by linarith) hg fun i hi => Between.relErr_iff.2 (h i hi)

/-! ### Quotients

A ratio of two `(1±ε)` quantities is **not** `(1±ε)`.  Both endpoints move: the
largest ratio is `(1+ε)/(1-ε)` and the smallest is `(1-ε)/(1+ε)`, so the smallest
symmetric window containing the ratio has half-width `2ε/(1-ε)`, which blows up as
`ε → 1`. -/

/-- **Quotients.**  If `a = (1±ε)b` and `a' = (1±ε')b'` with `b' > 0` and `ε' < 1`,
then `a/a' = (1 ± (ε+ε')/(1-ε'))·(b/b')`.

The denominator's tolerance enters *divided by* `1-ε'`, which is why `ε' < 1` is
required and why the composed tolerance is not simply `ε + ε'`. -/
theorem relErr_div {ε ε' a b a' b' : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hε' : 0 ≤ ε') (hε1' : ε' < 1) (hb : 0 ≤ b) (hb' : 0 < b')
    (h : a ∈ relErr ε b) (h' : a' ∈ relErr ε' b') :
    a / a' ∈ relErr ((ε + ε') / (1 - ε')) (b / b') := by
  have h1e' : (0 : ℝ) < 1 - ε' := by linarith
  have h1p' : (0 : ℝ) < 1 + ε' := by linarith
  have hne : (1 : ℝ) - ε' ≠ 0 := ne_of_gt h1e'
  have hne' : (1 : ℝ) + ε' ≠ 0 := ne_of_gt h1p'
  have hw := Between.div (by linarith) hb h1e' hb'
    (Between.relErr_iff.2 h) (Between.relErr_iff.2 h')
  refine Between.relErr_iff.1 (Between.mono (div_nonneg hb hb'.le) ?_ ?_ hw)
  · rw [← sub_nonneg]
    have key : (1 - ε) / (1 + ε') - (1 - (ε + ε') / (1 - ε'))
        = (2 * ε * ε' + 2 * ε' ^ 2) / ((1 + ε') * (1 - ε')) := by
      field_simp; ring
    rw [key]
    exact div_nonneg (by nlinarith [mul_nonneg hε hε', sq_nonneg ε'])
      (mul_nonneg h1p'.le h1e'.le)
  · have key : (1 + ε) / (1 - ε') = 1 + (ε + ε') / (1 - ε') := by field_simp
    exact le_of_eq key

/-- **The step the paper writes as `(1±ε)`.**  A ratio of two `(1±ε)` quantities
is `(1 ± 2ε/(1-ε))`.

This is the corrected form of [ACJR21]'s ratio-of-estimates step, where
the ratio `p̃ⱼ = Ñ(sⁱ,tⱼ)/Ñ(sⁱ,tⱼ₋₁)` of two `(1±ε₁)` estimates is asserted to be
`(1±ε₁)`.  It is not; the true tolerance is `2ε₁/(1-ε₁) = 2ε₁ + O(ε₁²)`, a factor
two larger.  `relErr_div_counterexample` shows the naive form genuinely fails. -/
theorem relErr_div_same {ε a b a' b' : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hb : 0 ≤ b) (hb' : 0 < b') (h : a ∈ relErr ε b) (h' : a' ∈ relErr ε b') :
    a / a' ∈ relErr (2 * ε / (1 - ε)) (b / b') := by
  have hd := relErr_div hε hε1.le hε hε1 hb hb' h h'
  rwa [show (ε + ε) / (1 - ε) = 2 * ε / (1 - ε) by ring] at hd

/-- **A ratio of two `(1±ε)` quantities need not be `(1±ε)`.**  With `ε = 1/2`,
`b = b' = 1`, `a = 3/2` and `a' = 1/2`, both numerator and denominator lie in
`(1 ± 1/2)·1`, but the ratio is `3`, well outside `(1 ± 1/2)·1 = [1/2, 3/2]`.

The witness for the correction to [ACJR21] recorded above. -/
theorem relErr_div_counterexample :
    (3 / 2 : ℝ) ∈ relErr (1 / 2) 1 ∧ (1 / 2 : ℝ) ∈ relErr (1 / 2) 1 ∧
      (3 / 2 : ℝ) / (1 / 2) ∉ relErr (1 / 2) (1 / 1) := by
  refine ⟨by norm_num [mem_relErr], by norm_num [mem_relErr], ?_⟩
  norm_num [mem_relErr]

/-- **Reciprocals.**  `1/a = (1 ± ε/(1-ε))·(1/b)` when `a = (1±ε)b`, `b > 0` and
`ε < 1`.  The special case `ε = 0` in the numerator of `relErr_div`. -/
theorem relErr_one_div {ε a b : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hb : 0 < b)
    (h : a ∈ relErr ε b) : 1 / a ∈ relErr (ε / (1 - ε)) (1 / b) := by
  have hd := relErr_div (ε := 0) (a := 1) (b := 1) le_rfl zero_le_one hε hε1 zero_le_one hb
    (by norm_num [mem_relErr]) h
  rwa [show (0 + ε) / (1 - ε) = ε / (1 - ε) by ring] at hd

/-! ### Absorbing a composed tolerance into a named one

The last step of every chain: the composed tolerance `ε + ε' + εε'` has to be
shown to be at most the tolerance the theorem promises.  `Between.mono` does the
transport; these two lemmas do the arithmetic. -/

/-- **Discharging a composed tolerance.**  To prove `ε + ε' + εε' ≤ c` it suffices
to prove the *linear* bound `ε + 2ε' ≤ c`, provided `ε ≤ 1` and `0 ≤ ε'`.

This is what makes a chain mechanical: the quadratic cross term never has to be
handled by hand, only `ε·ε' ≤ ε'`. -/
theorem compose_tol_le {a b c : ℝ} (ha1 : a ≤ 1) (hb : 0 ≤ b) (h : a + 2 * b ≤ c) :
    a + b + a * b ≤ c := by
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) hb]

/-- **A worked instance of slack absorption.**  For `r ≥ 4` and `ε ∈ [0,1]`,
composing the tolerances `ε/(200r³)` and `ε/(200r⁴)` stays inside `ε/(100r³)`:

`ε/(200r³) + ε/(200r⁴) + ε/(200r³)·ε/(200r⁴) ≤ ε/(100r³)`.

This is the shape of the "absorb a small additive slack" steps in [ACJR21]'s
partition-size analysis; the hypothesis `r ≥ 4` there is exactly what makes
the `r⁴` term fit in the room left by doubling `200r³` to `100r³`. -/
theorem tol_absorb {ε r : ℝ} (hr : 4 ≤ r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε / (200 * r ^ 3) + ε / (200 * r ^ 4)
        + ε / (200 * r ^ 3) * (ε / (200 * r ^ 4)) ≤ ε / (100 * r ^ 3) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have h7 : (0 : ℝ) < 40000 * r ^ 7 := by positivity
  rw [← sub_nonneg]
  have key : ε / (100 * r ^ 3) - (ε / (200 * r ^ 3) + ε / (200 * r ^ 4)
      + ε / (200 * r ^ 3) * (ε / (200 * r ^ 4)))
      = (200 * ε * r ^ 4 - 200 * ε * r ^ 3 - ε ^ 2) / (40000 * r ^ 7) := by
    field_simp; ring
  rw [key]
  refine div_nonneg ?_ h7.le
  have h3 : (64 : ℝ) ≤ r ^ 3 := by
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hr 3
    norm_num at hc
    linarith
  have hp : (192 : ℝ) ≤ r ^ 3 * (r - 1) := by
    nlinarith [mul_le_mul h3 (by linarith : (3 : ℝ) ≤ r - 1) (by norm_num : (0:ℝ) ≤ 3)
      (by positivity : (0:ℝ) ≤ r ^ 3)]
  nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ 200 * ε),
    mul_nonneg hε (sub_nonneg.2 hε1)]

end Arlib.Approximation
