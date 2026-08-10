/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.Markov
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# From a high-moment bound to an exponential tail

`Arlib.Probability.MomentMethod` supplies the *generalized Chebyshev* step

  `Pr[|X - μ| ≥ a] ≤ Ex[(X - μ)^{2t}] / a^{2t}`,

which converts control of a single high even moment into a **polynomial** tail.
The Schmidt–Siegel–Srinivasan `k`-wise Chernoff bound is obtained from that step
by *optimizing over `t`*: if the `2t`-th central moment obeys a bound of Stirling
shape, then a suitable choice of `t` turns the polynomial bound into an
**exponential** one.  This file isolates that optimization.  It is pure real
analysis: nothing here knows that `X` is a sum, or that anything is `k`-wise
independent.  The combinatorial input — the moment bound itself — is taken as a
hypothesis, so that the two halves of the argument can be developed and checked
independently.

## The optimization, in one line

Suppose the `2t`-th central moment satisfies, for every `t` in an allowed range,

  `Ex[(X - μ)^{2t}] ≤ K · (2 t μ / e)^t`.                                  (H)

Markov at `a` then gives

  `Pr[|X - μ| ≥ a] ≤ K · (2 t μ / (e a²))^t`,

and as soon as `2 t μ ≤ a²` the base of that power is at most `e⁻¹`, so the whole
bound collapses to `K · e^{-t}`.  Everything after that is bookkeeping: `t` has to
be a natural number, so one rounds, and the constant `K` has to be absorbed, so
one spends `log K` of the exponent on it.

Concretely, with a "deviation budget" `s` satisfying `s μ ≤ a²`, choosing

  `t = ⌈s/3 + d⌉₊`,   where `K ≤ e^d`,

works as soon as `s ≥ 6 (1 + d)`: the ceiling gives `t ≥ s/3 + d`, hence
`K e^{-t} ≤ e^{d - t} ≤ e^{-s/3}`, while `t ≤ s/3 + d + 1 ≤ s/2` gives
`2 t μ ≤ s μ ≤ a²`, which is what licenses the collapse.  The result is

  `Pr[|X - μ| ≥ a] ≤ e^{-s/3}`.

## The two branches of the `k`-wise Chernoff bound

Both branches of the Schmidt–Siegel–Srinivasan statement are this one theorem
with different budgets `s`, at the same deviation `a = γ μ`:

* `γ` arbitrary, `s = γ² μ`: then `s μ = (γ μ)²` exactly, and the conclusion is
  `Pr[|X - μ| ≥ γ μ] ≤ e^{-γ² μ / 3}`  (`exp_tail_relative_of_moment_bound`);
* `γ ≥ 1`, `s = γ μ`: then `s μ = γ μ² ≤ γ² μ² = (γ μ)²`, and the conclusion is
  `Pr[|X - μ| ≥ γ μ] ≤ e^{-γ μ / 3}`  (`exp_tail_relative_of_moment_bound_ge_one`).

The second is the weaker conclusion, but it asks the moment hypothesis (H) to
hold only for `2 t ≤ γ μ` rather than for `2 t ≤ γ² μ`, which is exactly the
trade-off in the literature: for `γ ≥ 1` the Stirling-shape moment bound is only
available up to a smaller order.  The side condition `2 t ≤ s` handed to (H) is
precisely the "`k`-wise independence suffices" condition `k ≥ γ² μ` (resp.
`k ≥ γ μ`) of the paper statement, read as `2 t ≤ k`.

## Structure

* `tail_le_moment_div` — generalized Chebyshev about an **arbitrary** centre `μ`
  (the version in `MomentMethod` centres at `Ex X`);
* `tail_le_of_moment_le` — the same with the moment bound supplied as a
  hypothesis: `Ex[(X-μ)^{2t}] ≤ M` gives `Pr[|X-μ| ≥ a] ≤ M / a^{2t}`;
* `pow_div_le_exp_neg` — the analytic core: `0 ≤ b`, `0 < c`, `b e ≤ c`, `r ≤ t`
  imply `(b/c)^t ≤ e^{-r}`;
* `exists_moment_index` — the rounding lemma: for `s ≥ 6 (1 + d)` and `d ≥ 0`
  there is a positive natural `t` with `s/3 + d ≤ t` and `2 t ≤ s`;
* `exp_tail_of_moment_le_pow` — "for THIS `t`", shape-agnostic: a moment bound
  `K · B^t` with `e B ≤ a²` gives `Pr[|X-μ| ≥ a] ≤ K e^{-t}`;
* `exp_tail_of_moment_bound_at` — the same at the Stirling base `B = 2 t μ / e`;
* `exp_tail_of_moment_bound` — the assembled optimization;
* the two `γ`-branch corollaries above, plus a `K = 1` specialization.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## The Markov step about an arbitrary centre

`even_moment_tail` in `Arlib.Probability.MomentMethod` is stated about the true
mean `Ex X`.  Downstream one usually has a *named* `μ` — the mean of an idealized
model, or a quantity the mean is only known to approximate — so we repeat the
argument about an arbitrary centre.  Nothing in the proof uses that `μ` is the
mean; the deviation event is simply contained in the event that the (nonnegative,
even) power `(X - μ)^{2t}` exceeds `a^{2t}`. -/

/-- **Generalized Chebyshev about an arbitrary centre.** For any real `μ`, any
`t : ℕ` and any `a > 0`,
`Pr[|X - μ| ≥ a] ≤ Ex[(X - μ)^{2t}] / a^{2t}`.
Taking `μ = Ex X` recovers `even_moment_tail`; taking additionally `t = 1`
recovers Chebyshev. -/
theorem tail_le_moment_div {P : FinProb} (X : P.Ω → ℝ) (μ : ℝ) (t : ℕ) {a : ℝ}
    (ha : 0 < a) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|))
      ≤ P.Ex (fun ω => (X ω - μ) ^ (2 * t)) / a ^ (2 * t) := by
  have heven : Even (2 * t) := ⟨t, by ring⟩
  -- The deviation event is contained in the event that the `2t`-th power is large.
  have hsub : (univ.filter (fun ω => a ≤ |X ω - μ|))
      ⊆ (univ.filter (fun ω => a ^ (2 * t) ≤ (X ω - μ) ^ (2 * t))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨hω.1, ?_⟩
    have h1 : a ^ (2 * t) ≤ |X ω - μ| ^ (2 * t) :=
      pow_le_pow_left₀ ha.le hω.2 (2 * t)
    rwa [heven.pow_abs] at h1
  -- Markov applied to the nonnegative variable `(X - μ)^{2t}`.
  have hnn : ∀ ω, 0 ≤ (X ω - μ) ^ (2 * t) := by
    intro ω; rw [pow_mul]; positivity
  calc P.Pr (univ.filter (fun ω => a ≤ |X ω - μ|))
      ≤ P.Pr (univ.filter (fun ω => a ^ (2 * t) ≤ (X ω - μ) ^ (2 * t))) :=
        P.Pr_mono hsub
    _ ≤ P.Ex (fun ω => (X ω - μ) ^ (2 * t)) / a ^ (2 * t) :=
        P.markov _ hnn (pow_pos ha (2 * t))

/-- **The Markov step, hypothesis form.** This is the interface between the
combinatorial half of a `k`-wise Chernoff bound (which produces some explicit
`M` bounding the `2t`-th central moment) and the analytic half (which only ever
uses `M`): from `Ex[(X - μ)^{2t}] ≤ M` conclude `Pr[|X - μ| ≥ a] ≤ M / a^{2t}`. -/
theorem tail_le_of_moment_le {P : FinProb} (X : P.Ω → ℝ) (μ : ℝ) (t : ℕ) {a M : ℝ}
    (ha : 0 < a) (hmom : P.Ex (fun ω => (X ω - μ) ^ (2 * t)) ≤ M) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|)) ≤ M / a ^ (2 * t) := by
  have hpos : (0 : ℝ) < a ^ (2 * t) := pow_pos ha (2 * t)
  refine (tail_le_moment_div X μ t ha).trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hmom (inv_nonneg.mpr hpos.le)

/-! ## The analytic core

Two elementary facts do all the optimization work: a ratio bounded by `e⁻¹` has
`t`-th power at most `e^{-t}`, and an integer `t` with prescribed lower and upper
real bounds exists as soon as the window is wide enough. -/

/-- **The `e⁻¹` collapse.** If `0 ≤ b`, `0 < c` and `b · e ≤ c`, then `b / c ≤ e⁻¹`
and hence `(b/c)^t ≤ e^{-t} ≤ e^{-r}` for every real `r ≤ t`.

This is the lemma that converts a polynomial Markov bound into an exponential
one: applied with `b = 2 t μ` and `c = e a²`, its hypothesis `b e ≤ c` is just
`2 t μ ≤ a²`. -/
theorem pow_div_le_exp_neg {b c r : ℝ} {t : ℕ} (hb : 0 ≤ b) (hc : 0 < c)
    (hbc : b * Real.exp 1 ≤ c) (hrt : r ≤ (t : ℝ)) :
    (b / c) ^ t ≤ Real.exp (-r) := by
  -- `b ≤ e⁻¹ c`, obtained from `b e ≤ c` by multiplying with `e⁻¹ = exp (-1)`.
  have key : b ≤ Real.exp (-1) * c := by
    have h := mul_le_mul_of_nonneg_right hbc (Real.exp_pos (-1 : ℝ)).le
    have hcancel : b * Real.exp 1 * Real.exp (-1) = b := by
      rw [mul_assoc, ← Real.exp_add]; norm_num
    linarith
  have h1 : b / c ≤ Real.exp (-1) := (div_le_iff₀ hc).mpr key
  calc (b / c) ^ t ≤ Real.exp (-1) ^ t :=
        pow_le_pow_left₀ (div_nonneg hb hc.le) h1 t
    _ = Real.exp (-(t : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)

/-- **The rounding lemma.** The optimization wants `t ≈ s/3 + d`, but `t` must be
a natural number.  As soon as the budget `s` exceeds `6 (1 + d)` the window
`[s/3 + d, s/2]` has length at least `1`, so it contains an integer; `⌈s/3 + d⌉₊`
is one, and it is positive. -/
theorem exists_moment_index {s d : ℝ} (hd : 0 ≤ d) (hs : 6 * (1 + d) ≤ s) :
    ∃ t : ℕ, 0 < t ∧ s / 3 + d ≤ (t : ℝ) ∧ 2 * (t : ℝ) ≤ s := by
  have hx0 : (0 : ℝ) < s / 3 + d := by linarith
  refine ⟨⌈s / 3 + d⌉₊, Nat.ceil_pos.mpr hx0, Nat.le_ceil _, ?_⟩
  have h := Nat.ceil_lt_add_one (α := ℝ) hx0.le
  linarith

/-! ## The optimization

`exp_tail_of_moment_bound_at` is the "for THIS `t`" statement — every hypothesis
about `t` is explicit, and no rounding happens.  `exp_tail_of_moment_bound` feeds
it the `t` produced by `exists_moment_index`. -/

/-- **The tail bound at a fixed `t`, shape-agnostic form.** Suppose the `2t`-th
central moment is bounded by `K · B^t` for *some* base `B` small enough that
`e · B ≤ a²`.  Then Markov at `a` collapses to

  `Pr[|X - μ| ≥ a] ≤ K · e^{-t}`.

This is the entire optimization step, with neither the choice of `t` nor the
shape of the moment bound fixed: any moment estimate of the form
`Ex[(X - μ)^{2t}] ≤ K · B^t` — Stirling shape or not — feeds into it, the only
requirement being that `B` beats `a²/e`. -/
theorem exp_tail_of_moment_le_pow {P : FinProb} (X : P.Ω → ℝ) {μ a K B : ℝ} (t : ℕ)
    (ha : 0 < a) (hK : 0 ≤ K) (hB : 0 ≤ B) (hBa : B * Real.exp 1 ≤ a ^ 2)
    (hmom : P.Ex (fun ω => (X ω - μ) ^ (2 * t)) ≤ K * B ^ t) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|)) ≤ K * Real.exp (-(t : ℝ)) := by
  have ha2 : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  -- Rearrange `K B^t / a^{2t}` into `K (B / a²)^t`.
  have hrw : K * B ^ t / a ^ (2 * t) = K * (B / a ^ 2) ^ t := by
    rw [pow_mul, mul_div_assoc, ← div_pow]
  -- The base of that power is at most `e⁻¹`, by `e B ≤ a²`.
  have hkey : (B / a ^ 2) ^ t ≤ Real.exp (-(t : ℝ)) :=
    pow_div_le_exp_neg hB ha2 hBa le_rfl
  calc P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|))
      ≤ K * B ^ t / a ^ (2 * t) := tail_le_of_moment_le X μ t ha hmom
    _ = K * (B / a ^ 2) ^ t := hrw
    _ ≤ K * Real.exp (-(t : ℝ)) := mul_le_mul_of_nonneg_left hkey hK

/-- **The tail bound at a fixed `t`, Stirling shape.** Given the moment bound
`Ex[(X - μ)^{2t}] ≤ K · (2 t μ / e)^t` *at this particular `t`*, together with the
compatibility condition `2 t μ ≤ a²`, Markov collapses to

  `Pr[|X - μ| ≥ a] ≤ K · e^{-t}`.

No rounding and no choice of `t` occurs here: this is the exact content of the
optimization step, with the choice of `t` deferred to the caller.  It is
`exp_tail_of_moment_le_pow` at `B = 2 t μ / e`, for which `e B ≤ a²` is literally
`2 t μ ≤ a²`. -/
theorem exp_tail_of_moment_bound_at {P : FinProb} (X : P.Ω → ℝ) {μ a K : ℝ} (t : ℕ)
    (hμ : 0 ≤ μ) (ha : 0 < a) (hK : 0 ≤ K) (hta : 2 * (t : ℝ) * μ ≤ a ^ 2)
    (hmom : P.Ex (fun ω => (X ω - μ) ^ (2 * t))
              ≤ K * (2 * (t : ℝ) * μ / Real.exp 1) ^ t) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|)) ≤ K * Real.exp (-(t : ℝ)) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  refine exp_tail_of_moment_le_pow X t ha hK
    (div_nonneg (mul_nonneg (by positivity) hμ) he.le) ?_ hmom
  rw [div_mul_cancel₀ _ he.ne']
  exact hta

/-- **The optimization, assembled.** Let `μ > 0`, let `a > 0` be the deviation,
and let `s` be a *deviation budget* compatible with `a` in the sense `s μ ≤ a²`.
Assume the Stirling-shape moment bound

  `Ex[(X - μ)^{2t}] ≤ K · (2 t μ / e)^t`   for every `t ≥ 1` with `2 t ≤ s`,

with `K ≤ e^d` for some `d ≥ 0`.  Then, provided the budget is at least
`6 (1 + d)`,

  `Pr[|X - μ| ≥ a] ≤ e^{-s/3}`.

The proof picks `t = ⌈s/3 + d⌉₊`.  The lower bound `t ≥ s/3 + d` pays for the
constant `K` (`K e^{-t} ≤ e^{d-t} ≤ e^{-s/3}`); the upper bound `t ≤ s/2`, which
is what `s ≥ 6 (1 + d)` buys, gives `2 t μ ≤ s μ ≤ a²` and so licenses the
`e⁻¹`-collapse of `exp_tail_of_moment_bound_at`.

The condition `2 t ≤ s` guarding the moment hypothesis is deliberate: it is the
only fact about `t` that the caller of the moment bound may assume, and it is
exactly the `k`-wise independence budget of the Schmidt–Siegel–Srinivasan
statement (`2 t ≤ k` with `k ≥ s`). -/
theorem exp_tail_of_moment_bound {P : FinProb} (X : P.Ω → ℝ) {μ a s d K : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hK : 0 ≤ K) (hd : 0 ≤ d) (hKd : K ≤ Real.exp d)
    (hs : 6 * (1 + d) ≤ s) (hsa : s * μ ≤ a ^ 2)
    (hmom : ∀ t : ℕ, 0 < t → 2 * (t : ℝ) ≤ s →
        P.Ex (fun ω => (X ω - μ) ^ (2 * t))
          ≤ K * (2 * (t : ℝ) * μ / Real.exp 1) ^ t) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - μ|)) ≤ Real.exp (-s / 3) := by
  obtain ⟨t, ht0, ht1, ht2⟩ := exists_moment_index hd hs
  -- `2 t μ ≤ s μ ≤ a²`.
  have hta : 2 * (t : ℝ) * μ ≤ a ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right ht2 hμ.le) hsa
  have hstep := exp_tail_of_moment_bound_at X t hμ.le ha hK hta (hmom t ht0 ht2)
  refine hstep.trans ?_
  calc K * Real.exp (-(t : ℝ)) ≤ Real.exp d * Real.exp (-(t : ℝ)) :=
        mul_le_mul_of_nonneg_right hKd (Real.exp_pos _).le
    _ = Real.exp (d - (t : ℝ)) := by rw [← Real.exp_add, ← sub_eq_add_neg]
    _ ≤ Real.exp (-s / 3) := Real.exp_le_exp.mpr (by linarith)

/-! ## The two branches of the `k`-wise Chernoff bound

Both are `exp_tail_of_moment_bound` at the deviation `a = γ μ`, with the budget
`s` set to `γ² μ` and to `γ μ` respectively. -/

/-- **Relative-deviation form, `s = γ² μ`.** If the `2t`-th central moment obeys
`Ex[(X-μ)^{2t}] ≤ K (2 t μ / e)^t` for all `t ≥ 1` with `2 t ≤ γ² μ`, and
`γ² μ ≥ 6 (1 + d)` where `K ≤ e^d`, then

  `Pr[|X - μ| ≥ γ μ] ≤ exp (-γ² μ / 3)`.

This is the `γ ≤ 1` branch of the Schmidt–Siegel–Srinivasan bound (the hypothesis
`γ ≤ 1` is not needed for the implication itself — it is needed only to make the
moment hypothesis available in that range). -/
theorem exp_tail_relative_of_moment_bound {P : FinProb} (X : P.Ω → ℝ) {μ γ d K : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hK : 0 ≤ K) (hd : 0 ≤ d) (hKd : K ≤ Real.exp d)
    (hs : 6 * (1 + d) ≤ γ ^ 2 * μ)
    (hmom : ∀ t : ℕ, 0 < t → 2 * (t : ℝ) ≤ γ ^ 2 * μ →
        P.Ex (fun ω => (X ω - μ) ^ (2 * t))
          ≤ K * (2 * (t : ℝ) * μ / Real.exp 1) ^ t) :
    P.Pr (Finset.univ.filter (fun ω => γ * μ ≤ |X ω - μ|))
      ≤ Real.exp (-(γ ^ 2 * μ) / 3) :=
  exp_tail_of_moment_bound X hμ (mul_pos hγ hμ) hK hd hKd hs (le_of_eq (by ring)) hmom

/-- **Relative-deviation form for `γ ≥ 1`, `s = γ μ`.** If the `2t`-th central
moment obeys `Ex[(X-μ)^{2t}] ≤ K (2 t μ / e)^t` for all `t ≥ 1` with `2 t ≤ γ μ`,
and `γ μ ≥ 6 (1 + d)` where `K ≤ e^d`, then

  `Pr[|X - μ| ≥ γ μ] ≤ exp (-γ μ / 3)`.

The conclusion is weaker than `exp_tail_relative_of_moment_bound`, but the moment
hypothesis is asked for on the smaller range `2 t ≤ γ μ`, which for `γ ≥ 1` is
the range in which a Stirling-shape moment bound is actually available. -/
theorem exp_tail_relative_of_moment_bound_ge_one {P : FinProb} (X : P.Ω → ℝ)
    {μ γ d K : ℝ} (hμ : 0 < μ) (hγ : 1 ≤ γ) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hKd : K ≤ Real.exp d) (hs : 6 * (1 + d) ≤ γ * μ)
    (hmom : ∀ t : ℕ, 0 < t → 2 * (t : ℝ) ≤ γ * μ →
        P.Ex (fun ω => (X ω - μ) ^ (2 * t))
          ≤ K * (2 * (t : ℝ) * μ / Real.exp 1) ^ t) :
    P.Pr (Finset.univ.filter (fun ω => γ * μ ≤ |X ω - μ|))
      ≤ Real.exp (-(γ * μ) / 3) := by
  have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le zero_lt_one hγ
  refine exp_tail_of_moment_bound X hμ (mul_pos hγ0 hμ) hK hd hKd hs ?_ hmom
  nlinarith [sq_nonneg μ, hμ.le, mul_pos hμ hμ]

/-- **The clean specialization `K = 1`, `d = 0`.** With no constant to pay for,
the budget condition is just `γ² μ ≥ 6`:
if `Ex[(X-μ)^{2t}] ≤ (2 t μ / e)^t` for every `t ≥ 1` with `2 t ≤ γ² μ`, then
`Pr[|X - μ| ≥ γ μ] ≤ exp (-γ² μ / 3)`. -/
theorem exp_tail_relative_of_moment_bound_one {P : FinProb} (X : P.Ω → ℝ) {μ γ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hs : 6 ≤ γ ^ 2 * μ)
    (hmom : ∀ t : ℕ, 0 < t → 2 * (t : ℝ) ≤ γ ^ 2 * μ →
        P.Ex (fun ω => (X ω - μ) ^ (2 * t)) ≤ (2 * (t : ℝ) * μ / Real.exp 1) ^ t) :
    P.Pr (Finset.univ.filter (fun ω => γ * μ ≤ |X ω - μ|))
      ≤ Real.exp (-(γ ^ 2 * μ) / 3) := by
  refine exp_tail_relative_of_moment_bound X hμ hγ zero_le_one le_rfl
    (by simp) (by linarith) ?_
  intro t ht0 ht2
  simpa using hmom t ht0 ht2

end Arlib.Probability
