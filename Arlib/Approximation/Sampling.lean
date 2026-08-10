/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Counting
import Arlib.Approximation.MulError
import Arlib.Approximation.Parsimonious
import Mathlib.Algebra.GeomSum

/-!
# From a defective sampler to an FPAUS

`Arlib.Approximation.Counting` defines `IsFPAUS` with a **multiplicative**
guarantee: every solution must be returned with probability in the window
`[(1-δ)/|U|, (1+δ)/|U|]`.  The samplers that algorithms actually deliver have two
defects, and neither is of that shape:

* an undetectable **preprocessing failure**, which happens with some probability
  `δ₀` and after which the sampler's law is completely unconstrained.  This
  produces an *additive* `δ₀` perturbation of the output law, not a multiplicative
  one;
* a detectable **`FAIL` output**, which happens with probability at most `3/4`
  (`1/2` after three repetitions, since `(3/4)³ < 1/2`) — **on an instance that
  has something to sample**.

**The `FAIL` bound is conditional on `U ≠ ∅`, and must be.**  The source —
[ACJR21]: Marcelo Arenas, Luis Alberto Croquevielle, Rajesh Jayaram, Cristian
Riveros, *#NFA Admits an FPRAS: Efficient Enumeration, Counting, and Uniform
Generation for Logspace Classes*, J. ACM **68**(6), art. 48, 2021
(arXiv:1906.09226), with its conjunctive-query companion *When Is Approximate
Counting for Conjunctive Queries Tractable?*, STOC 2021 (arXiv:2005.10029);
statements are cited by the labels of the authors' manuscript, which is not
distributed with this library — states `Pr[FAIL] ≤ 3/4` under the standing
proviso `T(sⁱ) ≠ ∅` of its preliminaries, and there is no reading under which
the proviso can be
dropped: on an instance with no solutions the only correct output is `FAIL`, so
`Pr[FAIL] = 1` there.  An unguarded `fail_le` therefore contradicts the `empty`
clause below — the two together assert `1 ≤ 3/4` — and makes
`PreprocessedSampler` unsatisfiable for any `g` that takes the value `∅`.
`PreprocessedSampler.fail_le` accordingly carries the hypothesis `(g w).Nonempty`,
exactly as `uniform` does; the empty instance is the business of `empty` alone.

This module closes both gaps, in the two steps [ACJR21, `thm:samplemain`]
takes in one line each.

## Step 1 — additive to multiplicative

This is the step the source elides.  An additive `δ₀`-approximation to the
uniform law on `U` is a multiplicative `(1 ± δ)`-approximation **as soon as
`δ₀ ≤ δ/|U|`**, and that is the entire content of the paper's
`eqn:additiverror`:

```
𝒟(t) = 1/|U| ± δ₀ = 1/|U| ± δ|U|⁻¹ = (1 ± δ)/|U|.
```

`between_of_abs_sub_le` is the arithmetic; `outProbR_mem_Icc_of_additive` is the
form `IsFPAUS.uniform` consumes.  The converse (`abs_sub_le_of_between`) is
immediate and is proved too: the two notions are *equivalent* at the calibration
`δ₀ = δ/|U|`, so nothing is lost by working additively.

The bridge from "the preprocessing fails with probability `δ₀`" to "the output
law is additively `δ₀`-close" is `abs_outProbR_mixPMF_sub_le`: a mixture that
agrees with `μ` except on an event of probability `q` has every output
probability within `q` of `μ`'s.  Crucially the failure branch is *arbitrary* —
a footnote of [ACJR21] says in as many words that the bad event cannot
be detected, so it cannot be retried away, and the lemma assumes nothing about
it.

## Step 2 — driving the `FAIL` rate down

`retryPMF μ k` runs `μ` at most `k` times and returns the first non-`FAIL`
output, or `none` if all `k` attempts fail.  The bound `k` is what keeps this
inside `PMF`: an unbounded `repeat until success` is not a `PMF` term at all
without a termination argument.  Three facts, all exact:

* `outProbR_retryPMF_none` — `Pr[FAIL] = f^k` exactly, where `f = Pr[one attempt
  FAILs]`.  With `f ≤ 1/2` this is `≤ 2^{-k}`;
* `outProbR_retryPMF` — for any event `S` not containing `none`,
  `Pr_k[S] = (∑_{i<k} f^i)·Pr₁[S]`.  The factor does not depend on `S`, so the
  **conditional law given success is exactly that of a single attempt** —
  repetition does not bias the sample.  This is the fact the source asserts
  without proof;
* `retryPMF_cost_le` — `k` attempts cost at most `k·B`.

## Step 3 — assembling an `IsFPAUS`

`PreprocessedSampler` bundles the guarantees of `thm:samplemain`'s sampler, and
`PreprocessedSampler.isFPAUS` concludes.  Two points where the statement is more
honest than the source:

**The polynomial-time clause needs `log |U| = poly`.**  `IsFPAUS.polytime` is
polynomial in `log(1/δ)`, and the preprocessing is run at `δ₀ ≈ δ/|U|`, so its
own cost is polynomial in `log(1/δ₀) = log(1/δ) + log|U|`.  That is polynomial in
the instance size *only if* `log|U|` is, which is a hypothesis
(`log_card_poly`) and not a consequence of anything else here.  The source is
right that it holds in its application — `|L_n(𝒯)| = exp(poly(n,m))` — but it is
a hypothesis nonetheless, and the whole point of the calibration
`δ₀ = δ·exp(-poly)` is that `log(1/δ₀)`, not `1/δ₀`, is what the running time
depends on.

**`Θ(log(δ⁻¹|U|))` repetitions are more than are needed.**  The source repeats
`Θ(log(δ⁻¹|L_n(𝒯)|))` times, on the grounds that exhausting all repetitions
"causes another additive `δ|U|⁻¹` error".  It does not: by `outProbR_retryPMF`
the retry loop multiplies *every* solution's probability by the same factor
`1 - f^k`, so the perturbation is already multiplicative and `f^k ≤ δ/2` — that
is, `k = Θ(log δ⁻¹)`, with no `log|U|` — suffices.  `retryCount` takes the
smaller count, and `retryCount_le` records that it is `Θ(log δ⁻¹)`.  The source's
count is sufficient, just larger by a `log|U| = poly(n,m)` factor.

`(3/4)³ < 1/2` is likewise not needed: `PreprocessedSampler` carries the raw
`3/4` bound and `retryCount` is calibrated against `3/4` directly.

## Main definitions

* `mixPMF q ν μ` — the two-point mixture: `ν` with probability `q`, else `μ`.
* `retryPMF μ k` — at most `k` attempts, first non-`FAIL` wins.
* `preTol`, `retryCount`, `retrySampler` — the calibrated assembly.
* `PreprocessedSampler` — the hypotheses of `thm:samplemain`, as a structure.

## Main results

* `between_of_abs_sub_le`, `abs_sub_le_of_between` — Step 1, both directions.
* `outProbR_retryPMF_none`, `outProbR_retryPMF`, `retryPMF_cost_le` — Step 2.
* `PreprocessedSampler.isFPAUS` — Step 3.
* `retryPMF_cost_ge`, `one_le_retryCount`, `retrySampler_cost_ge` — the cost
  bound in the *other* direction.  An upper bound on a recorded step count is
  satisfied by an algorithm that records nothing, so an upper bound alone is no
  evidence that any work was done; `retrySampler_cost_ge` says that whatever the
  attempts charge, the assembly charges at least as much, because `retryCount δ`
  is never zero on `(0,1)` and so at least one attempt is always run.  Paired
  with `retryPMF_cost_le` it sandwiches the assembled sampler's cost.
-/

universe u

namespace Arlib.Approximation

open scoped ENNReal BigOperators Classical

variable {α : Type*}

/-! ## Elementary facts about the output law

Four facts `Arlib.Approximation.Counting` does not state and every computation
below needs: that a real output probability is a probability, that the impossible
event has probability zero, that `outProb` unfolds to a `tsum` of an indicator,
and that `outProb` distributes over `PMF.bind`. -/

section OutProbBasic

variable {β γ : Type u}

/-! `outProbR_nonneg` and `outProbR_le_one` were originally proved here and in
`Arlib.Approximation.Concentration`, independently and identically.  Both are now
in `Arlib.Approximation.Counting`, the common ancestor — keeping either copy made
the area root `Arlib.Approximation` fail to elaborate, since it imports both. -/

/-- The impossible event has probability `0`. -/
@[simp] theorem outProb_empty (μ : PMF (β × ℕ)) : outProb μ (∅ : Set β) = 0 := by
  simp [outProb]

/-- The impossible event has probability `0`, as a real. -/
@[simp] theorem outProbR_empty (μ : PMF (β × ℕ)) : outProbR μ (∅ : Set β) = 0 := by
  simp [outProbR]

/-- **`outProb` as a sum.**  Unfolding `toOuterMeasure` to a `tsum` of an
indicator is what lets the `retryPMF` recursion be computed term by term.

The indicator, rather than an `if`, is deliberate: `Set.indicator` carries its
own `Classical` decision procedure, so no `Decidable` instance has to be matched
when this equation is used as a rewrite rule in either direction. -/
theorem outProb_eq_tsum (μ : PMF (β × ℕ)) (S : Set β) :
    outProb μ S = ∑' p, Set.indicator {q : β × ℕ | q.1 ∈ S} μ p :=
  PMF.toOuterMeasure_apply μ _

/-- **`outProb` distributes over `bind`.**  The output law of "draw `i` from `ρ`,
then run `F i`" is the `ρ`-average of the output laws of the `F i`.  The source
of the randomness is an arbitrary type: the mixture below binds over `Bool`. -/
theorem outProb_bind {ι : Type*} (ρ : PMF ι) (F : ι → PMF (γ × ℕ)) (S : Set γ) :
    outProb (ρ.bind F) S = ∑' i, ρ i * outProb (F i) S :=
  PMF.toOuterMeasure_bind_apply ρ F _

/-- A deterministic run whose output lands in `S` does so with probability `1`. -/
theorem outProb_pure_of_mem {p : β × ℕ} {S : Set β} (hp : p.1 ∈ S) :
    outProb (PMF.pure p) S = 1 := by
  simp [outProb, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq, hp]

/-- A deterministic run whose output misses `S` does so with probability `1`. -/
theorem outProb_pure_of_not_mem {p : β × ℕ} {S : Set β} (hp : p.1 ∉ S) :
    outProb (PMF.pure p) S = 0 := by
  simp [outProb, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq, hp]

end OutProbBasic

/-! ## Two-point mixtures

The preprocessing step of `thm:samplemain` either succeeds — after which the
sampler's law is `μ` — or fails, with probability `δ₀`, after which its law is an
arbitrary `ν`.  That is a two-point mixture, and the only thing needed about it
is that it perturbs every output probability by at most `δ₀`. -/

/-- **The two-point mixture**: run `ν` with probability `q`, otherwise run `μ`.

`q` is clamped to `[0,1]` by `min q 1` so that the definition needs no side
condition; every lemma below carries `q ≤ 1` as a hypothesis and the clamp is
then invisible. -/
noncomputable def mixPMF {β : Type u} (q : ℝ≥0∞) (ν μ : PMF β) : PMF β :=
  (PMF.bernoulli (min q 1) (min_le_right q 1)).bind fun b => cond b ν μ

/-- The output law of a mixture is the mixture of the output laws. -/
theorem outProb_mixPMF {β : Type u} {q : ℝ≥0∞} (hq : q ≤ 1) (ν μ : PMF (β × ℕ))
    (S : Set β) :
    outProb (mixPMF q ν μ) S = q * outProb ν S + (1 - q) * outProb μ S := by
  rw [mixPMF, outProb_bind, tsum_fintype, Fintype.sum_bool]
  simp [PMF.bernoulli_apply, min_eq_left hq, add_comm]

/-- The real-valued form of `outProb_mixPMF`, with a real mixing weight. -/
theorem outProbR_mixPMF {β : Type u} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ν μ : PMF (β × ℕ)) (S : Set β) :
    outProbR (mixPMF (ENNReal.ofReal q) ν μ) S
      = q * outProbR ν S + (1 - q) * outProbR μ S := by
  have hq : ENNReal.ofReal q ≤ 1 := ENNReal.ofReal_le_one.2 hq1
  have h1 : ENNReal.ofReal q * outProb ν S ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (outProb_ne_top ν S)
  have h2 : (1 - ENNReal.ofReal q) * outProb μ S ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [ENNReal.sub_ne_top]) (outProb_ne_top μ S)
  rw [outProbR, outProb_mixPMF hq, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top,
    ENNReal.toReal_ofReal hq0, ENNReal.one_toReal]
  rfl

/-- Every run of a mixture is a run of one of the two branches — the fact that
turns two cost bounds into one. -/
theorem mem_support_mixPMF {β : Type u} {q : ℝ≥0∞} {ν μ : PMF β} {x : β}
    (hx : x ∈ (mixPMF q ν μ).support) : x ∈ ν.support ∨ x ∈ μ.support := by
  rw [mixPMF, PMF.mem_support_bind_iff] at hx
  obtain ⟨b, _, hb⟩ := hx
  cases b
  · exact Or.inr hb
  · exact Or.inl hb

/-! ## Step 1 — additive error becomes multiplicative

The arithmetic inside the proof of [ACJR21, `thm:samplemain`].  It is stated first for a bare real
`1/N`, then for `outProb`, and in both directions: at `δ₀ = δ/N` the additive and
the multiplicative guarantees are *equivalent*, so working additively upstream
costs nothing. -/

/-- **Additive to multiplicative.**  A value within an additive `δ₀` of `1/N` is
within a multiplicative `(1 ± δ)` of `1/N`, provided `δ₀ ≤ δ/N`.

This is `eqn:additiverror`.  The hypothesis `δ₀ ≤ δ/N` is the calibration
`δ₀ = δ|U|⁻¹` the source performs; without it the conclusion is simply false, and
the calibration is exactly why the preprocessing has to be run at an exponentially
small tolerance. -/
theorem between_of_abs_sub_le {N a δ₀ δ : ℝ} (hδ₀ : δ₀ ≤ δ / N)
    (h : |a - 1 / N| ≤ δ₀) : Between (1 - δ) (1 + δ) a (1 / N) := by
  rw [abs_le] at h
  have hd : δ / N = δ * (1 / N) := by rw [mul_one_div]
  rw [hd] at hδ₀
  exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩

/-- **Multiplicative to additive**, the converse.  A `(1 ± δ)`-approximation to
`1/N` is an additive `δ/N`-approximation, so the two guarantees coincide at the
calibration `δ₀ = δ/N`. -/
theorem abs_sub_le_of_between {N a δ : ℝ}
    (h : Between (1 - δ) (1 + δ) a (1 / N)) : |a - 1 / N| ≤ δ / N := by
  obtain ⟨h1, h2⟩ := h
  have hd : δ / N = δ * (1 / N) := by rw [mul_one_div]
  rw [abs_le, hd]
  constructor <;> nlinarith

/-- **A mixture perturbs an output probability additively by its weight.**

If the sampler behaves as `μ` except on a preprocessing-failure event of
probability `q`, on which it behaves as the *arbitrary* `ν`, then every output
probability moves by at most `q`.  Nothing at all is assumed about `ν`: the
footnote of [ACJR21] insists that the failure cannot be detected, hence
cannot be conditioned away, and this lemma is the honest accounting of that. -/
theorem abs_outProbR_mixPMF_sub_le {β : Type u} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ν μ : PMF (β × ℕ)) (S : Set β) (c : ℝ) :
    |outProbR (mixPMF (ENNReal.ofReal q) ν μ) S - c|
      ≤ q + |outProbR μ S - c| := by
  have hA0 := outProbR_nonneg ν S
  have hA1 := outProbR_le_one ν S
  have hB0 := outProbR_nonneg μ S
  have hB1 := outProbR_le_one μ S
  rw [outProbR_mixPMF hq0 hq1]
  have hsplit : q * outProbR ν S + (1 - q) * outProbR μ S - c
      = q * (outProbR ν S - outProbR μ S) + (outProbR μ S - c) := by ring
  rw [hsplit]
  refine le_trans (abs_add _ _) (add_le_add_right ?_ _)
  rw [abs_mul, abs_of_nonneg hq0]
  have hd : |outProbR ν S - outProbR μ S| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  nlinarith

/-! ### The `Finset` form

`IsFPAUS.uniform` asks for membership in `Set.Icc ((1-δ)/|U|) ((1+δ)/|U|)`; this
is `between_of_abs_sub_le` transported to that shape, with `N = |U|`. -/

/-- **Step 1, in the shape `IsFPAUS.uniform` consumes.**

An algorithm whose output law is within an additive `δ₀` of uniform on a nonempty
`U`, with `δ₀ ≤ δ/|U|`, returns every solution with probability inside the
multiplicative window `[(1-δ)/|U|, (1+δ)/|U|]`.

No nonemptiness hypothesis is needed — but none is *useful* either.  On an empty
`U` both the hypothesis and the conclusion quantify over no `x`, and the window
`[(1-δ)/0, (1+δ)/0]` is meaningless; that is precisely why `IsFPAUS` guards its
`uniform` clause with `(g w).Nonempty` and discharges the empty case through the
separate `empty` clause instead. -/
theorem outProbR_mem_Icc_of_additive {Ω : Type u} {U : Finset Ω}
    {μ : PMF (Option Ω × ℕ)} {δ₀ δ : ℝ} (hδ₀ : δ₀ ≤ δ / U.card)
    (h : ∀ x ∈ U, |outProbR μ {some x} - 1 / U.card| ≤ δ₀) :
    ∀ x ∈ U, outProbR μ {some x} ∈ Set.Icc ((1 - δ) / U.card) ((1 + δ) / U.card) := by
  intro x hx
  obtain ⟨h1, h2⟩ := between_of_abs_sub_le hδ₀ (h x hx)
  rw [Set.mem_Icc]
  constructor
  · calc (1 - δ) / (U.card : ℝ) = (1 - δ) * (1 / U.card) := by rw [mul_one_div]
      _ ≤ _ := h1
  · calc outProbR μ {some x} ≤ (1 + δ) * (1 / U.card) := h2
      _ = (1 + δ) / (U.card : ℝ) := by rw [mul_one_div]

/-- The converse of `outProbR_mem_Icc_of_additive`: a multiplicative `(1 ± δ)`
sampler is an additive `δ/|U|` sampler. -/
theorem abs_outProbR_sub_le_of_mem_Icc {Ω : Type u} {U : Finset Ω}
    {μ : PMF (Option Ω × ℕ)} {δ : ℝ}
    (h : ∀ x ∈ U, outProbR μ {some x} ∈ Set.Icc ((1 - δ) / U.card) ((1 + δ) / U.card)) :
    ∀ x ∈ U, |outProbR μ {some x} - 1 / U.card| ≤ δ / U.card := by
  intro x hx
  obtain ⟨h1, h2⟩ := Set.mem_Icc.1 (h x hx)
  refine abs_sub_le_of_between ⟨?_, ?_⟩
  · calc (1 - δ) * (1 / (U.card : ℝ)) = (1 - δ) / U.card := by rw [mul_one_div]
      _ ≤ _ := h1
  · calc outProbR μ {some x} ≤ (1 + δ) / (U.card : ℝ) := h2
      _ = (1 + δ) * (1 / (U.card : ℝ)) := by rw [mul_one_div]

/-! ## Step 2 — bounded repeat-until-success

`retryPMF μ k` makes at most `k` attempts and returns the first non-`FAIL`
output.  The bound is essential: an unbounded loop is not a `PMF` term without a
separate termination argument, and `k` is in any case what the running-time
clause has to charge for. -/

/-- **At most `k` attempts, first success wins.**

At `k = 0` there is nothing left to try and the answer is `none` at no cost.  At
`k + 1`, one attempt is made; if it returns a sample it is returned as is, and
otherwise the remaining `k` attempts are made and their cost added to the failed
attempt's.

Failure is *detectable* — that is what `p.1.isSome` tests — which is the whole
difference between this defect and the preprocessing failure of Step 1. -/
noncomputable def retryPMF {Ω : Type u} (μ : PMF (Option Ω × ℕ)) :
    ℕ → PMF (Option Ω × ℕ)
  | 0 => PMF.pure (none, 0)
  | k + 1 => μ.bind fun p =>
      if p.1.isSome then PMF.pure p
      else (retryPMF μ k).map (fun q => (q.1, p.2 + q.2))

section Retry

variable {Ω : Type u} (μ : PMF (Option Ω × ℕ))

/-- **The recursion, at the level of output probabilities.**

One attempt either lands in `S` outright — which it can only do by *not* failing,
whence `S \ {none}` — or fails, with probability `outProb μ {none}`, and the
remaining `k` attempts start over.  Everything below is an induction on this. -/
theorem outProb_retryPMF_succ (k : ℕ) (S : Set (Option Ω)) :
    outProb (retryPMF μ (k + 1)) S
      = outProb μ (S \ {none}) + outProb μ {none} * outProb (retryPMF μ k) S := by
  rw [retryPMF, outProb_bind]
  have key : ∀ p : Option Ω × ℕ,
      μ p * outProb (if p.1.isSome then PMF.pure p
          else (retryPMF μ k).map (fun q => (q.1, p.2 + q.2))) S
        = Set.indicator {q : Option Ω × ℕ | q.1 ∈ S \ {none}} μ p
          + Set.indicator {q : Option Ω × ℕ | q.1 ∈ ({none} : Set (Option Ω))} μ p
            * outProb (retryPMF μ k) S := by
    intro p
    by_cases hp : p.1 = none
    · have hmap : outProb ((retryPMF μ k).map (fun q : Option Ω × ℕ => (q.1, p.2 + q.2))) S
          = outProb (retryPMF μ k) S := by
        have hm := outProb_map (retryPMF μ k)
          (fun q : Option Ω × ℕ => (q.1, p.2 + q.2)) id (fun _ => rfl) S
        rwa [Set.preimage_id] at hm
      rw [if_neg (by simp [hp]), hmap,
        Set.indicator_of_not_mem
          (show p ∉ {q : Option Ω × ℕ | q.1 ∈ S \ {none}} from fun hc => hc.2 hp),
        Set.indicator_of_mem
          (show p ∈ {q : Option Ω × ℕ | q.1 ∈ ({none} : Set (Option Ω))} from hp)]
      ring
    · have hsome : p.1.isSome = true := by
        cases hq : p.1 with
        | none => exact absurd hq hp
        | some _ => rfl
      rw [if_pos hsome,
        Set.indicator_of_not_mem
          (show p ∉ {q : Option Ω × ℕ | q.1 ∈ ({none} : Set (Option Ω))} from hp)]
      by_cases hs : p.1 ∈ S
      · rw [outProb_pure_of_mem hs,
          Set.indicator_of_mem
            (show p ∈ {q : Option Ω × ℕ | q.1 ∈ S \ {none}} from ⟨hs, hp⟩)]
        ring
      · rw [outProb_pure_of_not_mem hs,
          Set.indicator_of_not_mem
            (show p ∉ {q : Option Ω × ℕ | q.1 ∈ S \ {none}} from fun hc => hs hc.1)]
        ring
  rw [tsum_congr key, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    ← outProb_eq_tsum, ← outProb_eq_tsum]

/-- The real-valued form of `outProb_retryPMF_succ`. -/
theorem outProbR_retryPMF_succ (k : ℕ) (S : Set (Option Ω)) :
    outProbR (retryPMF μ (k + 1)) S
      = outProbR μ (S \ {none}) + outProbR μ {none} * outProbR (retryPMF μ k) S := by
  have hmul : outProb μ {none} * outProb (retryPMF μ k) S ≠ ⊤ :=
    ENNReal.mul_ne_top (outProb_ne_top _ _) (outProb_ne_top _ _)
  rw [outProbR, outProb_retryPMF_succ, ENNReal.toReal_add (outProb_ne_top _ _) hmul,
    ENNReal.toReal_mul]
  rfl

/-- **The `FAIL` probability is exactly `f^k`.**

`k` attempts fail only if all of them do, and — this is where the construction
earns its keep — the attempts are independent, so the probability is the exact
`k`-th power.  With `f ≤ 1/2` (the source's bound after three repetitions, since
`(3/4)³ < 1/2`) this is `≤ 2^{-k}`. -/
theorem outProbR_retryPMF_none (k : ℕ) :
    outProbR (retryPMF μ k) {none} = (outProbR μ {none}) ^ k := by
  induction k with
  | zero =>
      have h : outProb (PMF.pure ((none : Option Ω), 0)) ({none} : Set (Option Ω)) = 1 :=
        outProb_pure_of_mem rfl
      simp [retryPMF, outProbR, h]
  | succ k ih =>
      rw [outProbR_retryPMF_succ, ih, Set.diff_self, outProbR_empty]
      ring

/-- **Repetition does not bias the sample.**

For any event `S` of non-`FAIL` outputs, the retry loop's probability is the
single attempt's probability scaled by `∑_{i<k} f^i` — a factor that *does not
depend on `S`*.  Hence the law of the output conditioned on success is exactly
the law of a single attempt conditioned on success, which is what the source
asserts when it says one may "return the first sample obtained from an instance
that did not return `FAIL`".

The hypothesis `none ∉ S` is necessary and not a technicality: for `S = {none}`
the conclusion fails at `k = 0`, where the loop returns `none` with probability
`1` while the right-hand side is `0`. -/
theorem outProbR_retryPMF {S : Set (Option Ω)} (hS : none ∉ S) (k : ℕ) :
    outProbR (retryPMF μ k) S
      = (∑ i ∈ Finset.range k, (outProbR μ {none}) ^ i) * outProbR μ S := by
  have hSd : S \ {none} = S := Set.diff_singleton_eq_self hS
  induction k with
  | zero =>
      have h : outProb (PMF.pure ((none : Option Ω), 0)) S = 0 :=
        outProb_pure_of_not_mem hS
      simp [retryPMF, outProbR, h]
  | succ k ih =>
      have hgeom : ∑ i ∈ Finset.range (k + 1), (outProbR μ {none}) ^ i
          = 1 + outProbR μ {none} * ∑ i ∈ Finset.range k, (outProbR μ {none}) ^ i := by
        rw [Finset.sum_range_succ' (fun i => (outProbR μ {none}) ^ i) k, Finset.mul_sum,
          pow_zero, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]
      rw [outProbR_retryPMF_succ, hSd, ih, hgeom]
      ring

/-- **The cost of `k` attempts is `k` times the cost of one.**

Worst-case over the support, as everywhere in `Arlib.Approximation.Counting`.
The induction is the same one that defines `retryPMF`; the `+ 1` case splits on
whether the first attempt succeeded, and in both branches the accumulated cost is
bounded by `B + k·B`. -/
theorem retryPMF_cost_le {B : ℕ} (h : ∀ p ∈ μ.support, p.2 ≤ B) :
    ∀ (k : ℕ), ∀ q ∈ (retryPMF μ k).support, q.2 ≤ k * B := by
  intro k
  induction k with
  | zero =>
      intro q hq
      rw [retryPMF, PMF.mem_support_pure_iff] at hq
      simp [hq]
  | succ k ih =>
      intro q hq
      rw [retryPMF, PMF.mem_support_bind_iff] at hq
      obtain ⟨p, hp, hq⟩ := hq
      by_cases hpn : p.1 = none
      · rw [if_neg (by simp [hpn])] at hq
        obtain ⟨r, hr, hrq⟩ := mem_support_map hq
        have h1 := h p hp
        have h2 := ih r hr
        rw [← hrq]
        show p.2 + r.2 ≤ (k + 1) * B
        rw [Nat.succ_mul]
        omega
      · have hsome : p.1.isSome = true := by
          cases hq' : p.1 with
          | none => exact absurd hq' hpn
          | some _ => rfl
        rw [if_pos hsome, PMF.mem_support_pure_iff] at hq
        subst hq
        calc q.2 ≤ B := h q hp
          _ ≤ (k + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos k)

/-- **At least one attempt is paid for.**

The companion of `retryPMF_cost_le`, and the reason it is worth having: an
*upper* bound on a recorded step count is satisfied by an algorithm that records
`0`, so on its own it is no evidence that any work was done.  If every attempt
charges at least `A`, then so does the loop — provided the loop runs at all,
which is why the statement is about `k + 1` and not `k`.  At `k = 0` the loop
returns `(none, 0)` and the conclusion is false for `A > 0`.

No induction: whichever branch the first attempt takes, its own cost `p.2` is
already a summand of the total. -/
theorem retryPMF_cost_ge {A : ℕ} (h : ∀ p ∈ μ.support, A ≤ p.2) (k : ℕ) :
    ∀ q ∈ (retryPMF μ (k + 1)).support, A ≤ q.2 := by
  intro q hq
  rw [retryPMF, PMF.mem_support_bind_iff] at hq
  obtain ⟨p, hp, hq⟩ := hq
  by_cases hpn : p.1 = none
  · rw [if_neg (by simp [hpn])] at hq
    obtain ⟨r, _, hrq⟩ := mem_support_map hq
    have h1 := h p hp
    rw [← hrq]
    show A ≤ p.2 + r.2
    omega
  · have hsome : p.1.isSome = true := by
      cases hq' : p.1 with
      | none => exact absurd hq' hpn
      | some _ => rfl
    rw [if_pos hsome, PMF.mem_support_pure_iff] at hq
    subst hq
    exact h q hp

end Retry

/-! ## Calibrating the number of repetitions

`retryCount δ` is the least `k` with `(3/4)^k ≤ δ/2`, and it is `Θ(log δ⁻¹)` —
see the module docstring for why the source's `Θ(log(δ⁻¹|U|))` overshoots. -/

/-- The elementary numeric input: `log(4/3) ≥ 1/4`.

Proved from `x + 1 ≤ exp x` at `x = -1/4`, which gives `exp(1/4) ≤ 4/3`; no
numerical evaluation of `exp` is involved. -/
theorem quarter_le_log_four_thirds : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
  have hb : (3 : ℝ) / 4 ≤ Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith
  have hpos : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  rw [Real.exp_neg] at hb
  have hmul := mul_le_mul_of_nonneg_right hb hpos.le
  rw [inv_mul_cancel₀ hpos.ne'] at hmul
  have h43 : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by linarith
  calc (1 : ℝ) / 4 = Real.log (Real.exp (1 / 4)) := (Real.log_exp _).symm
    _ ≤ Real.log (4 / 3) := Real.log_le_log hpos h43

/-- **The repetition count.**  `⌈log(2/δ) / log(4/3)⌉` attempts drive the
probability that *every* attempt returns `FAIL` below `δ/2`, starting from the
per-attempt bound `3/4` of `lem:sampmain`. -/
noncomputable def retryCount (δ : ℝ) : ℕ := ⌈Real.log (2 / δ) / Real.log (4 / 3)⌉₊

/-- **The loop always runs.**  On `(0,1)` we have `2/δ > 2 > 1`, so
`log (2/δ) > 0`, and `log (4/3) > 0` by `quarter_le_log_four_thirds`; the ceiling
of a positive real is at least `1`.

This is what `retrySampler_cost_ge` needs and `retryPMF_cost_ge` cannot supply:
the lower bound on the loop's cost holds only because the loop is entered. -/
theorem one_le_retryCount {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) : 1 ≤ retryCount δ := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hL : (0 : ℝ) < Real.log (4 / 3) :=
    lt_of_lt_of_le (by norm_num) quarter_le_log_four_thirds
  have h2 : (1 : ℝ) < 2 / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  exact Nat.ceil_pos.2 (div_pos (Real.log_pos h2) hL)

/-- **The calibration.**  With `retryCount δ` attempts, `(3/4)^k ≤ δ/2`. -/
theorem pow_retryCount_le {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    (3 / 4 : ℝ) ^ retryCount δ ≤ δ / 2 := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hL : (0 : ℝ) < Real.log (4 / 3) :=
    lt_of_lt_of_le (by norm_num) quarter_le_log_four_thirds
  have h2δ : (1 : ℝ) < 2 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hlog0 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg h2δ.le
  have hceil : Real.log (2 / δ) / Real.log (4 / 3) ≤ (retryCount δ : ℝ) := Nat.le_ceil _
  have hkey : Real.log (2 / δ) ≤ (retryCount δ : ℝ) * Real.log (4 / 3) := by
    rwa [div_le_iff₀ hL] at hceil
  have hlog34 : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by
    rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  have hpow : (3 / 4 : ℝ) ^ retryCount δ
      = Real.exp ((retryCount δ : ℝ) * Real.log (3 / 4)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 3 / 4)]
  rw [hpow, hlog34]
  have hstep : (retryCount δ : ℝ) * -Real.log (4 / 3) ≤ -Real.log (2 / δ) := by
    nlinarith
  calc Real.exp ((retryCount δ : ℝ) * -Real.log (4 / 3))
      ≤ Real.exp (-Real.log (2 / δ)) := Real.exp_le_exp.2 hstep
    _ = δ / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 2 / δ)]
        field_simp

/-- **The repetition count is `Θ(log δ⁻¹)`.**  `retryCount δ ≤ 4⌈log(1/δ)⌉ + 5`.

No `log |U|` appears, which is the point recorded in the module docstring: the
source's `Θ(log(δ⁻¹|L_n(𝒯)|))` is sufficient but larger than necessary, because
the retry loop's perturbation is already multiplicative. -/
theorem retryCount_le {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    retryCount δ ≤ 4 * ⌈Real.log (1 / δ)⌉₊ + 5 := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hL : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := quarter_le_log_four_thirds
  have hL0 : (0 : ℝ) < Real.log (4 / 3) := lt_of_lt_of_le (by norm_num) hL
  have h2δ : (1 : ℝ) < 2 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hlog0 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg h2δ.le
  have hsplit : Real.log (2 / δ) = Real.log 2 + Real.log (1 / δ) := by
    rw [show (2 : ℝ) / δ = 2 * (1 / δ) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlogδ : Real.log (1 / δ) ≤ (⌈Real.log (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
  have hdiv : Real.log (2 / δ) / Real.log (4 / 3) ≤ 4 * Real.log (2 / δ) := by
    rw [div_le_iff₀ hL0]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.2 hL)]
  have hceil : ((retryCount δ : ℕ) : ℝ) < Real.log (2 / δ) / Real.log (4 / 3) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hB : Real.log (2 / δ) ≤ 1 + (⌈Real.log (1 / δ)⌉₊ : ℝ) := by rw [hsplit]; linarith
  have hbound : ((retryCount δ : ℕ) : ℝ) ≤ 4 * (⌈Real.log (1 / δ)⌉₊ : ℝ) + 5 := by
    linarith
  exact_mod_cast hbound

/-! ## Step 3 — the assembled sampler

The tolerance handed to the preprocessing step, the retry loop, and the mixture
with the (arbitrary) preprocessing-failure branch. -/

/-- **The preprocessing tolerance.**  `δ / (2(|g w| + 1))`, the calibration
`δ₀ = δ|U|⁻¹` of [ACJR21, `thm:samplemain`] with two pieces of slack: the factor `2`
splits the error budget with the retry loop, and the `+ 1` keeps `δ₀` positive on
an empty instance, where `IsFPAUS` asks a different question anyway. -/
noncomputable def preTol {Ω : Type u} (g : α → Finset Ω) (w : α) (δ : ℝ) : ℝ :=
  δ / (2 * ((g w).card + 1))

/-- **The assembled sampler.**  Run the preprocessing at tolerance `δ₀ = preTol`;
with probability `δ₀` it fails undetectably and the subsequent `retryCount δ`
attempts follow the arbitrary law `bad`, otherwise they follow `good`.

Writing the failure branch explicitly is forced by the absence of a computation
model: "the preprocessing fails with probability `δ₀` and thereafter the law is
unconstrained" *is* a two-point mixture, and there is nothing else it could
be. -/
noncomputable def retrySampler {Ω : Type u} (g : α → Finset Ω)
    (good bad : α → ℝ → PMF (Option Ω × ℕ)) : α → ℝ → PMF (Option Ω × ℕ) :=
  fun w δ => mixPMF (ENNReal.ofReal (preTol g w δ))
    (retryPMF (bad w (preTol g w δ)) (retryCount δ))
    (retryPMF (good w (preTol g w δ)) (retryCount δ))

/-- The preprocessing tolerance is a legal tolerance: `δ₀ ∈ (0,1)`. -/
theorem preTol_mem_Ioo {Ω : Type u} {g : α → Finset Ω} {w : α} {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1) : preTol g w δ ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hd : (0 : ℝ) < 2 * ((g w).card + 1) := by positivity
  have hc : (0 : ℝ) ≤ (g w).card := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · rw [preTol]; positivity
  · rw [preTol, div_lt_one hd]; linarith

/-- The calibration `δ₀ ≤ δ/(2|U|)` on a nonempty instance, which is what feeds
`between_of_abs_sub_le`. -/
theorem preTol_le {Ω : Type u} {g : α → Finset Ω} {w : α} {δ : ℝ} (hδ0 : 0 < δ)
    (hne : (g w).Nonempty) : preTol g w δ ≤ δ / (2 * (g w).card) := by
  have hc : (1 : ℝ) ≤ (g w).card := by exact_mod_cast Finset.card_pos.2 hne
  rw [preTol, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The cost of the assembled sampler: both branches of the mixture are retry
loops, so every run costs at most `retryCount δ` times the cost of one attempt. -/
theorem retrySampler_cost_le {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)} {c d : ℕ}
    (hcd : ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1,
      (∀ p ∈ (good w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d) ∧
      (∀ p ∈ (bad w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d))
    (w : α) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    ∀ p ∈ (retrySampler g good bad w δ).support,
      p.2 ≤ retryCount δ * (c * (size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1) ^ d) := by
  intro p hp
  obtain ⟨hg, hb⟩ := hcd w (preTol g w δ) (preTol_mem_Ioo hδ)
  rcases mem_support_mixPMF hp with h | h
  · exact retryPMF_cost_le _ hb _ p h
  · exact retryPMF_cost_le _ hg _ p h

/-- **The assembled sampler charges at least what one attempt charges.**

The mirror of `retrySampler_cost_le`, and the statement that distinguishes an
algorithm from the non-algorithm that records `0`: both branches of the mixture
are retry loops, `one_le_retryCount` says each of them runs at least one
attempt, and `retryPMF_cost_ge` says a loop that runs charges at least what its
attempt charges.

Note that the hypotheses are at `preTol g w δ`, not at `δ`: that is the
tolerance at which the assembly actually invokes `good` and `bad`, so this is
the weakest form that suffices and the one a caller can discharge. -/
theorem retrySampler_cost_ge {Ω : Type u} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)} {A : ℕ} (w : α) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1)
    (hg : ∀ p ∈ (good w (preTol g w δ)).support, A ≤ p.2)
    (hb : ∀ p ∈ (bad w (preTol g w δ)).support, A ≤ p.2) :
    ∀ p ∈ (retrySampler g good bad w δ).support, A ≤ p.2 := by
  intro p hp
  obtain ⟨k, hk⟩ : ∃ k, retryCount δ = k + 1 :=
    ⟨retryCount δ - 1, (Nat.succ_pred_eq_of_pos (one_le_retryCount hδ)).symm⟩
  rw [retrySampler, hk] at hp
  rcases mem_support_mixPMF hp with h | h
  · exact retryPMF_cost_ge _ hb k p h
  · exact retryPMF_cost_ge _ hg k p h

/-! ### The hypotheses of `thm:samplemain` -/

/-- **A sampler with the two defects of `thm:samplemain`.**

`good w δ₀` is the law of one attempt *given that the preprocessing succeeded*;
`bad w δ₀` is its law given that the preprocessing failed, and is completely
unconstrained apart from the empty-instance and cost clauses.

* `uniform` — conditioned on not returning `FAIL`, a good attempt is *exactly*
  uniform on `g w`.  This is `lem:sampmain` combined with Property 2, and it is
  an equality, not a window: all the approximation lives in the preprocessing.
* `fail_le` — a good attempt **on an instance with a solution** returns `FAIL`
  with probability at most `3/4` ([ACJR21], under its standing proviso
  `T(sⁱ) ≠ ∅`).  The source then repeats three times to
  reach `1/2`; that step is not needed here, `retryCount` being calibrated
  against `3/4` directly.  The `(g w).Nonempty` guard is not decoration: without
  it this clause and `empty` assert `1 ≤ 3/4` on an instance with no solutions,
  and the structure is unsatisfiable whenever `g` takes the value `∅`.
* `empty` — on an instance with no solutions *both* branches always return
  `FAIL`.  The source justifies this ([ACJR21, `thm:samplemain`]) by observing that
  membership in `L_n(𝒯)` is decidable in polynomial time, so a candidate output
  can always be checked before being returned — which is why the clause may be
  imposed on the failure branch too.
* `cost` — both branches run in time polynomial in the instance size and in
  `log(1/δ₀)`.  Note `log(1/δ₀)`, not `1/δ₀`: this is exactly what makes running
  the preprocessing at the exponentially small `δ₀ = δ·exp(-poly)` affordable. -/
structure PreprocessedSampler {Ω : Type u} (size : α → ℕ) (g : α → Finset Ω)
    (good bad : α → ℝ → PMF (Option Ω × ℕ)) : Prop where
  /-- Conditioned on success, a good attempt is exactly uniform on `g w`. -/
  uniform : ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty → ∀ x ∈ g w,
    outProbR (good w δ₀) {some x}
      = (1 - outProbR (good w δ₀) {none}) / (g w).card
  /-- A good attempt **on an instance with a solution** returns `FAIL` with
  probability at most `3/4` ([ACJR21], under its standing proviso
  `T(sⁱ) ≠ ∅`).  The `(g w).Nonempty` guard is what the
  source's proviso is; dropping it contradicts `empty`, which forces
  `Pr[FAIL] = 1` when `g w = ∅`. -/
  fail_le : ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty →
    outProbR (good w δ₀) {none} ≤ 3 / 4
  /-- On an instance with no solutions every attempt returns `FAIL`. -/
  empty : ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1, g w = ∅ →
    outProbR (good w δ₀) {none} = 1 ∧ outProbR (bad w δ₀) {none} = 1
  /-- Both branches run in time polynomial in `size w` and `log(1/δ₀)`. -/
  cost : ∃ c d : ℕ, ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1,
    (∀ p ∈ (good w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d) ∧
    (∀ p ∈ (bad w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d)

namespace PreprocessedSampler

variable {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
  {good bad : α → ℝ → PMF (Option Ω × ℕ)}

/-- **The retry loop, on a nonempty instance.**  After `k` attempts the good
branch returns each solution with probability exactly `(1 - f^k)/|g w|`, where
`f` is the per-attempt `FAIL` probability: the loop scales every solution's
probability by the same `1 - f^k`, so it is a *multiplicative*, not an additive,
perturbation. -/
theorem outProbR_retry_good (H : PreprocessedSampler size g good bad) (w : α)
    {δ₀ : ℝ} (hδ₀ : δ₀ ∈ Set.Ioo (0:ℝ) 1) (hne : (g w).Nonempty) (k : ℕ)
    {x : Ω} (hx : x ∈ g w) :
    outProbR (retryPMF (good w δ₀) k) {some x}
      = (1 - (outProbR (good w δ₀) {none}) ^ k) / (g w).card := by
  set f := outProbR (good w δ₀) {none} with hf
  have hgeom : (∑ i ∈ Finset.range k, f ^ i) * (1 - f) = 1 - f ^ k := by
    have h := geom_sum_mul f k
    have hneg : (∑ i ∈ Finset.range k, f ^ i) * (1 - f)
        = -((∑ i ∈ Finset.range k, f ^ i) * (f - 1)) := by ring
    rw [hneg, h]; ring
  rw [outProbR_retryPMF _ (by simp) k, H.uniform w δ₀ hδ₀ hne x hx, ← hf,
    div_eq_mul_inv, ← mul_assoc, hgeom, ← div_eq_mul_inv]

/-- **The additive error of the assembled sampler.**

Two contributions, both bounded by `δ/(2|U|)`: the undetectable preprocessing
failure (`abs_outProbR_mixPMF_sub_le`, calibrated by `preTol_le`) and the
exhaustion of the retry loop (`pow_retryCount_le`).  Their sum is the `δ/|U|`
that Step 1 converts into the multiplicative window. -/
theorem abs_outProbR_retrySampler_sub_le (H : PreprocessedSampler size g good bad)
    (w : α) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) (hne : (g w).Nonempty)
    {x : Ω} (hx : x ∈ g w) :
    |outProbR (retrySampler g good bad w δ) {some x} - 1 / (g w).card|
      ≤ δ / (g w).card := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hδ₀ : preTol g w δ ∈ Set.Ioo (0:ℝ) 1 := preTol_mem_Ioo ⟨hδ0, hδ1⟩
  have hc : (1 : ℝ) ≤ (g w).card := by exact_mod_cast Finset.card_pos.2 hne
  have hcpos : (0 : ℝ) < (g w).card := by linarith
  set f := outProbR (good w (preTol g w δ)) {none} with hf
  have hf0 : 0 ≤ f := outProbR_nonneg _ _
  have hf34 : f ≤ 3 / 4 := H.fail_le w (preTol g w δ) hδ₀ hne
  have hgood : outProbR (retryPMF (good w (preTol g w δ)) (retryCount δ)) {some x}
      = (1 - f ^ retryCount δ) / (g w).card :=
    H.outProbR_retry_good w hδ₀ hne _ hx
  have hfk : f ^ retryCount δ ≤ δ / 2 :=
    le_trans (pow_le_pow_left₀ hf0 hf34 _) (pow_retryCount_le ⟨hδ0, hδ1⟩)
  have hfk0 : 0 ≤ f ^ retryCount δ := pow_nonneg hf0 _
  have hretry : |outProbR (retryPMF (good w (preTol g w δ)) (retryCount δ)) {some x}
      - 1 / (g w).card| ≤ δ / (2 * (g w).card) := by
    have heq : (1 - f ^ retryCount δ) / ((g w).card : ℝ) - 1 / (g w).card
        = -(f ^ retryCount δ / (g w).card) := by field_simp
    rw [hgood, heq, abs_neg, abs_of_nonneg (div_nonneg hfk0 hcpos.le),
      div_le_div_iff₀ hcpos (by positivity)]
    calc f ^ retryCount δ * (2 * (g w).card)
        ≤ (δ / 2) * (2 * (g w).card) :=
          mul_le_mul_of_nonneg_right hfk (by positivity)
      _ = δ * (g w).card := by ring
  have hpre : preTol g w δ ≤ δ / (2 * (g w).card) := preTol_le hδ0 hne
  have hmix := abs_outProbR_mixPMF_sub_le (q := preTol g w δ) hδ₀.1.le hδ₀.2.le
    (retryPMF (bad w (preTol g w δ)) (retryCount δ))
    (retryPMF (good w (preTol g w δ)) (retryCount δ))
    {some x} (1 / (g w).card)
  have hsplit : δ / (2 * (g w).card) + δ / (2 * (g w).card) = δ / (g w).card := by
    field_simp; ring
  calc |outProbR (retrySampler g good bad w δ) {some x} - 1 / (g w).card|
      ≤ preTol g w δ
        + |outProbR (retryPMF (good w (preTol g w δ)) (retryCount δ)) {some x}
            - 1 / (g w).card| := hmix
    _ ≤ δ / (2 * (g w).card) + δ / (2 * (g w).card) := add_le_add hpre hretry
    _ = δ / (g w).card := hsplit

/-- **The empty instance.**  When there is nothing to sample every attempt of
both branches returns `FAIL`, hence so do all `k` of them, hence so does the
mixture: the assembled sampler outputs `none` with probability `1`, which is what
`IsFPAUS.empty` demands. -/
theorem outProbR_retrySampler_none (H : PreprocessedSampler size g good bad)
    (w : α) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) (hemp : g w = ∅) :
    outProbR (retrySampler g good bad w δ) {none} = 1 := by
  have hδ₀ : preTol g w δ ∈ Set.Ioo (0:ℝ) 1 := preTol_mem_Ioo hδ
  obtain ⟨hg, hb⟩ := H.empty w (preTol g w δ) hδ₀ hemp
  rw [retrySampler, outProbR_mixPMF hδ₀.1.le hδ₀.2.le,
    outProbR_retryPMF_none, outProbR_retryPMF_none, hg, hb]
  simp

end PreprocessedSampler

/-! ### The running-time bookkeeping

`log(1/δ₀) = log 2 + log(|g w| + 1) + log(1/δ)`, so the preprocessing's own
running time is polynomial in the instance size only when `log |g w|` is.  That
hypothesis is `log_card_poly` below and it is the one the source leaves
implicit. -/

/-- **The tolerance blow-up, in the units `polytime` counts in.**

`⌈log(1/δ₀)⌉ ≤ ⌈log(1/δ)⌉ + ⌈log(|g w| + 1)⌉ + 1`.  The `+ 1` absorbs
`log 2 ≤ 1`; the middle term is the one that needs `log_card_poly`. -/
theorem ceil_log_preTol_le {Ω : Type u} {g : α → Finset Ω} {w : α} {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    ⌈Real.log (1 / preTol g w δ)⌉₊
      ≤ ⌈Real.log (1 / δ)⌉₊ + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 1 := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hlog : Real.log (1 / preTol g w δ)
      = Real.log 2 + Real.log ((g w).card + 1 : ℝ) + Real.log (1 / δ) := by
    rw [preTol, one_div_div,
      show (2 * ((g w).card + 1) / δ : ℝ) = 2 * ((g w).card + 1) * (1 / δ) by ring,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  refine Nat.ceil_le.2 ?_
  rw [hlog]
  push_cast
  have h1 : Real.log ((g w).card + 1 : ℝ) ≤ (⌈Real.log ((g w).card + 1 : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : Real.log (1 / δ) ≤ (⌈Real.log (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- **The headline of Step 3.**

Given a `PreprocessedSampler` and the hypothesis that `log |g w|` is polynomially
bounded in the instance size, `retrySampler` is an FPAUS.

The three clauses come from the three steps: `uniform` from Step 1
(`outProbR_mem_Icc_of_additive`) applied to the two additive errors of
`abs_outProbR_retrySampler_sub_le`; `empty` from `outProbR_retrySampler_none`;
and `polytime` from `retrySampler_cost_le`, `retryCount_le` and
`ceil_log_preTol_le`.

**`log_card_poly` is a genuine hypothesis, and the source does not state it.**
The preprocessing is run at `δ₀ = δ/(2(|g w|+1))`, so its running time is
polynomial in `log(1/δ₀) = log(1/δ) + log|g w| + O(1)`.  Nothing forces
`log |g w|` to be polynomial in `size w` — for a general `g` it need not be —
and without it the assembled sampler is not polynomial-time.  In the source's
application it holds because `|L_n(𝒯)| ≤ exp(poly(n,m))`, which is the content of
"`δ₀ = δ exp(-poly(n,m))` does not affect the stated polynomial runtime"
([ACJR21, `thm:samplemain`]).  The clause is polynomial in `log(1/δ₀)`, never in
`1/δ₀`. -/
theorem PreprocessedSampler.isFPAUS {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)}
    (H : PreprocessedSampler size g good bad)
    (log_card_poly : PolyBounded size fun w => ⌈Real.log ((g w).card + 1 : ℝ)⌉₊) :
    IsFPAUS size g (retrySampler g good bad) where
  uniform := by
    intro w δ hδ hne x hx
    refine outProbR_mem_Icc_of_additive (le_refl _) ?_ x hx
    intro y hy
    exact H.abs_outProbR_retrySampler_sub_le w hδ hne hy
  empty := fun w δ hδ hemp => H.outProbR_retrySampler_none w hδ hemp
  polytime := by
    obtain ⟨c, d, hcd⟩ := H.cost
    obtain ⟨c', d', hc'⟩ := log_card_poly
    refine ⟨5 * (c * (c' + 2 + 2) ^ d), max (max d' 1) 1 * d + 1, ?_⟩
    intro w δ hδ p hp
    have hbase : size w + 1 ≤ (size w + 1) ^ (max d' 1) := by
      conv_lhs => rw [← pow_one (size w + 1)]
      exact Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hpow : (size w + 1) ^ d' ≤ (size w + 1) ^ (max d' 1) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hLP : ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ ≤ c' * (size w + 1) ^ (max d' 1) :=
      le_trans (hc' w) (Nat.mul_le_mul (le_refl c') hpow)
    have hR : size w + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 2
        ≤ (c' + 2) * (size w + 1) ^ (max d' 1) := by
      have h2 : size w + 2 ≤ 2 * (size w + 1) ^ (max d' 1) := by
        calc size w + 2 ≤ (size w + 1) + (size w + 1) := by omega
          _ ≤ (size w + 1) ^ (max d' 1) + (size w + 1) ^ (max d' 1) :=
              Nat.add_le_add hbase hbase
          _ = 2 * (size w + 1) ^ (max d' 1) := by ring
      calc size w + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 2
          = ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + (size w + 2) := by ring
        _ ≤ c' * (size w + 1) ^ (max d' 1) + 2 * (size w + 1) ^ (max d' 1) :=
            Nat.add_le_add hLP h2
        _ = (c' + 2) * (size w + 1) ^ (max d' 1) := by ring
    have hstep1 : size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1
        ≤ (c' + 2) * (size w + 1) ^ (max d' 1) + ⌈Real.log (1 / δ)⌉₊ + 1 := by
      have h1 : ⌈Real.log (1 / preTol g w δ)⌉₊
          ≤ ⌈Real.log (1 / δ)⌉₊ + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 1 :=
        ceil_log_preTol_le hδ
      calc size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1
          ≤ size w + (⌈Real.log (1 / δ)⌉₊ + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 1) + 1 := by
            omega
        _ = (size w + ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ + 2) + ⌈Real.log (1 / δ)⌉₊ := by ring
        _ ≤ (c' + 2) * (size w + 1) ^ (max d' 1) + ⌈Real.log (1 / δ)⌉₊ :=
            Nat.add_le_add_right hR _
        _ ≤ (c' + 2) * (size w + 1) ^ (max d' 1) + ⌈Real.log (1 / δ)⌉₊ + 1 := Nat.le_succ _
    have hattempt : c * (size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1) ^ d
        ≤ c * (c' + 2 + 2) ^ d * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ (max (max d' 1) 1 * d) :=
      le_trans (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left hstep1 d))
        (poly_comp c (c' + 2) d (max d' 1) (size w) ⌈Real.log (1 / δ)⌉₊)
    have hcost := retrySampler_cost_le hcd w hδ p hp
    have hk : retryCount δ ≤ 5 * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) := by
      have := retryCount_le hδ
      omega
    calc p.2 ≤ retryCount δ * (c * (size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1) ^ d) := hcost
      _ ≤ (5 * (size w + ⌈Real.log (1 / δ)⌉₊ + 1))
            * (c * (c' + 2 + 2) ^ d
              * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ (max (max d' 1) 1 * d)) :=
          Nat.mul_le_mul hk hattempt
      _ = 5 * (c * (c' + 2 + 2) ^ d)
            * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ (max (max d' 1) 1 * d + 1) := by
          rw [pow_succ]; ring

/-- **Transporting `IsFPAUS` along a pointwise equality of algorithms.**

`IsFPAUS` only ever looks at `A w δ` for `δ ∈ (0,1)`, so an algorithm that agrees
with an FPAUS on that range is one too.  This is what lets a caller present the
sampler of `PreprocessedSampler.isFPAUS` in whatever form its own development
produced, rather than as the literal `retrySampler` term. -/
theorem IsFPAUS.of_eq {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
    {A A' : α → ℝ → PMF (Option Ω × ℕ)} (h : IsFPAUS size g A)
    (heq : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, A w δ = A' w δ) :
    IsFPAUS size g A' where
  uniform := fun w δ hδ hne x hx => by rw [← heq w δ hδ]; exact h.uniform w δ hδ hne x hx
  empty := fun w δ hδ hemp => by rw [← heq w δ hδ]; exact h.empty w δ hδ hemp
  polytime := by
    obtain ⟨c, d, hcd⟩ := h.polytime
    exact ⟨c, d, fun w δ hδ p hp => hcd w δ hδ p (by rw [heq w δ hδ]; exact hp)⟩

end Arlib.Approximation

