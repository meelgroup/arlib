/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Sampling
import Arlib.Approximation.Pinned

/-!
# `thm:samplemain`'s assembly, with the constants surviving it

`thm:samplemain` is the label the sampling theorem carries in [ACJR21]
(Arenas–Croquevielle–Jayaram–Riveros; the full reference, and the reason
statements of that work are cited by label rather than by page, are in
`Arlib/Approximation/Sampling.lean`).

`Approximation/Sampling.lean` turns a `PreprocessedSampler` into an `IsFPAUS`.
Its running-time clause is `IsFPAUS.polytime`, an `∃ c d`, and the two numbers
it quantifies away are *computed* in the proof: they are

    5 · (c · (c' + 4) ^ d)      and      max d' 1 · d + 1,

where `(c, d)` is the pinned form of `PreprocessedSampler.cost` and `(c', d')`
the pinned form of the `log_card_poly` side condition.  This module states them.

## Why this is not cosmetic

`Approximation/Pinned.lean` exists because `PolyBounded` and the two `polytime`
clauses are existentials that a zero-cost non-algorithm satisfies, so a
development that has actually computed an exponent has no way to say so.  The
`Pinned` module supplies the vocabulary and the *transfer* theorems
(`IsFPAUS.comp_bijection_pinned_on`), but it does not supply the **producer**:
before this module, the only route from a `PreprocessedSampler` to an `IsFPAUS`
opened the existential at `PreprocessedSampler.cost` and again at
`IsFPAUS.polytime`, so no caller of `PreprocessedSampler.isFPAUS` could feed
`comp_bijection_pinned_on`.  A caller therefore had to prove the accuracy of one
sampler and the running time of another, and had no lemma with which to notice.

`PreprocessedSampler.isFPAUS_pinned` closes that: it returns the **conjunction**
of `PreprocessedSampler.isFPAUS`'s own conclusion — proved by calling it, so the
two cannot disagree — with an `IsFPAUS.PinnedTime` about the *same* `retrySampler`
term.

## What is **not** repaired

Nothing here makes an upper bound into evidence that work was done.
`IsFPAUS.pinnedTime_of_cost_zero` still applies, and worse:
`retrySampler_not_charges_of_bad_free` shows that `IsFPAUS.Charges` is
**refutable** for `retrySampler g good bad` whenever the preprocessing-failure
branch `bad` is the zero-cost constant `FAIL` — which is a legal `bad`, since
`PreprocessedSampler` constrains that branch only through `empty` and `cost`.
So on the cheapest legal instantiation of `thm:samplemain`'s own hypotheses the
assembled sampler provably has cost-`0` runs, and the sandwich of
`Approximation/Pinned.lean` cannot be closed at this level at all.  What *can*
close it is a hop that adds a positive cost, which is why
`IsFPAUS.Charges.map_add_of_cost_pos` is here beside it: after a reduction that
charges its own construction, `Charges` holds for the composite even though it
fails for the sampler being composed.

## Main results

* `PinnedAttemptCost` — `PreprocessedSampler.cost` with `∃ c d` removed, and
  `preprocessedSampler_cost_iff` saying the field is exactly its existential
  closure.
* `retrySampler_pinnedTime` — the assembly's running time, at
  `retryAssemblyConst`/`retryAssemblyExp`.
* `PreprocessedSampler.isFPAUS_pinned` — the conjunction.
* `PinnedBounded.comp` — composing a pinned bound with an outer polynomial
  without a `max` appearing, the pinned companion of the `PolyBounded`
  transitivity every size-blow-up chain uses.
* `IsFPAUS.Charges.map_add_of_cost_pos` — `Charges` from the reduction's own
  charge alone, with nothing assumed about the algorithm being composed.
* `retrySampler_not_charges_of_bad_free` — and the refutation that makes the
  previous lemma necessary rather than convenient.
-/

universe u v

namespace Arlib.Approximation

open scoped ENNReal

variable {α : Type*}

/-! ## The cost field, unquantified -/

/-- **`PreprocessedSampler.cost` with the `∃ c d` removed.**

Both branches of one attempt, at the preprocessing tolerance `δ₀`, are bounded by
`c · (‖w‖ + ⌈log(1/δ₀)⌉ + 1) ^ d`.  Stated as a predicate rather than as a field
so that it attaches to an existing `PreprocessedSampler` without changing that
structure's type — the same discipline `IsFPAUS.PinnedTime` follows. -/
def PinnedAttemptCost {Ω : Type u} (size : α → ℕ)
    (good bad : α → ℝ → PMF (Option Ω × ℕ)) (c d : ℕ) : Prop :=
  ∀ w, ∀ δ₀ ∈ Set.Ioo (0:ℝ) 1,
    (∀ p ∈ (good w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d) ∧
    (∀ p ∈ (bad w δ₀).support, p.2 ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d)

/-- **What the structure gives back**: some pair, and no more.

`PreprocessedSampler.cost` is the existential closure of `PinnedAttemptCost` on
the nose, so this is the exact sense in which a caller holding only a
`PreprocessedSampler` holds no number.  The mirror of
`IsFPAUS.exists_pinnedTime`, one rung further up the chain, and the reason the
number has to be supplied as a *hypothesis* below rather than recovered. -/
theorem PreprocessedSampler.exists_pinnedAttemptCost {Ω : Type u} {size : α → ℕ}
    {g : α → Finset Ω} {good bad : α → ℝ → PMF (Option Ω × ℕ)}
    (H : PreprocessedSampler size g good bad) :
    ∃ c d : ℕ, PinnedAttemptCost size good bad c d := H.cost

/-- Weakening a pinned attempt bound, so that two of them can be brought to a
common pair before being used together. -/
theorem PinnedAttemptCost.weaken {Ω : Type u} {size : α → ℕ}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)} {c d c' d' : ℕ}
    (h : PinnedAttemptCost size good bad c d) (hc : c ≤ c') (hd : d ≤ d') :
    PinnedAttemptCost size good bad c' d' := by
  intro w δ₀ hδ₀
  obtain ⟨hg, hb⟩ := h w δ₀ hδ₀
  have key : ∀ n : ℕ, n ≤ c * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d →
      n ≤ c' * (size w + ⌈Real.log (1/δ₀)⌉₊ + 1) ^ d' := fun n hn =>
    hn.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd))
  exact ⟨fun p hp => key _ (hg p hp), fun p hp => key _ (hb p hp)⟩

/-! ## The constants the assembly reaches -/

/-- **The constant of `retrySampler`**: `5 · c · (c' + 4) ^ d`.

`5` is the retry loop's `retryCount δ ≤ 5(‖w‖ + ⌈log(1/δ)⌉ + 1)`
(`retryCount_le`); `(c' + 4) ^ d` is the tolerance composition
`δ₀ = δ/(2(|g w| + 1))` seen through `ceil_log_preTol_le` and the pinned
`log_card` bound, raised to the attempt's own degree. -/
def retryAssemblyConst (c c' d : ℕ) : ℕ := 5 * (c * (c' + 4) ^ d)

/-- **The exponent of `retrySampler`**: `max d' 1 · d + 1`.

`max d' 1 · d` is the attempt's degree seen through the tolerance composition —
this is where the `log |g w|` bound's degree *multiplies* rather than adds — and
the `+ 1` is the retry loop's linear factor. -/
def retryAssemblyExp (d d' : ℕ) : ℕ := max d' 1 * d + 1

/-- **The running time of `thm:samplemain`'s assembled sampler, with both
constants written down.**

This is the `polytime` field of `PreprocessedSampler.isFPAUS`, verbatim, with the
two `obtain`s at its head replaced by hypotheses.  Nothing about the bound
changes; what changes is that the caller keeps the numbers.

The `log_card` hypothesis is the one `Sampling.lean`'s docstring flags as the
source's unstated one: the preprocessing runs at `δ₀ = δ/(2(|g w|+1))`, so its
own time is polynomial in `log(1/δ₀) = log(1/δ) + log|g w| + O(1)`, and nothing
forces `log |g w|` to be polynomial in `size w`. -/
theorem retrySampler_pinnedTime {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)} {c d c' d' : ℕ}
    (hcost : PinnedAttemptCost size good bad c d)
    (hlog : PinnedBounded size (fun w => ⌈Real.log ((g w).card + 1 : ℝ)⌉₊) c' d') :
    IsFPAUS.PinnedTime size (retrySampler g good bad)
      (retryAssemblyConst c c' d) (retryAssemblyExp d d') := by
  intro w δ hδ p hp
  have hbase : size w + 1 ≤ (size w + 1) ^ (max d' 1) := by
    conv_lhs => rw [← pow_one (size w + 1)]
    exact Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hpow : (size w + 1) ^ d' ≤ (size w + 1) ^ (max d' 1) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hLP : ⌈Real.log ((g w).card + 1 : ℝ)⌉₊ ≤ c' * (size w + 1) ^ (max d' 1) :=
    le_trans (hlog w) (Nat.mul_le_mul (le_refl c') hpow)
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
  have hcost' := retrySampler_cost_le (c := c) (d := d) hcost w hδ p hp
  have hk : retryCount δ ≤ 5 * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) := by
    have := retryCount_le hδ
    omega
  have hmax : max (max d' 1) 1 = max d' 1 := max_eq_left (le_max_right _ _)
  rw [retryAssemblyConst, retryAssemblyExp]
  calc p.2 ≤ retryCount δ * (c * (size w + ⌈Real.log (1 / preTol g w δ)⌉₊ + 1) ^ d) := hcost'
    _ ≤ (5 * (size w + ⌈Real.log (1 / δ)⌉₊ + 1))
          * (c * (c' + 2 + 2) ^ d
            * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ (max (max d' 1) 1 * d)) :=
        Nat.mul_le_mul hk hattempt
    _ = 5 * (c * (c' + 4) ^ d)
          * (size w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ (max d' 1 * d + 1) := by
        rw [hmax, pow_succ]; ring

/-- **`PreprocessedSampler.isFPAUS`, with the exponent surviving.**

The first component is `PreprocessedSampler.isFPAUS` itself — called, not
re-proved, so the accuracy conclusion here is *the same proposition* that
development already establishes — and the second is `retrySampler_pinnedTime`
about the same `retrySampler g good bad` term.

This is the lemma a caller needs in order to feed
`IsFPAUS.comp_bijection_pinned_on`: without it the sampler whose accuracy is
known and the sampler whose running time is known are related only by an
existential that has already been opened twice. -/
theorem PreprocessedSampler.isFPAUS_pinned {Ω : Type u} {size : α → ℕ} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)} {c d c' d' : ℕ}
    (H : PreprocessedSampler size g good bad)
    (hcost : PinnedAttemptCost size good bad c d)
    (hlog : PinnedBounded size (fun w => ⌈Real.log ((g w).card + 1 : ℝ)⌉₊) c' d') :
    IsFPAUS size g (retrySampler g good bad)
      ∧ IsFPAUS.PinnedTime size (retrySampler g good bad)
          (retryAssemblyConst c c' d) (retryAssemblyExp d d') :=
  ⟨H.isFPAUS hlog.polyBounded, retrySampler_pinnedTime hcost hlog⟩

/-! ## Composing a pinned bound with an outer polynomial

A size blow-up that factors through an intermediate measure — "the reduction's
automaton is polynomial in the input, and the *preprocessed* automaton is
polynomial in that" — is the shape every multi-stage reduction produces.  The
`PolyBounded` version quantifies both pairs away; this one does not, and needs no
`max` because the outer degree is assumed positive, which it always is in
practice. -/

/-- **`PinnedBounded`, composed.**  If `f` is pinned at `(c', e')` and
`g w ≤ c·(f w + 1)^e`, then `g` is pinned at `(c·(c'+1)^e, e'·e)`.

The exponents **multiply**.  That is the whole content: a two-stage size blow-up
costs a product, not a sum, and any development that routes a running-time bound
through an intermediate instance pays it.  Unlike the `PolyBounded` version,
which has to write `max e' 1` because the intermediate degree is unknown, no
`max` appears — the multiplication is correct at `e' = 0` too, where it says a
bounded intermediate contributes nothing. -/
theorem PinnedBounded.comp {sA f g : α → ℕ} {c e c' e' : ℕ}
    (hf : PinnedBounded sA f c' e')
    (hg : ∀ w, g w ≤ c * (f w + 1) ^ e) :
    PinnedBounded sA g (c * (c' + 1) ^ e) (e' * e) := by
  intro w
  have hb : 1 ≤ (sA w + 1) ^ e' := Nat.one_le_pow _ _ (by omega)
  have h1 : c' * (sA w + 1) ^ e' + 1 ≤ (c' + 1) * (sA w + 1) ^ e' := by nlinarith
  calc g w ≤ c * (f w + 1) ^ e := hg w
    _ ≤ c * (c' * (sA w + 1) ^ e' + 1) ^ e :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.succ_le_succ (hf w)) e)
    _ ≤ c * ((c' + 1) * (sA w + 1) ^ e') ^ e :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left h1 e)
    _ = c * (c' + 1) ^ e * (sA w + 1) ^ (e' * e) := by
        rw [mul_pow, ← pow_mul, mul_assoc]

/-- **A pinned sampling time bound transports along a linearly related size
measure**, at the *same* exponent.

If `s w + 1 ≤ m·(s' w + 1)` then a bound in `s` becomes a bound in `s'` with the
factor absorbed as `c ↦ c·mᵉ`.  The exponent is untouched, which is the point: a
normalisation that only inflates the instance by a constant factor is free in the
degree, and stating that requires the pinned form — through `PolyBounded` the
degree is quantified away and there is nothing to compare.

`δ` is not rescaled anywhere, so the `⌈log(1/δ)⌉` term rides along; the counting
analogue would have to say the same of `⌈ε⁻¹⌉`. -/
theorem IsFPAUS.PinnedTime.of_size_le {Ω : Type v} {s s' : α → ℕ}
    {A : α → ℝ → PMF (Option Ω × ℕ)} {c e m : ℕ}
    (hm : 1 ≤ m) (hle : ∀ w, s w + 1 ≤ m * (s' w + 1))
    (h : IsFPAUS.PinnedTime s A c e) :
    IsFPAUS.PinnedTime s' A (c * m ^ e) e := by
  intro w δ hδ p hp
  refine (h w δ hδ p hp).trans ?_
  have hb : s w + ⌈Real.log (1 / δ)⌉₊ + 1 ≤ m * (s' w + ⌈Real.log (1 / δ)⌉₊ + 1) := by
    have h1 := hle w
    have h2 : ⌈Real.log (1 / δ)⌉₊ ≤ m * ⌈Real.log (1 / δ)⌉₊ := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : m * (s' w + ⌈Real.log (1 / δ)⌉₊ + 1)
        = m * (s' w + 1) + m * ⌈Real.log (1 / δ)⌉₊ := by ring
    omega
  calc c * (s w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ e
      ≤ c * (m * (s' w + ⌈Real.log (1 / δ)⌉₊ + 1)) ^ e :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left hb e)
    _ = c * m ^ e * (s' w + ⌈Real.log (1 / δ)⌉₊ + 1) ^ e := by rw [Nat.mul_pow]; ring

/-! ## `Charges`, and why it has to come from somewhere else -/

/-- **`Charges` from the reduction's own charge, with nothing assumed about the
algorithm being composed.**

`IsFPAUS.Charges.map_add` asks that `B` itself charge on every run.  That is the
wrong hypothesis whenever `B` is a `retrySampler` whose failure branch is free —
see `retrySampler_not_charges_of_bad_free` — and it is not needed: the composed
algorithm adds `cost w` unconditionally, so `0 < cost w` alone suffices. -/
theorem IsFPAUS.Charges.map_add_of_cost_pos {Ω₁ : Type v} {Ω₂ : Type v} {β : Type*}
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} {hm : α → β} {cost : α → ℕ}
    (dec : α → Option Ω₂ → Option Ω₁) (hcost : ∀ w, 0 < cost w) :
    IsFPAUS.Charges
      (fun w δ => (B (hm w) δ).map (fun p => (dec w p.1, p.2 + cost w))) := by
  intro w δ _ p hp
  obtain ⟨q, _, rfl⟩ := mem_support_map hp
  show 0 < q.2 + cost w
  have := hcost w
  omega

/-- The zero-cost constant `FAIL` is a fixed point of the retry loop. -/
theorem retryPMF_pure_none_zero {Ω : Type u} :
    ∀ k : ℕ, retryPMF (PMF.pure ((none : Option Ω), 0)) k = PMF.pure (none, 0) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [retryPMF, PMF.pure_bind]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, ih, Nat.zero_add]
    exact PMF.map_id _

/-- A run of the left branch of a mixture is a run of the mixture, provided the
mixing weight is positive.  The companion of `mem_support_mixPMF`, which only
goes the other way. -/
theorem mem_support_mixPMF_left {β : Type u} {q : ℝ≥0∞} {ν μ : PMF β} {x : β}
    (hq : q ≠ 0) (hx : x ∈ ν.support) : x ∈ (mixPMF q ν μ).support := by
  rw [mixPMF, PMF.mem_support_bind_iff]
  refine ⟨true, ?_, hx⟩
  have hmin : min q 1 ≠ 0 := by
    rcases le_total q 1 with h | h
    · rwa [min_eq_left h]
    · rw [min_eq_right h]; exact one_ne_zero
  simpa using hmin

/-- **`IsFPAUS.Charges` is refutable for `thm:samplemain`'s assembly.**

`PreprocessedSampler` constrains the preprocessing-failure branch `bad` only
through `empty` and `cost`, so the zero-cost constant `FAIL` is a legal `bad` —
and it is the cheapest one, hence the one a satisfiability certificate will pick.
With it, the mixture's failure branch contributes the run `(FAIL, 0)` at every
instance and every tolerance, and `Charges` fails outright.

Note what this is *not*: it is not a statement about `good`, and not about any
particular `good`.  It says that the assembly's cost sandwich cannot be closed at
this level whatever the attempt costs, because the assembly is a mixture with a
free branch.  A caller wanting `Charges` must get it from a later hop that
charges unconditionally — `IsFPAUS.Charges.map_add_of_cost_pos`. -/
theorem retrySampler_not_charges_of_bad_free {Ω : Type u} {g : α → Finset Ω}
    {good bad : α → ℝ → PMF (Option Ω × ℕ)}
    (hbad : ∀ w δ₀, bad w δ₀ = PMF.pure (none, 0)) (w : α) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    ¬ IsFPAUS.Charges (retrySampler g good bad) := by
  intro hC
  have hmem : ((none : Option Ω), 0) ∈ (retrySampler g good bad w δ).support := by
    refine mem_support_mixPMF_left ?_ ?_
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact (preTol_mem_Ioo (g := g) (w := w) hδ).1
    · rw [hbad, retryPMF_pure_none_zero]
      simp
  exact absurd (hC w δ hδ _ hmem) (by simp)

end Arlib.Approximation
