/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.CondVariational

/-!
# The conditional variational bound with an exceptional set

`CondVariational.lean` ends with `condI_le_log_of_ratio_le`: if the conditional
law of one answer is dominated by `r` times a reference kernel,

    `P_{Z | X = a, W = w}(b) ≤ r * Q w b`   for **every** letter `b`,

then `I(X ; Z | W) ≤ log r`. That shape is too rigid for the query lower bounds
it was written for. A typical argument splits the alphabet into regimes: on some
letters the likelihood ratio really is bounded by `r`, but on a residual set of
letters the ratio is *unbounded* — there is simply no `r` that works — and what
one controls instead is the total contribution of those letters to the KL sum,
which is a directly estimated, very small additive quantity.

This file relaxes the hypothesis exactly that far. Fix a "good" set `G` of
letters. Require the ratio bound only on `G`, and require, in place of a ratio
bound off `G`, an explicit bound `ε` on the residual KL mass

    `∑_{b ∉ G} p b * log (p b / q b) ≤ ε`.

The conclusion degrades by exactly the same additive `ε`:

    `KL(p ‖ q) ≤ log r + ε`   and   `I(X ; Z | W) ≤ log r + ε`.

In the conditional statement the good set is allowed to depend on the level `a`
*and* the prefix `w`, which it must: which regime a letter falls in is a function
of both.

## Main results

* `Arlib.InformationTheory.KLdist_le_log_add_of_ratio_le_on` — the KL lemma: a
  ratio bound on `G` plus an additive bound on the residual KL mass gives
  `KL(p ‖ q) ≤ log r + ε`.
* `Arlib.InformationTheory.condI_le_log_add_of_ratio_le_on` — the conditional
  corollary, obtained from `condI_le_of_KL_le` exactly as
  `condI_le_log_of_ratio_le` is.
* `Arlib.InformationTheory.condI_le_log_of_ratio_le'` — the sanity check: taking
  `G = univ` and `ε = 0` recovers `condI_le_log_of_ratio_le` verbatim, so nothing
  was lost in the relaxation.
* `Arlib.InformationTheory.KLdist_le_log_add_of_ratio_le_on_of_mass_le` and
  `Arlib.InformationTheory.condI_le_log_add_of_ratio_le_on_of_mass_le` — a
  convenience form in which the residual hypothesis is replaced by the two facts
  that are usually what one actually has: the *reference* law is bounded below by
  `m > 0` on the exceptional letters, and the *true* law puts total mass at most
  `δ` on them. The additive error is then `δ * log (1 / m)`.

## Relation to `condI_le_log_of_ratio_le`

`condI_le_log_add_of_ratio_le_on` is strictly stronger: `condI_le_log_of_ratio_le'`
below derives the old statement from the new one by instantiating `G := univ` and
`ε := 0`, and the private lemma
`condI_le_log_of_ratio_le_eq_condI_le_log_of_ratio_le'` certifies that the
derived statement is *the same statement* — the two have identical types, so no
hypothesis was silently added, dropped or reordered in the generalisation.
Nothing in `CondVariational.lean` is modified; this file only adds.

## Implementation notes

The only real content is the KL lemma, and it is a two-line split once the
degenerate letters are understood.

* On `G`, the termwise bound `p b * log (p b / q b) ≤ p b * log r` is
  `mul_log_div_le_mul_log_of_le`. It needs **no** absolute-continuity hypothesis:
  if `p b = 0` both sides are `0` by `Real.log 0 = 0` and `x / 0 = 0`, and if
  `p b > 0` then `q b > 0` is *forced* by `p b ≤ r * q b` together with
  `0 ≤ q b`, so `Real.log_le_log` applies with no side condition. This is why the
  statement carries no hypothesis of the form `∀ b, p b ≠ 0 → q b ≠ 0`: on the
  good letters absolute continuity is a consequence, and on the bad letters the
  hypothesis `hbad` is about the KL mass directly, so a `q b = 0` letter with
  `p b ≠ 0` is not excluded — it simply makes `hbad` unsatisfiable unless `p b`
  is `0` too, since `p b * log (p b / 0) = p b * log 0 = 0`. (Mathlib's junk
  values are load-bearing in the *permissive* direction here.)
* Summing the good part gives `(∑_{b ∈ G} p b) * log r ≤ log r`, using
  `0 ≤ log r` from `1 ≤ r` and `∑_{b ∈ G} p b ≤ ∑_b p b = 1`.
* The two pieces are recombined with `Finset.sum_sdiff` over `G ⊆ univ`.

Only nonnegativity of `q` is used, never `∑ q = 1`; the `IsProbDist q` form is
kept in the headline statements because that is what the conditional corollary
supplies. The primed variants take the weaker hypothesis.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

variable {α β γ : Type}

/-! ### Termwise bounds -/

/-- **The termwise ratio bound.** If `p ≤ r * q` at a point, with `q` nonnegative
and `r` positive, then `p * log (p / q) ≤ p * log r` there.

No absolute-continuity hypothesis is needed. If `p = 0` both sides vanish
(`Real.log 0 = 0`, `x / 0 = 0`); if `p > 0` then `q > 0` is forced by the
hypothesis, and the bound is monotonicity of `Real.log`. -/
private theorem mul_log_div_le_mul_log_of_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 < r) (h : p ≤ r * q) : p * Real.log (p / q) ≤ p * Real.log r := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · rw [← hp0]; simp
  · have hqb : 0 < q := by
      rcases eq_or_lt_of_le hq with h0 | h0
      · exact absurd h (by rw [← h0, mul_zero]; exact not_le.mpr hp0)
      · exact h0
    have hdiv : p / q ≤ r := div_le_of_le_mul₀ hq (le_of_lt hr) h
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hp0 hqb) hdiv) (le_of_lt hp0)

/-- **The termwise bound on an exceptional letter.** If the reference law is
bounded below by `m > 0` and the true law is bounded above by `1`, then
`p * log (p / q) ≤ p * log (1 / m)`.

This is the estimate that replaces a ratio bound where none exists: it costs
`log (1 / m)` per unit of exceptional mass, which is useful precisely when that
mass is tiny. -/
private theorem mul_log_div_le_mul_log_one_div {p q m : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hm : 0 < m) (hq : m ≤ q) :
    p * Real.log (p / q) ≤ p * Real.log (1 / m) := by
  have hqpos : 0 < q := lt_of_lt_of_le hm hq
  rcases eq_or_lt_of_le hp0 with hz | hz
  · rw [← hz]; simp
  · have hdiv : p / q ≤ 1 / m := div_le_div₀ (by norm_num) hp1 hm hq
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hz hqpos) hdiv) hp0

/-! ### The good part of the sum -/

/-- **The good part of a KL sum.** If `p b ≤ r * q b` on a set `G`, with `r ≥ 1`,
then the part of the KL sum indexed by `G` is at most `log r`.

The two ingredients are the termwise bound and `∑_{b ∈ G} p b ≤ ∑_b p b = 1`;
`0 ≤ log r` is what lets the second be used as a bound on a coefficient. -/
private theorem sum_mul_log_div_le_log_of_ratio_le_on [Fintype β] {p q : β → ℝ}
    (hp : IsProbDist p) (hq : ∀ b, 0 ≤ q b) (G : Finset β) {r : ℝ} (hr : 1 ≤ r)
    (hgood : ∀ b ∈ G, p b ≤ r * q b) :
    ∑ b ∈ G, p b * Real.log (p b / q b) ≤ Real.log r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hmass : ∑ b ∈ G, p b ≤ 1 := by
    calc ∑ b ∈ G, p b ≤ ∑ b, p b :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
            fun b _ _ => hp.nonneg b
      _ = 1 := hp.sum_eq_one
  calc ∑ b ∈ G, p b * Real.log (p b / q b)
      ≤ ∑ b ∈ G, p b * Real.log r :=
        Finset.sum_le_sum fun b hb =>
          mul_log_div_le_mul_log_of_le (hp.nonneg b) (hq b) hr0 (hgood b hb)
    _ = (∑ b ∈ G, p b) * Real.log r := by rw [Finset.sum_mul]
    _ ≤ Real.log r := mul_le_of_le_one_left hlog hmass

/-! ### The KL lemma -/

/-- **The KL divergence under a ratio bound on a subset, with an additive error.**
If `p b ≤ r * q b` for every `b` in a set `G` (with `r ≥ 1`), and the remaining
letters contribute at most `ε` to the KL sum, then `KL(p ‖ q) ≤ log r + ε`.

This is the version of `KLdist_le_log_of_pointwise` that a three-regime argument
can actually supply: it does not ask for a likelihood-ratio bound off `G`, where
typically none exists, only for a bound on that region's contribution.

Only nonnegativity of `q` is used, hence the hypothesis `hq : ∀ b, 0 ≤ q b`. No
absolute-continuity hypothesis appears: see the module docstring. -/
theorem KLdist_le_log_add_of_ratio_le_on' [Fintype β] [DecidableEq β] {p q : β → ℝ}
    (hp : IsProbDist p) (hq : ∀ b, 0 ≤ q b) (G : Finset β) {r ε : ℝ} (hr : 1 ≤ r)
    (hgood : ∀ b ∈ G, p b ≤ r * q b)
    (hbad : ∑ b ∈ Finset.univ \ G, p b * Real.log (p b / q b) ≤ ε) :
    KLdist p q ≤ Real.log r + ε := by
  have hsplit : KLdist p q
      = ∑ b ∈ Finset.univ \ G, p b * Real.log (p b / q b)
        + ∑ b ∈ G, p b * Real.log (p b / q b) :=
    (Finset.sum_sdiff (Finset.subset_univ G)).symm
  have hgoodsum : ∑ b ∈ G, p b * Real.log (p b / q b) ≤ Real.log r :=
    sum_mul_log_div_le_log_of_ratio_le_on hp hq G hr hgood
  rw [hsplit]
  linarith

/-- **The KL divergence under a ratio bound on a subset, with an additive error**,
stated with `q` a probability distribution. This is the form the conditional
corollary consumes; the substance is `KLdist_le_log_add_of_ratio_le_on'`, which
needs only `0 ≤ q`. -/
theorem KLdist_le_log_add_of_ratio_le_on [Fintype β] [DecidableEq β] {p q : β → ℝ}
    (hp : IsProbDist p) (hq : IsProbDist q) (G : Finset β) {r ε : ℝ} (hr : 1 ≤ r)
    (hgood : ∀ b ∈ G, p b ≤ r * q b)
    (hbad : ∑ b ∈ Finset.univ \ G, p b * Real.log (p b / q b) ≤ ε) :
    KLdist p q ≤ Real.log r + ε :=
  KLdist_le_log_add_of_ratio_le_on' hp hq.nonneg G hr hgood hbad

/-! ### The conditional bound -/

/-- **The conditional variational bound with an exceptional set.** If, for every
level `a` and prefix `w`, the conditional law of the answer is dominated by
`r * Q w b` on a set `G a w` of letters, and the letters outside `G a w`
contribute at most `ε` to that cell's KL sum, then

    `I(X ; Z | W) ≤ log r + ε`.

This is `condI_le_log_of_ratio_le` with the pointwise hypothesis weakened to a
pointwise hypothesis *on a subset* plus an additive account of the rest. The good
set may depend on both `a` and `w`, as it must: the regime a letter falls in
depends on the hidden level and on the prefix of answers already seen.

The absolute-continuity side condition `hQ0` is unchanged — it is the hypothesis
of `condI_le_of_KL_le`, about the *prefix-conditional* law, and has nothing to do
with the exceptional set. -/
theorem condI_le_log_add_of_ratio_le_on {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ)
    (hQ : ∀ w, IsProbDist (Q w))
    (hQ0 : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0)
    (G : α → γ → Finset β) {r ε : ℝ} (hr : 1 ≤ r)
    (hgood : ∀ a w, ∀ b ∈ G a w, condDist P Z (pair X W) (a, w) b ≤ r * Q w b)
    (hbad : ∀ a w, ∑ b ∈ Finset.univ \ G a w,
        condDist P Z (pair X W) (a, w) b *
          Real.log (condDist P Z (pair X W) (a, w) b / Q w b) ≤ ε) :
    condI P X Z W ≤ Real.log r + ε :=
  condI_le_of_KL_le X Z W Q hQ hQ0 (Real.log r + ε) fun a w haw =>
    KLdist_le_log_add_of_ratio_le_on
      (isProbDist_condDist Z (pair X W) (a, w) haw) (hQ w) (G a w) hr
      (hgood a w) (hbad a w)

/-! ### Sanity check: the old bound is a special case -/

/-- **`condI_le_log_of_ratio_le`, re-derived from the exceptional-set bound.**
Taking `G a w = univ` and `ε = 0` makes the exceptional sum empty, so the new
statement collapses to the old one verbatim.

This is a check that the relaxation did not weaken anything: `condI_le_log_of_ratio_le`
is exactly the `G = univ`, `ε = 0` corner of
`condI_le_log_add_of_ratio_le_on`. -/
theorem condI_le_log_of_ratio_le' {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ)
    (hQ : ∀ w, IsProbDist (Q w))
    (hQ0 : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0) {r : ℝ} (hr : 1 ≤ r)
    (h : ∀ a w b, condDist P Z (pair X W) (a, w) b ≤ r * Q w b) :
    condI P X Z W ≤ Real.log r := by
  have := condI_le_log_add_of_ratio_le_on X Z W Q hQ hQ0
    (fun _ _ => (Finset.univ : Finset β)) (r := r) (ε := 0) hr
    (fun a w b _ => h a w b)
    (fun a w => by rw [Finset.sdiff_self, Finset.sum_empty])
  simpa using this

/-- **The two statements are literally the same statement.** `condI_le_log_of_ratio_le'`
above is not merely *an* analogue of `CondVariational.lean`'s
`condI_le_log_of_ratio_le`; the two have identical types, so the `G = univ`,
`ε = 0` specialisation of `condI_le_log_add_of_ratio_le_on` reproduces the old
endpoint with no hypothesis added, removed or reordered.

The `funext` succeeds only if every one of the eighteen binders — implicit type
variables, `Fintype`/`DecidableEq` instances, the space, the four maps, the two
side conditions, `r`, and the ratio hypothesis — matches on the nose; the
remaining goal is an equality of two proofs of one Prop, closed by proof
irrelevance. -/
private theorem condI_le_log_of_ratio_le_eq_condI_le_log_of_ratio_le' :
    @condI_le_log_of_ratio_le = @condI_le_log_of_ratio_le' := by
  funext α β γ _ _ _ _ _ _ P X Z W Q hQ hQ0 r hr h
  rfl

/-! ### A convenience form of the exceptional hypothesis

The hypothesis `hbad` is a bound on a KL-like sum, which is not the shape an
application usually has in hand. What one usually has is: the reference law is
not too small on the exceptional letters, and the true law puts very little mass
there. Those two facts give `hbad` with `ε = δ * log (1 / m)` — the shape of the
paper-style estimate "exceptional contribution ≤ (tiny mass) × (a log factor)".

The requirement `m ≤ 1` is not restrictive: `m` is a lower bound on the masses of
a probability distribution, so `m ≤ 1` unless the exceptional set is empty. It is
needed to know `log (1 / m) ≥ 0`, which is what lets the mass bound `δ` be
substituted for the actual exceptional mass. -/

/-- **The exceptional KL mass, bounded by mass times a log factor.** If the
reference law is at least `m > 0` on `S` and `p` is a probability distribution,
then `∑_{b ∈ S} p b * log (p b / q b) ≤ (∑_{b ∈ S} p b) * log (1 / m)`. -/
private theorem sum_mul_log_div_le_mass_mul_log [Fintype β] {p q : β → ℝ}
    (hp : IsProbDist p) (S : Finset β) {m : ℝ} (hm : 0 < m)
    (hq : ∀ b ∈ S, m ≤ q b) :
    ∑ b ∈ S, p b * Real.log (p b / q b) ≤ (∑ b ∈ S, p b) * Real.log (1 / m) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b hb =>
    mul_log_div_le_mul_log_one_div (hp.nonneg b) (hp.le_one b) hm (hq b hb)

/-- `log (1 / m) ≥ 0` for `0 < m ≤ 1`. -/
private theorem log_one_div_nonneg {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    0 ≤ Real.log (1 / m) := by
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hm, one_mul]
  exact hm1

/-- **The KL bound with the exceptional set controlled by mass.** A ratio bound
`p ≤ r * q` on `G`; a lower bound `m` on the reference law off `G`; and a bound
`δ` on the mass `p` puts off `G`. Then

    `KL(p ‖ q) ≤ log r + δ * log (1 / m)`.

This is the shape an application typically has: the exceptional regime is
characterised by "the true law is tiny there", and the reference law is a null
model whose masses are explicitly bounded below. -/
theorem KLdist_le_log_add_of_ratio_le_on_of_mass_le [Fintype β] [DecidableEq β]
    {p q : β → ℝ} (hp : IsProbDist p) (hq : IsProbDist q) (G : Finset β)
    {r m δ : ℝ} (hr : 1 ≤ r) (hm : 0 < m) (hm1 : m ≤ 1)
    (hgood : ∀ b ∈ G, p b ≤ r * q b)
    (hqm : ∀ b ∈ Finset.univ \ G, m ≤ q b)
    (hmass : ∑ b ∈ Finset.univ \ G, p b ≤ δ) :
    KLdist p q ≤ Real.log r + δ * Real.log (1 / m) := by
  refine KLdist_le_log_add_of_ratio_le_on hp hq G hr hgood ?_
  refine (sum_mul_log_div_le_mass_mul_log hp _ hm hqm).trans ?_
  exact mul_le_mul_of_nonneg_right hmass (log_one_div_nonneg hm hm1)

/-- **The conditional bound with the exceptional set controlled by mass.** The
conditional counterpart of `KLdist_le_log_add_of_ratio_le_on_of_mass_le`, and the
most directly usable endpoint of this file: every hypothesis is a statement about
the conditional law of a *single* answer, and the additive budget is an explicit
product of an exceptional mass and a log factor. -/
theorem condI_le_log_add_of_ratio_le_on_of_mass_le {α β γ : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {P : FinProb} (X : P.Ω → α) (Z : P.Ω → β) (W : P.Ω → γ) (Q : γ → β → ℝ)
    (hQ : ∀ w, IsProbDist (Q w))
    (hQ0 : ∀ w b, condDist P Z W w b ≠ 0 → Q w b ≠ 0)
    (G : α → γ → Finset β) {r m δ : ℝ} (hr : 1 ≤ r) (hm : 0 < m) (hm1 : m ≤ 1)
    (hgood : ∀ a w, ∀ b ∈ G a w, condDist P Z (pair X W) (a, w) b ≤ r * Q w b)
    (hqm : ∀ a w, ∀ b ∈ Finset.univ \ G a w, m ≤ Q w b)
    (hmass : ∀ a w, ∑ b ∈ Finset.univ \ G a w,
        condDist P Z (pair X W) (a, w) b ≤ δ) :
    condI P X Z W ≤ Real.log r + δ * Real.log (1 / m) :=
  condI_le_of_KL_le X Z W Q hQ hQ0 (Real.log r + δ * Real.log (1 / m))
    fun a w haw =>
      KLdist_le_log_add_of_ratio_le_on_of_mass_le
        (isProbDist_condDist Z (pair X W) (a, w) haw) (hQ w) (G a w) hr hm hm1
        (hgood a w) (hqm a w) (hmass a w)

end InformationTheory
end Arlib
