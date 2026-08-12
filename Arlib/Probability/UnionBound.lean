/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.Markov

/-!
# Union-bound and Markov corollaries in "all events fail" form

The two workhorses of every "with high probability everything goes right"
argument are already in the library in their primitive form:

* the union bound `FinProb.Pr_biUnion_le` — `Pr[⋃ᵢ Eᵢ] ≤ ∑ᵢ Pr[Eᵢ]`
  (`Arlib.Probability.FinProb`);
* monotonicity `FinProb.Pr_mono` (same file);
* Markov's inequality `FinProb.markov` — `Pr[X ≥ a] ≤ Ex[X]/a` for `X ≥ 0`,
  `a > 0` (`Arlib.Probability.Markov`).

What downstream proofs actually reach for, however, is never quite that shape.
A typical argument produces a *uniform* per-event failure bound
`∀ i ∈ s, Pr[Eᵢ] ≤ b` — for instance from `fourth_moment_tail`, which bounds each
`Pr[|Sᵢ - μᵢ| ≥ a]` by the same expression — and then wants to conclude that with
probability at least `1 - |s| · b` *no* event occurs.  Getting there from
`Pr_biUnion_le` costs three small steps every time: sum a constant bound, take a
complement, and rewrite a `biUnion` of `filter`s as a `filter` of an existential.
This file does those three steps once and for all.

## Main results

* `FinProb.Pr_compl` — `Pr[univ \ E] = 1 - Pr[E]`, the missing complement lemma
  (`Pr_filter_compl` covers only the `filter`/`¬ filter` pair).
* `FinProb.Pr_biUnion_le_card_mul` — `Pr[⋃_{i∈s} Eᵢ] ≤ |s| · b` from a uniform
  bound `b` on each `Pr[Eᵢ]`.
* `FinProb.one_sub_card_mul_le_Pr_compl_biUnion` — the complementary form
  `1 - |s| · b ≤ Pr[univ \ ⋃_{i∈s} Eᵢ]`.
* `FinProb.Pr_exists_le` and `FinProb.one_sub_card_mul_le_Pr_forall_not` — the
  same two statements with the events presented as `univ.filter (p i)`, which is
  the idiom in which `Arlib.Probability.FourthMomentTail` and
  `Arlib.Probability.MomentMethod` state their tail bounds, so that the union
  bound composes with them without any set-theoretic massaging.
* `FinProb.markov_one` — Markov at `a = 1`, i.e. `Pr[X ≥ 1] ≤ Ex[X]`, the form
  used for an `ℕ`-valued counting variable (where `X ≥ 1` is exactly `X ≠ 0`).

Markov's inequality itself is **not** restated here: `FinProb.markov` is already
public in `Arlib.Probability.Markov`, in exactly the `Pr`-of-`filter` idiom, and
`even_moment_tail` uses it directly.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-! ## Complements

`Pr_filter_compl` already records that a predicate and its negation split the
total mass; what is missing is the same fact for an arbitrary event and its
set-theoretic complement `univ \ E`, which is the shape a union bound leaves
behind. -/

/-- **The complement rule.** `Pr[univ \ E] = 1 - Pr[E]`.

The `Finset` difference `univ \ E` is the complement of `E` in the outcome
space, so this is additivity over the disjoint decomposition
`univ = E ∪ (univ \ E)`. -/
theorem Pr_compl (E : Event P) : P.Pr (Finset.univ \ E) = 1 - P.Pr E := by
  have hdisj : Disjoint E (Finset.univ \ E) := Finset.disjoint_sdiff
  have hunion : E ∪ (Finset.univ \ E) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ E)
  have h : P.Pr E + P.Pr (Finset.univ \ E) = 1 := by
    rw [← P.Pr_union_disjoint hdisj, hunion, Pr_univ]
  linarith

/-! ## The union bound with a uniform per-event bound

`Pr_biUnion_le` bounds `Pr[⋃ᵢ Eᵢ]` by `∑ᵢ Pr[Eᵢ]`; in practice the individual
bounds are all the same number `b`, and the sum collapses to `|s| · b`. -/

/-- **Union bound, uniform form.**  If every event in the family has probability
at most `b`, then their union has probability at most `|s| · b`.

This is `Pr_biUnion_le` followed by `∑_{i∈s} b = |s| · b`; it is the form in
which the union bound is applied when a single tail estimate (say
`fourth_moment_tail`) bounds every event by the same expression. -/
theorem Pr_biUnion_le_card_mul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Event P) {b : ℝ} (h : ∀ i ∈ s, P.Pr (E i) ≤ b) :
    P.Pr (s.biUnion E) ≤ s.card * b := by
  calc P.Pr (s.biUnion E) ≤ ∑ i ∈ s, P.Pr (E i) := P.Pr_biUnion_le s E
    _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum h
    _ = s.card * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Union bound, complementary ("nothing goes wrong") form.**  If every event
in the family has probability at most `b`, then with probability at least
`1 - |s| · b` **none** of them occurs.

This is the statement an "all `|s|` sub-arguments succeed simultaneously" step
consumes; note that it is vacuously true (though useless) when `|s| · b > 1`. -/
theorem one_sub_card_mul_le_Pr_compl_biUnion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Event P) {b : ℝ} (h : ∀ i ∈ s, P.Pr (E i) ≤ b) :
    1 - s.card * b ≤ P.Pr (Finset.univ \ s.biUnion E) := by
  have hle := P.Pr_biUnion_le_card_mul s E h
  rw [P.Pr_compl]
  linarith

/-! ## The `Pr`-of-`filter` presentation

Tail bounds throughout the library (`markov`, `chebyshev`, `even_moment_tail`,
`fourth_moment_tail`) state their conclusions as `P.Pr (univ.filter p)`.  To
union-bound a family of such events one first has to see the `biUnion` of the
`filter`s as the `filter` of the existential; `biUnion_filter_eq` does that, and
the two lemmas after it are the uniform and complementary forms above,
transported across it. -/

/-- The union of the events `{ω | p i ω}` over `i ∈ s` is the event
`{ω | ∃ i ∈ s, p i ω}`.

This is the bridge between the `biUnion` shape in which the union bound is
proved and the `filter` shape in which tail bounds are stated. -/
theorem biUnion_filter_eq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → P.Ω → Prop) [∀ i, DecidablePred (p i)] :
    (s.biUnion fun i => Finset.univ.filter (p i))
      = Finset.univ.filter (fun ω => ∃ i ∈ s, p i ω) := by
  ext ω
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Union bound in the `filter` idiom.**  The probability that *some* `p i`
holds is at most the sum of the individual probabilities.

Stated so that the summands `P.Pr (univ.filter (p i))` are literally the
left-hand sides produced by `markov`, `chebyshev`, `even_moment_tail` and
`fourth_moment_tail`. -/
theorem Pr_exists_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → P.Ω → Prop) [∀ i, DecidablePred (p i)] :
    P.Pr (Finset.univ.filter (fun ω => ∃ i ∈ s, p i ω))
      ≤ ∑ i ∈ s, P.Pr (Finset.univ.filter (p i)) := by
  rw [← P.biUnion_filter_eq s p]
  exact P.Pr_biUnion_le s _

/-- **Union bound in the `filter` idiom, uniform form.**  If each `p i` holds
with probability at most `b`, then some `p i` holds with probability at most
`|s| · b`. -/
theorem Pr_exists_le_card_mul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → P.Ω → Prop) [∀ i, DecidablePred (p i)] {b : ℝ}
    (h : ∀ i ∈ s, P.Pr (Finset.univ.filter (p i)) ≤ b) :
    P.Pr (Finset.univ.filter (fun ω => ∃ i ∈ s, p i ω)) ≤ s.card * b := by
  rw [← P.biUnion_filter_eq s p]
  exact P.Pr_biUnion_le_card_mul s _ h

/-- **Union bound in the `filter` idiom, complementary form.**  If each "bad
event" `p i` has probability at most `b`, then with probability at least
`1 - |s| · b` **every** `p i` fails simultaneously.

This is the exact statement a "all sub-estimates hold at once" step needs: the
conclusion is again a `P.Pr (univ.filter _)`, so it can itself be fed into a
further union bound. -/
theorem one_sub_card_mul_le_Pr_forall_not {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → P.Ω → Prop) [∀ i, DecidablePred (p i)] {b : ℝ}
    (h : ∀ i ∈ s, P.Pr (Finset.univ.filter (p i)) ≤ b) :
    1 - s.card * b
      ≤ P.Pr (Finset.univ.filter (fun ω => ∀ i ∈ s, ¬ p i ω)) := by
  have hsplit := P.Pr_filter_compl (fun ω => ∃ i ∈ s, p i ω)
  have hbad := P.Pr_exists_le_card_mul s p h
  -- `¬ ∃ i ∈ s, p i ω` is definitionally the "all good" predicate.
  have hgood : Finset.univ.filter (fun ω => ¬ ∃ i ∈ s, p i ω)
      = Finset.univ.filter (fun ω => ∀ i ∈ s, ¬ p i ω) := by
    apply Finset.filter_congr
    intro ω _
    simp only [not_exists]
    tauto
  rw [hgood] at hsplit
  linarith

/-! ## Markov at threshold one

For an `ℕ`-valued counting variable viewed in `ℝ`, "the count is nonzero" is the
event `X ≥ 1`, and Markov at `a = 1` bounds its probability by the mean itself.
This is the form used whenever one shows that an expected count `o(1)` forces the
count to vanish with high probability (the *first-moment method*). -/

/-- **Markov at threshold `1`.**  For a nonnegative random variable,
`Pr[X ≥ 1] ≤ Ex[X]`.

For an `ℕ`-valued `X` (viewed in `ℝ`) the hypothesis `0 ≤ X` is automatic and the
event `1 ≤ X ω` is exactly `X ω ≠ 0`, so this reads: the probability that the
count is nonzero is at most its expectation. -/
theorem markov_one (X : P.Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) :
    P.Pr (Finset.univ.filter (fun ω => 1 ≤ X ω)) ≤ P.Ex X := by
  have h := P.markov X hX (a := 1) one_pos
  simpa using h

/-- **First-moment method for an `ℕ`-valued count.**  If `N : P.Ω → ℕ` counts
something, the probability that the count is nonzero is at most its expectation
`Ex[(N ·  : ℝ)]`.

This is `markov_one` specialized to a variable of the form `fun ω => (N ω : ℝ)`,
with the nonnegativity hypothesis discharged and the threshold event stated as
`N ω ≠ 0` rather than `1 ≤ (N ω : ℝ)`. -/
theorem Pr_count_ne_zero_le_Ex (N : P.Ω → ℕ) :
    P.Pr (Finset.univ.filter (fun ω => N ω ≠ 0))
      ≤ P.Ex (fun ω => (N ω : ℝ)) := by
  have hev : Finset.univ.filter (fun ω => N ω ≠ 0)
      = Finset.univ.filter (fun ω => 1 ≤ ((N ω : ℝ))) := by
    apply Finset.filter_congr
    intro ω _
    have : (1 : ℝ) ≤ (N ω : ℝ) ↔ 1 ≤ N ω := by exact_mod_cast Iff.rfl
    simp only [this]
    omega
  rw [hev]
  exact P.markov_one _ (fun ω => Nat.cast_nonneg _)

end FinProb
end Arlib.Probability
