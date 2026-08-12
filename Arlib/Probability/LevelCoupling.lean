/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Level-by-level coupling: the two-family first-bad decomposition

A recurring pattern in the analysis of a randomized process that is built up in
*levels*, where the level-`ℓ` randomness is only approximately the idealized one:

* `A ℓ` — "the level-`ℓ` output is accurate";
* `E ℓ` — "the level-`ℓ` sample agrees with its idealized coupling partner".

One wants to bound `Pr[¬⋂_{ℓ ≤ n} A ℓ]`, but the per-level accuracy bound is
only available *conditioned on* both the accuracy and the coupling agreement at
all lower levels — because the level-`ℓ` estimate is computed from the level-`ℓ-1`
samples, whose law is only controlled through the coupling.

The resolution is two nested first-bad decompositions.  Let

  `Ainf ℓ = ⋂_{j < ℓ} A j`  and  `Einf ℓ = ⋂_{j < ℓ} E j`.

Then, purely as sets,

  `¬⋂_{ℓ ≤ n} A ℓ  ⊆  ⋃_{ℓ ≤ n} (¬A ℓ ∩ Ainf ℓ ∩ Einf ℓ)`
                   `∪  ⋃_{ℓ ≤ n} (¬E ℓ ∩ Einf ℓ ∩ Ainf (ℓ+1))`,

and hence `Pr[¬⋂ A]` is at most the sum of the two families of probabilities.
Each term of the first family is exactly the quantity a per-level accuracy lemma
bounds; each term of the second is exactly what a per-level total-variation
bound controls.

This is the abstract content of Claims `xbound`, `claim-1-main-proof` and
`fermat` in [MCM24] — Kuldeep S. Meel ⓡ Sourav Chakraborty ⓡ Umang Mathur,
*A Faster FPRAS for #NFA*, PODS 2024 (arXiv:2312.13320) — with the
process-specific content stripped out: nothing here mentions samples,
estimates, or automata.

The decomposition is *sharper* than a plain union bound over `¬A ℓ`, in the same
way `Arlib.FinProb.Pr_biUnion_eq_sum_firstBad` is: each term carries the
conjunction of all the earlier events, which is what makes the conditional
per-level bounds applicable.
-/
import Arlib.Probability.UnionBound

namespace Arlib.Probability

open Finset
open scoped BigOperators

namespace FinProb

variable {P : FinProb}

/-- **First index at which a predicate holds, within a range.**

If some `j < n` satisfies `p`, then there is a *least* such `j`: an `l < n` with
`p l` and with `¬ p j` for every `j < l`.  This is the "first bad level" step,
used twice in `compl_Ainf_subset` (once for the family `A`, once for `E`). -/
private theorem exists_first {p : ℕ → Prop} [DecidablePred p] {n : ℕ}
    (h : ∃ j < n, p j) : ∃ l < n, p l ∧ ∀ j < l, ¬ p j := by
  obtain ⟨j, hjn, hpj⟩ := h
  have hex : ∃ j, p j := ⟨j, hpj⟩
  exact ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_le hpj) hjn, Nat.find_spec hex,
    fun i hi => Nat.find_min hex hi⟩

/-- `Ainf A ℓ = ⋂_{j < ℓ} A j`, the conjunction of the first `ℓ` events.
`Ainf A 0 = univ`. -/
def Ainf (A : ℕ → Finset P.Ω) (l : ℕ) : Finset P.Ω :=
  (range l).inf A

/-- The empty conjunction is the sure event. -/
@[simp] theorem Ainf_zero (A : ℕ → Finset P.Ω) : Ainf A 0 = univ := by
  simp [Ainf]

/-- Peeling off the top level: `⋂_{j < ℓ+1} A j = (⋂_{j < ℓ} A j) ∩ A ℓ`. -/
theorem Ainf_succ (A : ℕ → Finset P.Ω) (l : ℕ) :
    Ainf A (l + 1) = Ainf A l ∩ A l := by
  rw [Ainf, Ainf, Finset.range_add_one, Finset.inf_insert, inf_comm, Finset.inf_eq_inter]

/-- `Ainf A` is antitone: a longer conjunction is a smaller event. -/
theorem Ainf_mono (A : ℕ → Finset P.Ω) {l l' : ℕ} (h : l ≤ l') :
    Ainf A l' ⊆ Ainf A l :=
  Finset.inf_mono (f := A) (Finset.range_subset_range.2 h)

/-- Each individual event of the conjunction contains it. -/
theorem Ainf_subset (A : ℕ → Finset P.Ω) {j l : ℕ} (h : j < l) :
    Ainf A l ⊆ A j :=
  Finset.inf_le (f := A) (Finset.mem_range.2 h)

/-- Membership in `Ainf A ℓ` is exactly membership in every `A j` with `j < ℓ`. -/
theorem mem_Ainf_iff (A : ℕ → Finset P.Ω) (l : ℕ) (ω : P.Ω) :
    ω ∈ Ainf A l ↔ ∀ j < l, ω ∈ A j := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [Ainf_succ, Finset.mem_inter, ih]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact h1 j h
        · exact h ▸ h2
      · exact fun h => ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h l (Nat.lt_succ_self l)⟩

/-- **The two-family first-bad decomposition**, as an inclusion of `Finset`s.

If the conjunction of `A 0, …, A n` fails, then either some `A ℓ` is the first
to fail while the coupling still held at every lower level, or the coupling
broke first, at some level `ℓ` at which every `A j`, `j ≤ ℓ`, still held. -/
theorem compl_Ainf_subset (A E : ℕ → Finset P.Ω) (n : ℕ) :
    (univ \ Ainf A (n + 1)) ⊆
      ((range (n + 1)).biUnion fun l => (univ \ A l) ∩ Ainf A l ∩ Ainf E l) ∪
      ((range (n + 1)).biUnion fun l => (univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1)) := by
  intro ω hω
  rw [Finset.mem_sdiff] at hω
  -- The conjunction fails, so some level `j ≤ n` has `ω ∉ A j`.
  have hex : ∃ j < n + 1, ω ∉ A j := by
    by_contra hc
    push Not at hc
    exact hω.2 ((mem_Ainf_iff A (n + 1) ω).2 hc)
  -- Take the first such level `l`; minimality says `ω ∈ Ainf A l`.
  obtain ⟨l, hln, hAl, hmin⟩ := exists_first hex
  have hωA : ω ∈ Ainf A l :=
    (mem_Ainf_iff A l ω).2 fun j hj => not_not.1 (hmin j hj)
  by_cases hE : ω ∈ Ainf E l
  · -- The coupling still held below `l`: `ω` lies in the `l`-th accuracy piece.
    refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_range.2 hln, ?_⟩)
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨⟨hAl, hωA⟩, hE⟩
  · -- The coupling broke first; take the first level `l' < l` at which it did.
    have hex' : ∃ j < l, ω ∉ E j := by
      by_contra hc
      push Not at hc
      exact hE ((mem_Ainf_iff E l ω).2 hc)
    obtain ⟨l', hl'l, hEl', hmin'⟩ := exists_first hex'
    have hωE : ω ∈ Ainf E l' :=
      (mem_Ainf_iff E l' ω).2 fun j hj => not_not.1 (hmin' j hj)
    -- `l' + 1 ≤ l`, so accuracy up to `l` gives accuracy up to `l' + 1`.
    have hωA' : ω ∈ Ainf A (l' + 1) := Ainf_mono A hl'l hωA
    refine Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨l', Finset.mem_range.2 (hl'l.trans hln), ?_⟩)
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨⟨hEl', hωE⟩, hωA'⟩

/-- **The probability form.**  `Pr[¬⋂_{ℓ ≤ n} A ℓ]` is bounded by the sum of the
per-level accuracy terms and the per-level coupling terms. -/
theorem Pr_compl_Ainf_le (A E : ℕ → Finset P.Ω) (n : ℕ) :
    P.Pr (univ \ Ainf A (n + 1)) ≤
      (∑ l ∈ range (n + 1), P.Pr ((univ \ A l) ∩ Ainf A l ∩ Ainf E l)) +
      (∑ l ∈ range (n + 1), P.Pr ((univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1))) := by
  calc P.Pr (univ \ Ainf A (n + 1))
      ≤ P.Pr (((range (n + 1)).biUnion fun l => (univ \ A l) ∩ Ainf A l ∩ Ainf E l) ∪
          ((range (n + 1)).biUnion fun l => (univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1))) :=
        P.Pr_mono (compl_Ainf_subset A E n)
    _ ≤ P.Pr ((range (n + 1)).biUnion fun l => (univ \ A l) ∩ Ainf A l ∩ Ainf E l) +
          P.Pr ((range (n + 1)).biUnion fun l => (univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1)) :=
        P.Pr_union_le _ _
    _ ≤ _ := add_le_add (P.Pr_biUnion_le _ _) (P.Pr_biUnion_le _ _)

/-- The packaged form used at a call site: uniform per-level bounds `a` and `e`
give `Pr[⋂_{ℓ ≤ n} A ℓ] ≥ 1 - (n+1)(a + e)`. -/
theorem one_sub_le_Pr_Ainf (A E : ℕ → Finset P.Ω) (n : ℕ) (a e : ℝ)
    (ha : ∀ l ∈ range (n + 1), P.Pr ((univ \ A l) ∩ Ainf A l ∩ Ainf E l) ≤ a)
    (he : ∀ l ∈ range (n + 1), P.Pr ((univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1)) ≤ e) :
    1 - ((n : ℝ) + 1) * (a + e) ≤ P.Pr (Ainf A (n + 1)) := by
  have hcard : ((range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hA : (∑ l ∈ range (n + 1), P.Pr ((univ \ A l) ∩ Ainf A l ∩ Ainf E l))
      ≤ ((n : ℝ) + 1) * a := by
    calc (∑ l ∈ range (n + 1), P.Pr ((univ \ A l) ∩ Ainf A l ∩ Ainf E l))
        ≤ ∑ _l ∈ range (n + 1), a := Finset.sum_le_sum ha
      _ = ((n : ℝ) + 1) * a := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hE : (∑ l ∈ range (n + 1), P.Pr ((univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1)))
      ≤ ((n : ℝ) + 1) * e := by
    calc (∑ l ∈ range (n + 1), P.Pr ((univ \ E l) ∩ Ainf E l ∩ Ainf A (l + 1)))
        ≤ ∑ _l ∈ range (n + 1), e := Finset.sum_le_sum he
      _ = ((n : ℝ) + 1) * e := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hbound := Pr_compl_Ainf_le A E n
  have hcompl := P.Pr_compl (Ainf A (n + 1))
  rw [hcompl] at hbound
  have hexp : ((n : ℝ) + 1) * (a + e) = ((n : ℝ) + 1) * a + ((n : ℝ) + 1) * e := by ring
  rw [hexp]
  linarith

end FinProb

end Arlib.Probability
