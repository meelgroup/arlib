/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# First-bad decomposition (exact "first occurrence in visitation order" identity)

For a finite family of events `E : ι → (P.Ω → Prop)` indexed by a `Finset s` carrying a
linear order (the *visitation order*), the probability of the union decomposes
*exactly* as the sum, over each `q`, of the probability of the "first-bad-at-`q`"
event `E q ∩ ⋂_{q' < q} (E q')ᶜ`:

  `Pr (⋃_{q∈s} E q) = ∑_{q∈s} Pr (E q ∩ {∀ q'∈s, q' < q → ¬ E q'})`.

This is the standard disjointification of a union along a linear order,
formalized purely at the abstract-probability (`ProbSpace`) level.  The
"prefix-good" event `firstBadPre s E q` is exactly `⋂_{q' < q} (E q')ᶜ`.  The
point of the identity is that it lets one bound each summand by the *stronger*
conditioned bound `Pr (E q ∩ prefix-good_q)` — restricting to the event that
every earlier index behaved well — instead of the unconditional `Pr (E q)`.

The exact additivity comes from linearity of the abstract expectation over the
*disjoint* first-bad pieces (`Ex_sum`): the indicator of the union equals the pointwise
sum of the pieces' indicators, so `Ex` distributes.  Admissibility of each piece
indicator is threaded through the `hpiece` hypothesis (auto over `FinProb`).

No `sorry`, no new axioms.
-/
import Arlib.Probability.ProbSpace

namespace Arlib.Probability

open scoped BigOperators Classical
open Finset ProbSpace

set_option linter.unusedSectionVars false

namespace FinProb

variable {P : ProbSpace} {ι : Type} [DecidableEq ι] [LinearOrder ι]

/-- **The prefix-good event of `q`** (relative to a family `E` and index set `s`):
all *strictly earlier* states `q' < q` (`q' ∈ s`) are *good*, i.e. `¬ E q' ω`.
This is the predicate realization of `⋂_{q'∈s, q'<q} (E q')ᶜ`. -/
def firstBadPre (s : Finset ι) (E : ι → P.Ω → Prop) (q : ι) : P.Ω → Prop :=
  fun ω => ∀ q' ∈ s, q' < q → ¬ E q' ω

/-- **The first-bad piece at `q`**: `q` is bad and every strictly-earlier state is good. -/
def firstBadPiece (s : Finset ι) (E : ι → P.Ω → Prop) (q : ι) : P.Ω → Prop :=
  fun ω => E q ω ∧ firstBadPre s E q ω

/-- The first-bad pieces are pairwise disjoint: two distinct `q₁ < q₂` cannot both be
first-bad, since `firstBadPiece … q₂` demands `q₁` (which is `< q₂`) be good, while
`firstBadPiece … q₁` entails `E q₁`. -/
theorem firstBadPiece_disjoint (s : Finset ι) (E : ι → P.Ω → Prop) :
    ∀ q₁ ∈ s, ∀ q₂ ∈ s, q₁ ≠ q₂ → ∀ ω,
      firstBadPiece s E q₁ ω → ¬ firstBadPiece s E q₂ ω := by
  intro q₁ h₁ q₂ h₂ hne ω hω₁ hω₂
  simp only [firstBadPiece, firstBadPre] at hω₁ hω₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hω₂.2 q₁ h₁ hlt hω₁.1
  · exact hω₁.2 q₂ h₂ hgt hω₂.1

/-- The union of the first-bad pieces equals the union of the events (pointwise): any
outcome in `⋃ E` lies in the first-bad piece of the *least* index whose event it hits
(finite linear order). -/
theorem exists_firstBadPiece_iff (s : Finset ι) (E : ι → P.Ω → Prop) (ω : P.Ω) :
    (∃ q ∈ s, firstBadPiece s E q ω) ↔ (∃ q ∈ s, E q ω) := by
  constructor
  · -- pieces ⊆ events
    rintro ⟨q, hq, hEq, -⟩
    exact ⟨q, hq, hEq⟩
  · -- events ⊆ pieces: take the least bad index
    rintro ⟨q, hq, hωq⟩
    -- the set of bad indices for `ω` is a nonempty subset of `s`
    have hbad : (s.filter (fun q => E q ω)).Nonempty :=
      ⟨q, Finset.mem_filter.2 ⟨hq, hωq⟩⟩
    obtain ⟨q₀, hq₀mem, hq₀min⟩ := (s.filter (fun q => E q ω)).exists_min_image id hbad
    rw [Finset.mem_filter] at hq₀mem
    refine ⟨q₀, hq₀mem.1, hq₀mem.2, ?_⟩
    intro q' hq' hlt hωq'
    -- `q'` is a bad index `< q₀`, contradicting minimality of `q₀`
    have : q₀ ≤ q' := hq₀min q' (Finset.mem_filter.2 ⟨hq', hωq'⟩)
    exact absurd this (not_le.2 hlt)

/-- **First-bad decomposition (exact identity).**  `Pr (⋃_{q∈s} E q)` equals the sum
over `q ∈ s` of the probability of the "first-bad-at-`q`" event
`E q ∩ firstBadPre s E q` (`= E q ∩ ⋂_{q'<q} (E q')ᶜ`).

The identity is exact linearity of `Ex` over the *disjoint* pieces: the indicator of the
union is the pointwise sum of the pieces' indicators, so `Ex_sum` applies (guarded by
`hpiece`, auto over `FinProb`). -/
theorem Pr_biUnion_eq_sum_firstBad (s : Finset ι) (E : ι → P.Ω → Prop)
    (hpiece : ∀ q ∈ s, IsAdm P (indic (firstBadPiece s E q))) :
    P.Pr (fun ω => ∃ q ∈ s, E q ω) = ∑ q ∈ s, P.Pr (firstBadPiece s E q) := by
  have hcongr : P.Pr (fun ω => ∃ q ∈ s, E q ω)
      = P.Pr (fun ω => ∃ q ∈ s, firstBadPiece s E q ω) :=
    (P.Pr_congr (fun ω => exists_firstBadPiece_iff s E ω)).symm
  rw [hcongr]
  simp only [ProbSpace.Pr_eq_Ex_indicator]
  rw [← P.Ex_sum s (fun q => indic (firstBadPiece s E q)) hpiece]
  refine congrArg P.Ex (funext (fun ω => ?_))
  simp only [indic_apply]
  by_cases h : ∃ q ∈ s, firstBadPiece s E q ω
  · rw [if_pos h]
    obtain ⟨q₀, hq₀, hpc₀⟩ := h
    rw [Finset.sum_eq_single q₀]
    · rw [if_pos hpc₀]
    · intro q hq hqne
      exact if_neg (fun hpcq =>
        firstBadPiece_disjoint s E q hq q₀ hq₀ hqne ω hpcq hpc₀)
    · intro hq₀notin
      exact absurd hq₀ hq₀notin
  · rw [if_neg h]
    refine (Finset.sum_eq_zero ?_).symm
    intro q hq
    exact if_neg (fun hpcq => h ⟨q, hq, hpcq⟩)

/-- **First-bad bound.**  If each first-bad summand `Pr (E q ∩ firstBadPre s E q)` is
`≤ c q`, then `Pr (⋃_{q∈s} E q) ≤ ∑_{q∈s} c q`.  This is the identity above combined
with termwise monotonicity — the workhorse form that replaces the naive union bound
with the sharper "first-bad, on the prefix-good event" per-state bounds. -/
theorem Pr_biUnion_le_sum_firstBad (s : Finset ι) (E : ι → P.Ω → Prop) (c : ι → ℝ)
    (hpiece : ∀ q ∈ s, IsAdm P (indic (firstBadPiece s E q)))
    (h : ∀ q ∈ s, P.Pr (firstBadPiece s E q) ≤ c q) :
    P.Pr (fun ω => ∃ q ∈ s, E q ω) ≤ ∑ q ∈ s, c q := by
  rw [Pr_biUnion_eq_sum_firstBad s E hpiece]
  exact Finset.sum_le_sum h

end FinProb
end Arlib.Probability
