/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Independence and the Chernoff-type bound for independent runs

A tail bound on the number of events that occur among an independent family of
"bad" events follows from independence together with the intersection tail bound.

We already have the Chernoff-type **intersection tail bound**
(`intersection_tail_bound`): if `Pr[⋂_{i∈S} Eᵢ] ≤ p^{|S|}` for all `S`,
then `Pr[∑ᵢ 𝟙_{Eᵢ} ≥ B/2] ≤ (4p)^{B/2}`.  Its hypothesis is *exactly* what
independence provides: for an independent family with `Pr[Eᵢ] ≤ p`,

  `Pr[⋂_{i∈S} Eᵢ] = ∏_{i∈S} Pr[Eᵢ] ≤ ∏_{i∈S} p = p^{|S|}`.

So `chernoff_of_indep` discharges the tail bound for any independent family of
events with `Pr[Eᵢ] ≤ p`.  Proved with no `sorry`.

**Probability model.**  Developed against the abstract `ProbSpace` interface:
events are *predicates* `P.Ω → Prop`.  The Chernoff bridge inherits the
`[IsAdm …]` guards of `intersection_tail_bound` (auto-discharged over
`FinProb`, supplied from bounded-measurability in the continuous-coin model).
-/
import Arlib.Probability.IntersectionTailBound

namespace Arlib.Probability

open scoped BigOperators Classical
open Finset ProbSpace

namespace ProbSpace

variable (P : ProbSpace) {B : ℕ} (E : Fin B → P.Ω → Prop)

/-- A family of events is (mutually) **independent** when the probability of every
finite intersection is the product of the probabilities. -/
def IndepEvents : Prop :=
  ∀ S : Finset (Fin B), P.Pr (P.interEvent E S) = ∏ i ∈ S, P.Pr (E i)

/-- For an independent family with each `Pr[Eᵢ] ≤ p` (`0 ≤ p`), the intersection
hypothesis of the tail bound holds: `Pr[⋂_{i∈S} Eᵢ] ≤ p^{|S|}`. -/
theorem interEvent_le_of_indep {p : ℝ} (hindep : P.IndepEvents E)
    (hpi : ∀ i, P.Pr (E i) ≤ p) (S : Finset (Fin B)) :
    P.Pr (P.interEvent E S) ≤ p ^ S.card := by
  rw [hindep S]
  calc ∏ i ∈ S, P.Pr (E i)
      ≤ ∏ _i ∈ S, p := by
        apply Finset.prod_le_prod
        · intro i _; exact P.Pr_nonneg _
        · intro i _; exact hpi i
    _ = p ^ S.card := by rw [Finset.prod_const]

/-- **Chernoff-type bound for an independent family.**
If `E₁,…,E_B` are independent with each `Pr[Eᵢ] ≤ p ≤ 1/2`, then the probability
that at least `B/2` of them occur is at most `(4p)^{B/2}`.

The admissibility binders are inherited from
`intersection_tail_bound` — auto-discharged over `FinProb`. -/
theorem chernoff_of_indep {p : ℝ} (hB : 1 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    [IsAdm P (indic (P.atLeast E ⌈(B : ℝ) / 2⌉₊))]
    [IsAdm P (indic (fun ω => ∃ S ∈ Finset.univ.powersetCard ⌈(B : ℝ) / 2⌉₊,
        P.interEvent E S ω))]
    (hadm : ∀ S ∈ Finset.univ.powersetCard ⌈(B : ℝ) / 2⌉₊,
        IsAdm P (indic (P.interEvent E S)))
    (hindep : P.IndepEvents E) (hpi : ∀ i, P.Pr (E i) ≤ p) :
    P.Pr (fun ω => (B : ℝ) / 2 ≤ (P.numSat E ω : ℝ))
      ≤ (4 * p) ^ ((B : ℝ) / 2) :=
  P.intersection_tail_bound E hB hp0 hp1 hadm
    (P.interEvent_le_of_indep E hindep hpi)

end ProbSpace
end Arlib.Probability
