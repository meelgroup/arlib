/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The bundled finite probability space

Many combinatorial probability arguments live over a *finite* outcome space,
with each outcome carrying an explicit probability (for example, obtained as a
product of coin-toss probabilities).  Rather than pulling in the full
measure-theoretic machinery, we model exactly this, and keep every quantity in
`ℝ`, which is what makes the combinatorial arguments (union bound, tail bounds)
clean and robust.

**One primitive, two presentations.**  `FinDist Ω`
(`Arlib.Probability.FinDist`) is the primitive: a mass function on a *given*
finite type, parameterised over `Ω` and universe-polymorphic.  `FinProb` is its
*bundled* form — it packages the outcome type together with its
`Fintype`/`DecidableEq` instances and its law, so that a whole space can be
passed as a single object, which is what the combinatorial arguments here want.

`FinProb` is therefore a thin layer, not a rival: its field is literally a
`FinDist`, and `P.mass` is a reducible abbreviation for `P.μ.p`.  Every
definitional-equality argument that used to go through a primitive `mass` field
still goes through unchanged, and `P.toFinDist` takes a bundled space back to the
primitive.  Reach for `FinDist` when the outcome type is fixed and given; reach
for `FinProb` when the space itself is the thing being constructed, transported
or quantified over.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDist

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-- A finite probability space: a `Fintype` of outcomes `Ω` carrying a
distribution `μ : FinDist Ω`.

This is the *bundled* form of `FinDist`: it packages the outcome type together
with its `Fintype`/`DecidableEq` instances and its law, so that a space can be
passed around as a single object.  `FinDist` remains the primitive; everything
here is a thin layer over it.  The mass function is available as `P.mass`
(a reducible abbreviation for `P.μ.p`), so all the existing `mass`-level API is
unchanged. -/
structure FinProb where
  /-- The outcome type. -/
  Ω : Type
  [fin : Fintype Ω]
  [dec : DecidableEq Ω]
  /-- The law of the space, as a distribution on `Ω`. -/
  μ : FinDist Ω

attribute [instance] FinProb.fin FinProb.dec

namespace FinProb

variable (P : FinProb)

/-- The mass function of a finite probability space.  Reducible: it *is* the
underlying `FinDist`'s mass function, so every definitional-equality argument
that used to go through the old `mass` field still goes through. -/
abbrev mass : P.Ω → ℝ := P.μ.p

theorem mass_nonneg (ω : P.Ω) : 0 ≤ P.mass ω := P.μ.p_nonneg ω

theorem mass_sum : ∑ ω, P.mass ω = 1 := P.μ.p_sum

/-- The law of a finite probability space, read as a distribution on its outcome
type.  This is the bridge in the other direction from the `FinProb` bundle back
to the `FinDist` primitive. -/
abbrev toFinDist : FinDist P.Ω := P.μ

@[simp] theorem toFinDist_apply (ω : P.Ω) : P.toFinDist ω = P.mass ω := rfl

/-- Events are subsets of the outcome space, represented as `Finset`s. -/
abbrev Event := Finset P.Ω

/-- The probability of an event is the total mass of its outcomes. -/
def Pr (E : Event P) : ℝ := ∑ ω ∈ E, P.mass ω

@[simp] theorem Pr_empty : P.Pr ∅ = 0 := by simp [Pr]

@[simp] theorem Pr_univ : P.Pr (Finset.univ) = 1 := by
  simpa [Pr] using P.mass_sum

theorem Pr_nonneg (E : Event P) : 0 ≤ P.Pr E :=
  Finset.sum_nonneg fun ω _ => P.mass_nonneg ω

/-- Probability is monotone with respect to event inclusion. -/
theorem Pr_mono {E F : Event P} (h : E ⊆ F) : P.Pr E ≤ P.Pr F :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => P.mass_nonneg ω

theorem Pr_le_one (E : Event P) : P.Pr E ≤ 1 := by
  have h : P.Pr E ≤ P.Pr (Finset.univ) := P.Pr_mono (Finset.subset_univ E)
  simpa [Pr, P.mass_sum] using h

/-- Subadditivity for a binary union: `Pr (A ∪ B) ≤ Pr A + Pr B`. -/
theorem Pr_union_le (A B : Event P) : P.Pr (A ∪ B) ≤ P.Pr A + P.Pr B := by
  have hkey : (∑ ω ∈ A ∪ B, P.mass ω) + (∑ ω ∈ A ∩ B, P.mass ω)
      = (∑ ω ∈ A, P.mass ω) + (∑ ω ∈ B, P.mass ω) :=
    Finset.sum_union_inter
  have hnn : 0 ≤ ∑ ω ∈ A ∩ B, P.mass ω :=
    Finset.sum_nonneg fun ω _ => P.mass_nonneg ω
  unfold Pr
  linarith

/-- Finite union bound (Boole's inequality) over an index `Finset`. -/
theorem Pr_biUnion_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Event P) :
    P.Pr (s.biUnion E) ≤ ∑ i ∈ s, P.Pr (E i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hnotmem ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hnotmem]
      calc
        P.Pr (E i ∪ s.biUnion E) ≤ P.Pr (E i) + P.Pr (s.biUnion E) :=
              P.Pr_union_le _ _
        _ ≤ P.Pr (E i) + ∑ i ∈ s, P.Pr (E i) := by linarith [ih]

/-- Additivity of `Pr` over a **disjoint** binary union. -/
theorem Pr_union_disjoint {A B : Event P} (h : Disjoint A B) :
    P.Pr (A ∪ B) = P.Pr A + P.Pr B := by
  unfold Pr
  exact Finset.sum_union h

/-- An event and its complement (relative to `univ`) partition the total mass. -/
theorem Pr_filter_compl (p : P.Ω → Prop) [DecidablePred p] :
    P.Pr (univ.filter p) + P.Pr (univ.filter (fun ω => ¬ p ω)) = 1 := by
  have hdisj : Disjoint (univ.filter p) (univ.filter (fun ω => ¬ p ω)) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hunion : univ.filter p ∪ univ.filter (fun ω => ¬ p ω) = univ := by
    ext ω; by_cases h : p ω <;> simp [h]
  rw [← P.Pr_union_disjoint hdisj, hunion, Pr_univ]

/-- Additivity of `Pr` over a **pairwise-disjoint** finite union. -/
theorem Pr_biUnion_disjoint {ι : Type*}
    (s : Finset ι) (E : ι → Event P)
    (h : (s : Set ι).PairwiseDisjoint E) :
    P.Pr (s.biUnion E) = ∑ i ∈ s, P.Pr (E i) := by
  unfold Pr
  rw [Finset.sum_biUnion h]

end FinProb
end Arlib.Probability
