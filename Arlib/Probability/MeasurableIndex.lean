/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Measurability of a quantity read at a random index

A recurring obligation in any formalization of a randomized process: a quantity
is read at an index that is *itself* a random variable — `f (X ω) ω`, where `X`
picks which of a family of functions to evaluate.  Nothing in Mathlib applies
directly, because `f` is a function of two arguments and only the second is the
sample point.

When the index type is **countable** the obligation dissolves: the preimage
splits as the countable union `⋃ c, {X = c} ∩ (f c)⁻¹ B` over the level sets of
the index.  This module is that split, in the three forms one actually needs.

## Main statements

* `measurable_at_index` — `ω ↦ F (g ω) ω` is measurable, given that each level
  set of `g` is measurable and each `F c` is.
* `measurableSet_at_index` — the level-set form, for a codomain carrying no
  measurable space at all.
* `measurable_comp_index` — `ω ↦ f (g ω)` for a measurable countably-valued `g`
  and an **arbitrary** `f`: no measurability hypothesis on `f` is needed, since a
  countable space with measurable singletons carries the discrete σ-algebra.
* `measurableSet_const_eq` — the degenerate case.
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

namespace Arlib.Probability

open MeasureTheory

/-- **A constant comparison is a measurable event** — trivially, the event is
`univ` or `∅`.  The degenerate case of the lemmas below: a branch that does not
read the sample point at all. -/
theorem measurableSet_const_eq {Ω β : Type*} {m : MeasurableSpace Ω} (c y : β) :
    MeasurableSet[m] {_ω : Ω | c = y} := by
  by_cases h : c = y
  · simp only [h, Set.ofPred_true]
    exact MeasurableSet.univ
  · simp only [h, Set.ofPred_false]
    exact MeasurableSet.empty

/-- **Evaluation at a measurably-varying index is measurable.**  If the index
`g` takes countably many values, each on a measurable event, and each *fixed*
index gives a measurable function `F c`, then `ω ↦ F (g ω) ω` is measurable:
its preimage is the countable union of the pieces. -/
theorem measurable_at_index {Ω γ β : Type*} {m : MeasurableSpace Ω} [Countable γ]
    [MeasurableSpace β] {g : Ω → γ} (hg : ∀ c, MeasurableSet[m] {ω | g ω = c})
    {F : γ → Ω → β} (hF : ∀ c, Measurable[m] (F c)) :
    Measurable[m] fun ω => F (g ω) ω := by
  intro B hB
  have hset : (fun ω => F (g ω) ω) ⁻¹' B = ⋃ c, {ω | g ω = c} ∩ F c ⁻¹' B := by
    ext ω
    constructor
    · intro h
      exact Set.mem_iUnion.2 ⟨g ω, rfl, h⟩
    · intro h
      obtain ⟨c, hc, h'⟩ := Set.mem_iUnion.1 h
      simp only [Set.mem_ofPred_eq] at hc
      subst hc
      exact h'
  rw [hset]
  exact MeasurableSet.iUnion fun c => (hg c).inter (hF c hB)

/-- The level-set form of `measurable_at_index`, for codomains carrying **no**
measurable space at all.  Working with level sets rather than a `Measurable`
statement means no σ-algebra on `β` ever has to be chosen — useful when `β` is a
finite state space that one would rather not equip. -/
theorem measurableSet_at_index {Ω γ β : Type*} {m : MeasurableSpace Ω} [Countable γ]
    {g : Ω → γ} (hg : ∀ c, MeasurableSet[m] {ω | g ω = c})
    {F : γ → Ω → β} (hF : ∀ c y, MeasurableSet[m] {ω | F c ω = y}) (y : β) :
    MeasurableSet[m] {ω | F (g ω) ω = y} := by
  have hset : {ω | F (g ω) ω = y} = ⋃ c, {ω | g ω = c} ∩ {ω | F c ω = y} := by
    ext ω
    constructor
    · intro h
      exact Set.mem_iUnion.2 ⟨g ω, rfl, h⟩
    · intro h
      obtain ⟨c, hc, h'⟩ := Set.mem_iUnion.1 h
      simp only [Set.mem_ofPred_eq] at hc
      subst hc
      exact h'
  rw [hset]
  exact MeasurableSet.iUnion fun c => (hg c).inter (hF c y)

/-- **An arbitrary function of a countably-valued measurable index is
measurable.**  A countable space with measurable singletons carries the discrete
σ-algebra, so *no* measurability hypothesis on `f` is needed: the preimage
splits along the (countably many) level sets of `g`.

This is what lets a schedule indexed by a random *counter* go through with the
schedule an entirely arbitrary function: `fun ω => rate (N ω)` is measurable
purely because `ℕ` is countable, so no regularity is required of `rate`. -/
theorem measurable_comp_index {Ω γ β : Type*} {m : MeasurableSpace Ω} [Countable γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace β]
    {g : Ω → γ} (hg : Measurable[m] g) (f : γ → β) :
    Measurable[m] fun ω => f (g ω) :=
  measurable_at_index (fun c => hg (measurableSet_singleton c)) (fun _ => measurable_const)


end Arlib.Probability
