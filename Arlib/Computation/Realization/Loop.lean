/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization
import Arlib.Computation.WordLoop

/-!
# Composing read-only word-loop realizations

This rule connects an unchanged Charged computation's proved value recurrence to
an executable word loop. Body correctness is required only at guarded indices
of admissible input states. Control work is explicit in the resulting budget.
The recurrence retains fuel: complete traversal additionally requires sufficient
fuel, as proved in `Realization.Scan`. Mutable and differently represented loop
accumulators require further relational invariant rules.
-/
namespace Arlib.Computation.Realizes

variable {κ κₛ : Type} {α : Type} {w : ℕ}

/-- A read-only loop realization, preserving the admissible input representation
and accounting for every guard, increment and initialization literal. -/
theorem readOnlyWordLoop (p : Charged κ κₛ α) (fuel : ℕ) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (spec : ℕ → α → Option α)
    (acc : α) (Pre : RamState w → Prop) (bodyBound : ℕ)
    (hwidth : 1 < 2 ^ w)
    (hvalue : p.val = wordLoopSpec spec limit.toNat fuel 0 acc)
    (hbody : ∀ σ, Pre σ → ∀ index a, index.toNat < limit.toNat →
      (body index a).val σ = spec index.toNat a)
    (hstate : ∀ index a σ, (body index a).state σ = σ)
    (hcost : ∀ index a σ, RAM.steps CostModel.unitCost (body index a) σ ≤ bodyBound) :
    Realizes p (wordRepeatWhile fuel limit body acc) Pre
      (fun a b σ => a = b ∧ Pre σ) (3 + fuel * (bodyBound + 2)) where
  correct := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · rw [val_wordRepeatWhile_eq_spec_at fuel limit body spec acc σ hwidth
        (hbody σ hσ) (fun i a _ => hstate i a σ)]
      exact hvalue
    · rw [state_wordRepeatWhile fuel limit body acc σ hstate]
      exact hσ
  steps_le := by
    intro σ _
    exact steps_wordRepeatWhile_le fuel limit body acc σ bodyBound hcost

end Arlib.Computation.Realizes
