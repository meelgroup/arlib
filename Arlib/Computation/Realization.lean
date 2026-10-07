/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Charged
import Arlib.Computation.Machine

/-!
# Certified realizations of charged computations

These certificates relate an unchanged abstract computation to concrete RAM
execution. They do not reconstruct instructions from an evaluated `Charged`
value, validate the source grammar, or measure native Lean execution time.
Preconditions describe admissible represented inputs; an implementation-existence
claim additionally needs witnesses showing those inputs can be represented.
-/
namespace Arlib.Computation

universe u v

/-- Correctness and a unit-cost RAM bound on every admissible initial state.
`Post` includes any required representation and memory preservation invariants.
A certificate with an unsatisfiable `Pre` is only a vacuous conditional theorem. -/
structure Realizes {κ κₛ : Type} {α : Type u} {β : Type v} {w : ℕ}
    (p : Charged κ κₛ α) (q : RAM w β) (Pre : RamState w → Prop)
    (Post : α → β → RamState w → Prop) (budget : ℕ) : Prop where
  correct : ∀ σ, Pre σ → Post p.val (q.val σ) (q.state σ)
  steps_le : ∀ σ, Pre σ → RAM.steps CostModel.unitCost q σ ≤ budget

namespace Realizes

variable {κ κₛ : Type} {α γ : Type u} {β δ : Type v} {w : ℕ}

/-- Forward already represented values. This semantic rule is not permission to
perform arbitrary uncharged source computation in a RAM program. -/
theorem pure (a : α) (b : β) (Pre : RamState w → Prop)
    (Post : α → β → RamState w → Prop)
    (h : ∀ σ, Pre σ → Post a b σ) :
    Realizes (pure a : Charged κ κₛ α) (pure b : RAM w β) Pre Post 0 := by
  constructor
  · simpa using h
  · intro σ _
    simp

/-- Sequencing passes the first result relation, in the updated state, to the
continuation. The concrete continuation receives its concrete result, rather
than observing the abstract value at runtime. -/
theorem bind {p : Charged κ κₛ α} {q : RAM w β}
    {f : α → Charged κ κₛ γ} {g : β → RAM w δ}
    {Pre : RamState w → Prop} {Mid : α → β → RamState w → Prop}
    {Post : γ → δ → RamState w → Prop} {b₁ b₂ : ℕ}
    (hp : Realizes p q Pre Mid b₁)
    (hf : ∀ a b, Realizes (f a) (g b) (Mid a b) Post b₂) :
    Realizes (p >>= f) (q >>= g) Pre Post (b₁ + b₂) := by
  constructor
  · intro σ hσ
    simpa only [Charged.val_bind, RAM.val_bind, RAM.state_bind] using
      (hf p.val (q.val σ)).correct (q.state σ) (hp.correct σ hσ)
  · intro σ hσ
    rw [RAM.steps_bind]
    exact Nat.add_le_add (hp.steps_le σ hσ)
      ((hf p.val (q.val σ)).steps_le (q.state σ) (hp.correct σ hσ))

/-- Restrict admissible initial states, relax the result relation, or enlarge
the budget. -/
theorem consequence {p : Charged κ κₛ α} {q : RAM w β}
    {Pre Pre' : RamState w → Prop}
    {Post Post' : α → β → RamState w → Prop} {b b' : ℕ}
    (h : Realizes p q Pre Post b)
    (hpre : ∀ σ, Pre' σ → Pre σ)
    (hpost : ∀ a b σ, Post a b σ → Post' a b σ)
    (hbudget : b ≤ b') : Realizes p q Pre' Post' b' := by
  constructor
  · intro σ hσ
    exact hpost _ _ _ (h.correct σ (hpre σ hσ))
  · intro σ hσ
    exact le_trans (h.steps_le σ (hpre σ hσ)) hbudget

/-- Branch on an already obtained Boolean answer; producing the answer is
accounted for by the preceding computation. -/
theorem branch (c : Bool)
    {pt pf : Charged κ κₛ α} {qt qf : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    {bt bf : ℕ} (ht : Realizes pt qt Pre Post bt)
    (hf : Realizes pf qf Pre Post bf) :
    Realizes (if c then pt else pf) (if c then qt else qf)
      Pre Post (max bt bf) := by
  cases c
  · exact hf.consequence (fun _ h => h) (fun _ _ _ h => h) (le_max_right _ _)
  · exact ht.consequence (fun _ h => h) (fun _ _ _ h => h) (le_max_left _ _)

/-- Attach an invariant proved of the final state. Memory preservation is an
explicit additional obligation, never inferred from output correctness. -/
theorem strengthenPost {p : Charged κ κₛ α} {q : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    {budget : ℕ} (h : Realizes p q Pre Post budget)
    (F : RamState w → Prop) (hF : ∀ σ, Pre σ → F (q.state σ)) :
    Realizes p q Pre (fun a b σ => Post a b σ ∧ F σ) budget := by
  constructor
  · intro σ hσ
    exact ⟨h.correct σ hσ, hF σ hσ⟩
  · exact h.steps_le

end Realizes
end Arlib.Computation
