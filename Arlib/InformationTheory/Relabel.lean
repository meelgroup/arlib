/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Defs

/-!
# Entropy is a relabelling invariant

Entropy depends on a random variable only through the *partition of the sample
space* it induces, never on the names of the values. This file makes that
precise: composing with an injection on the value space leaves `H` unchanged.

The content is bookkeeping, but it is load-bearing. The submodularity and chain
rule arguments downstream constantly need to move between the groupings
`(X, (Y, Z))`, `((X, Y), Z)` and `(Y, X)`, and those are exactly relabellings by
`Equiv.prodAssoc` and `Prod.swap`. Proving the general statement once means those
steps are one rewrite rather than a fresh double-sum manipulation each time.

## Main results

* `Arlib.InformationTheory.dist_comp_of_injective` — the law pushes forward.
* `Arlib.InformationTheory.H_comp_of_injective` — the invariance itself.
* `Arlib.InformationTheory.H_comp_equiv` — the same for an equivalence.
* `Arlib.InformationTheory.H₂_comm` — joint entropy is symmetric.
* `Arlib.InformationTheory.H_pair_assoc` — regrouping a triple.
* `Arlib.InformationTheory.H_pair_self_comp` — `(X, f ∘ X)` carries no more
  information than `X`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Pushing a law forward along an injection -/

/-- Pushing a law forward along an injection: the law of `f ∘ X` at `f a` is the
law of `X` at `a`, and it vanishes off the range of `f`. -/
theorem dist_comp_of_injective {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) {f : α → β}
    (hf : Function.Injective f) (a : α) :
    dist P (fun ω => f (X ω)) (f a) = dist P X a := by
  simp only [dist]
  exact Finset.sum_congr rfl fun ω _ => by simp only [hf.eq_iff]

/-- Off the image of `f` the pushed-forward law is zero: no sample point can be
sent there. -/
private theorem dist_comp_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) {f : α → β} {b : β}
    (hb : b ∉ Finset.univ.image f) :
    dist P (fun ω => f (X ω)) b = 0 := by
  simp only [dist]
  refine Finset.sum_eq_zero fun ω _ => ?_
  have hne : f (X ω) ≠ b := fun h =>
    hb (Finset.mem_image.mpr ⟨X ω, Finset.mem_univ _, h⟩)
  simp [hne]

/-! ### Invariance of entropy -/

/-- **Entropy is a relabelling invariant.** Composing with an injection on the
value space does not change entropy. -/
theorem H_comp_of_injective {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) {f : α → β}
    (hf : Function.Injective f) :
    H P (fun ω => f (X ω)) = H P X := by
  have hsub : ∑ b : β, Real.negMulLog (dist P (fun ω => f (X ω)) b)
      = ∑ b ∈ Finset.univ.image f,
          Real.negMulLog (dist P (fun ω => f (X ω)) b) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro b _ hb
    rw [dist_comp_eq_zero X hb, Real.negMulLog_zero]
  rw [H_def, H_def, hsub,
    Finset.sum_image (fun x _ y _ h => hf h)]
  exact Finset.sum_congr rfl fun a _ => by rw [dist_comp_of_injective X hf a]

/-- Entropy transported along an equivalence of value spaces. -/
theorem H_comp_equiv {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {P : FinProb} (X : P.Ω → α) (e : α ≃ β) :
    H P (fun ω => e (X ω)) = H P X :=
  H_comp_of_injective X e.injective

/-! ### The three relabellings used downstream -/

/-- Joint entropy is symmetric. -/
theorem H₂_comm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    H₂ P X Y = H₂ P Y X := by
  have hfun : (fun ω => Prod.swap (pair X Y ω)) = pair Y X := rfl
  rw [H₂_def, H₂_def, ← hfun]
  exact (H_comp_of_injective (pair X Y) Prod.swap_injective).symm

/-- Regrouping a triple: `(X, (Y, Z))` and `((X, Y), Z)` have the same entropy. -/
theorem H_pair_assoc {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    H P (pair X (pair Y Z)) = H P (pair (pair X Y) Z) := by
  have hfun :
      (fun ω => (Equiv.prodAssoc α β γ).symm (pair X (pair Y Z) ω))
        = pair (pair X Y) Z := rfl
  rw [← hfun]
  exact (H_comp_equiv (pair X (pair Y Z)) (Equiv.prodAssoc α β γ).symm).symm

/-- Duplicating a coordinate does not change entropy: `(X, f ∘ X)` carries the
same information as `X`. Used for the data-processing inequality. -/
theorem H_pair_self_comp {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} (X : P.Ω → α) (f : α → β) :
    H P (pair X (fun ω => f (X ω))) = H P X := by
  have hinj : Function.Injective (fun a : α => (a, f a)) :=
    fun _ _ h => congrArg Prod.fst h
  have h := H_comp_of_injective (f := fun a : α => (a, f a)) X hinj
  exact h

end InformationTheory
end Arlib
