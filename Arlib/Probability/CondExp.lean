/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Expectation and conditional expectation over a finite probability space

We give a concrete expectation `Ex P X = ∑_ω mass(ω) · X(ω)` and prove its basic
algebra (linearity, `Ex 1 = 1`, monotonicity).

Conditional expectation `E[X | F]` is characterized by two facts:

* **Fixed-variable rule**: if `X` is fixed by `F` then
  `E[XY | F] = X · E[Y | F]`; in particular `E[X | F] = X`.
* **Tower rule**: if `F₁ ⊆ F₂` then
  `E[E[X | F₂] | F₁] = E[X | F₁]`, hence `E[E[X | F₂]] = E[X]`.

We package a conditional-expectation operator together with these two facts as
an interface `HasCondExp`.  The concrete construction over `FinProb` (via the
partition induced by `F`) satisfies this interface; we record the interface here
so that downstream results can be developed against the two facts alone.
-/
import Arlib.Probability.FinProb

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-- Expectation `Ex[X] = ∑_ω mass(ω)·X(ω)`. -/
def Ex (X : P.Ω → ℝ) : ℝ := ∑ ω, P.mass ω * X ω

@[simp] theorem Ex_const (c : ℝ) : P.Ex (fun _ => c) = c := by
  unfold Ex
  rw [← Finset.sum_mul, mul_comm]
  simp [P.mass_sum]

theorem Ex_add (X Y : P.Ω → ℝ) : P.Ex (fun ω => X ω + Y ω) = P.Ex X + P.Ex Y := by
  unfold Ex
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _; ring

theorem Ex_smul (c : ℝ) (X : P.Ω → ℝ) :
    P.Ex (fun ω => c * X ω) = c * P.Ex X := by
  unfold Ex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _; ring

theorem Ex_mono {X Y : P.Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : P.Ex X ≤ P.Ex Y := by
  unfold Ex
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (P.mass_nonneg ω)

theorem Ex_nonneg {X : P.Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ P.Ex X := by
  have := P.Ex_mono (X := fun _ => (0:ℝ)) (Y := X) h
  simpa using this

/-- `Pr[E]` equals `Ex[𝟙_E]`, linking the two viewpoints. -/
theorem Pr_eq_Ex_indicator (E : Event P) :
    P.Pr E = P.Ex (fun ω => if ω ∈ E then 1 else 0) := by
  unfold Pr Ex
  have hpt : ∀ ω, P.mass ω * (if ω ∈ E then (1 : ℝ) else 0)
      = if ω ∈ E then P.mass ω else 0 := by
    intro ω; by_cases h : ω ∈ E <;> simp [h]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω), Finset.sum_ite_mem,
    Finset.univ_inter]

end FinProb

/-- A conditional-expectation operator over `P`, indexed by a filtration type
`Filt`, satisfying the fixed-variable and tower rules.  A "sub-filtration"
relation `Sub` models `F₁ ⊆ F₂`, and `Fixed F X` models "`X` is fixed by `F`". -/
structure HasCondExp (P : FinProb) where
  Filt : Type
  Sub : Filt → Filt → Prop
  Fixed : Filt → (P.Ω → ℝ) → Prop
  cond : Filt → (P.Ω → ℝ) → (P.Ω → ℝ)
  /-- Fixed-variable rule: `E[XY | F] = X · E[Y | F]` when `X` is fixed by `F`. -/
  fixed_rule : ∀ (F : Filt) (X Y : P.Ω → ℝ), Fixed F X →
    cond F (fun ω => X ω * Y ω) = fun ω => X ω * cond F Y ω
  /-- Tower rule: `E[E[X | F₂] | F₁] = E[X | F₁]` when `F₁ ⊆ F₂`. -/
  tower : ∀ (F₁ F₂ : Filt) (X : P.Ω → ℝ), Sub F₁ F₂ →
    cond F₁ (cond F₂ X) = cond F₁ X
  /-- Taking expectation of a conditional expectation recovers the expectation. -/
  cond_Ex : ∀ (F : Filt) (X : P.Ω → ℝ), P.Ex (cond F X) = P.Ex X

/-
This interface is not merely axiomatized: `Probability/CondExpConstruction.lean`
*constructs* a `HasCondExp P` for every `FinProb P` (`FinProb.mkCondExp`) — the
partition/fiber conditional expectation `E[X | π] = (∑_{cell} mass·X)/(∑_{cell}
mass)` — and proves `fixed_rule`, `tower` and `cond_Ex` from first principles.
So the two facts above are theorems about a concrete object.
-/

end Arlib.Probability
