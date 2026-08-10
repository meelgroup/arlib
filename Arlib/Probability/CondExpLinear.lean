/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Linearity of the concrete conditional expectation

This file proves that the concrete conditional expectation `condCE` (a
mass-average over the cells of a partition) is **linear**: it commutes with
addition, scalar multiplication, and finite sums.  These are pure algebra of
`condCE` and require no further assumptions.

`condCE_sum_transport` packages the sum case directly: from a per-term identity
`E[f i | 𝓕] = g i` it derives `E[∑ᵢ f i | 𝓕] = ∑ᵢ g i`.
-/
import Arlib.Probability.CondExpConstruction

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-- `E[0 | π] = 0`. -/
theorem condCE_zero (π : P.Ω → P.Ω) : condCE P π (fun _ => 0) = fun _ => 0 := by
  funext ω
  unfold condCE
  simp

/-- **Additivity of conditional expectation:** `E[X + Y | π] = E[X | π] + E[Y | π]`. -/
theorem condCE_add (π : P.Ω → P.Ω) (X Y : P.Ω → ℝ) :
    condCE P π (fun ω => X ω + Y ω) = fun ω => condCE P π X ω + condCE P π Y ω := by
  funext ω
  unfold condCE
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω' _ => by ring)

/-- **Scalar homogeneity of conditional expectation:** `E[c·X | π] = c·E[X | π]`. -/
theorem condCE_smul (π : P.Ω → P.Ω) (c : ℝ) (X : P.Ω → ℝ) :
    condCE P π (fun ω => c * X ω) = fun ω => c * condCE P π X ω := by
  funext ω
  unfold condCE
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun ω' _ => by ring)

/-- **Subtractivity of conditional expectation:** `E[X - Y | π] = E[X | π] - E[Y | π]`. -/
theorem condCE_sub (π : P.Ω → P.Ω) (X Y : P.Ω → ℝ) :
    condCE P π (fun ω => X ω - Y ω) = fun ω => condCE P π X ω - condCE P π Y ω := by
  have h : (fun ω => X ω - Y ω) = fun ω => X ω + (-1) * Y ω := by funext ω; ring
  rw [h, condCE_add, condCE_smul]
  funext ω
  ring

/-- **Linearity over a finite index sum:**
`E[∑_{i∈s} f i | π] = ∑_{i∈s} E[f i | π]`.  This is the form used to pass the
conditional expectation through a finite sum. -/
theorem condCE_sum {ι : Type*} [DecidableEq ι] (π : P.Ω → P.Ω) (s : Finset ι)
    (f : ι → P.Ω → ℝ) :
    condCE P π (fun ω => ∑ i ∈ s, f i ω)
      = fun ω => ∑ i ∈ s, condCE P π (f i) ω := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, condCE_zero]
  | @insert i s hi ih =>
      have hstep : (fun ω => ∑ j ∈ insert i s, f j ω)
          = fun ω => f i ω + ∑ j ∈ s, f j ω := by
        funext ω; rw [Finset.sum_insert hi]
      rw [hstep, condCE_add, ih]
      funext ω
      rw [Finset.sum_insert hi]

/-- **The sum-transport reduction.**  Given the *per-term* conditional identities
`E[f i | π] = g i`, conditional expectation of the sum is the sum of the targets:
`E[∑_{i∈s} f i | π] = ∑_{i∈s} g i`. -/
theorem condCE_sum_transport {ι : Type*} [DecidableEq ι] (π : P.Ω → P.Ω) (s : Finset ι)
    (f g : ι → P.Ω → ℝ) (h : ∀ i ∈ s, condCE P π (f i) = g i) :
    condCE P π (fun ω => ∑ i ∈ s, f i ω) = fun ω => ∑ i ∈ s, g i ω := by
  rw [condCE_sum]
  funext ω
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [h i hi]

end FinProb
end Arlib.Probability
