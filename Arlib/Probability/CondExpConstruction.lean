/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A concrete conditional expectation over a finite probability space

`CondExp.lean` axiomatizes conditional expectation through the interface
`HasCondExp` (the fixed-variable and tower rules).  Here we
*construct* a conditional-expectation operator over an arbitrary `FinProb` and
**prove** it satisfies that interface — discharging the axiomatization with a
real object.

## The construction

A sub-σ-algebra of a finite space is the same data as a partition of the outcome
space.  We encode a partition by an *observable* map `π : Ω → Ω`: two outcomes
lie in the same cell iff they have the same `π`-value (the fibers of `π` are the
cells; `π` need not be idempotent, only its fibers matter).  Then

  `E[X | π](ω) = (∑_{ω' ∼ ω} mass(ω')·X(ω')) / (∑_{ω' ∼ ω} mass(ω'))`

is the average of `X` over the cell of `ω` (a `0/0 = 0` cell contributes
nothing, so no positivity hypothesis is needed).

* `Fixed π X`  — `X` is constant on cells (measurable w.r.t. `π`);
* `Sub π₁ π₂`  — `π₂` refines `π₁` (`π₁ ⊆ π₂` as σ-algebras).

Everything reduces to one lemma, `sum_measurable_mul_condCE`: *averaging
collapses* — for any `π`-measurable set `C`,
`∑_{a∈C} mass(a)·E[X|π](a) = ∑_{a∈C} mass(a)·X(a)`.  Taking `C = univ` gives the
tower-into-expectation identity `cond_Ex`; taking `C` a coarser cell gives the
tower rule.  Everything here is proved with no `sorry`.
-/
import Arlib.Probability.CondExp

namespace Arlib.Probability

open Finset

namespace FinProb

variable (P : FinProb)

/-- The cell (fiber) of `ω` under the observable `π`: all outcomes with the same
`π`-value. -/
def cell (π : P.Ω → P.Ω) (ω : P.Ω) : Finset P.Ω :=
  univ.filter (fun ω' => π ω' = π ω)

/-- Concrete conditional expectation `E[X | π]`: the mass-average of `X` over the
cell of each outcome. -/
noncomputable def condCE (π : P.Ω → P.Ω) (X : P.Ω → ℝ) : P.Ω → ℝ :=
  fun ω => (∑ ω' ∈ cell P π ω, P.mass ω' * X ω') / (∑ ω' ∈ cell P π ω, P.mass ω')

/-- `X` is fixed by `π` when it is constant on each cell. -/
def CFixed (π : P.Ω → P.Ω) (X : P.Ω → ℝ) : Prop :=
  ∀ a b, π a = π b → X a = X b

/-- `π₂` refines `π₁` (`π₁ ⊆ π₂` as σ-algebras): agreeing under `π₂` forces
agreeing under `π₁`. -/
def CSub (π₁ π₂ : P.Ω → P.Ω) : Prop :=
  ∀ a b, π₂ a = π₂ b → π₁ a = π₁ b

variable {P}

theorem mem_cell {π : P.Ω → P.Ω} {ω ω' : P.Ω} : ω' ∈ cell P π ω ↔ π ω' = π ω := by
  simp [cell]

/-- Cells depend only on the `π`-value: equal `π`-values give the same cell. -/
theorem cell_congr {π : P.Ω → P.Ω} {a b : P.Ω} (h : π a = π b) :
    cell P π a = cell P π b := by
  unfold cell; rw [h]

/-- `E[X | π]` is constant on cells. -/
theorem condCE_congr {π : P.Ω → P.Ω} (X : P.Ω → ℝ) {a b : P.Ω} (h : π a = π b) :
    condCE P π X a = condCE P π X b := by
  unfold condCE; rw [cell_congr h]

/-- **Per-cell collapse.**  The mass-weighted sum of `E[X|π]` over a cell equals
the mass-weighted sum of `X` over that cell (both equal the cell's `mass·X`
total).  The one computational core of the whole file. -/
theorem sum_cell_mul_condCE (π : P.Ω → P.Ω) (X : P.Ω → ℝ) (ω : P.Ω) :
    ∑ ω' ∈ cell P π ω, P.mass ω' * condCE P π X ω'
      = ∑ ω' ∈ cell P π ω, P.mass ω' * X ω' := by
  have hconst : ∀ ω' ∈ cell P π ω, P.mass ω' * condCE P π X ω'
      = P.mass ω' * condCE P π X ω := by
    intro ω' hω'
    rw [condCE_congr X (mem_cell.1 hω')]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
  unfold condCE
  by_cases hmk : (∑ ω' ∈ cell P π ω, P.mass ω') = 0
  · rw [hmk, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω' hω'
    have hz : P.mass ω' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => P.mass_nonneg i)).1 hmk ω' hω'
    rw [hz, zero_mul]
  · field_simp

/-- **Averaging collapses on any measurable set.**  If `C` is a union of cells
(`π`-measurable), then `∑_{a∈C} mass(a)·E[X|π](a) = ∑_{a∈C} mass(a)·X(a)`.
`cond_Ex` (take `C = univ`) and the tower rule both follow. -/
theorem sum_measurable_mul_condCE (π : P.Ω → P.Ω) (X : P.Ω → ℝ) (C : Finset P.Ω)
    (hC : ∀ a ∈ C, ∀ b, π b = π a → b ∈ C) :
    ∑ a ∈ C, P.mass a * condCE P π X a = ∑ a ∈ C, P.mass a * X a := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := C.image π) (g := π)
        (fun x hx => Finset.mem_image_of_mem π hx)
        (f := fun a => P.mass a * condCE P π X a),
      ← Finset.sum_fiberwise_of_maps_to (t := C.image π) (g := π)
        (fun x hx => Finset.mem_image_of_mem π hx)
        (f := fun a => P.mass a * X a)]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨a₀, ha₀C, ha₀k⟩ := Finset.mem_image.1 hk
  have hfib : C.filter (fun a => π a = k) = cell P π a₀ := by
    ext x
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hx⟩; rw [hx, ha₀k]
    · intro hx
      exact ⟨hC a₀ ha₀C x hx, hx.trans ha₀k⟩
  rw [hfib]
  exact sum_cell_mul_condCE π X a₀

/-- **Fixed-variable rule** for the concrete construction:
`E[XY | π] = X · E[Y | π]` when `X` is fixed by `π`. -/
theorem condCE_fixed_rule (π : P.Ω → P.Ω) (X Y : P.Ω → ℝ) (hX : CFixed P π X) :
    condCE P π (fun ω => X ω * Y ω) = fun ω => X ω * condCE P π Y ω := by
  funext ω
  unfold condCE
  have hnum : ∑ ω' ∈ cell P π ω, P.mass ω' * (X ω' * Y ω')
      = X ω * ∑ ω' ∈ cell P π ω, P.mass ω' * Y ω' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω' hω'
    rw [hX ω' ω (mem_cell.1 hω')]; ring
  rw [hnum, mul_div_assoc]

/-- **Tower into expectation:** `Ex[E[X | π]] = Ex[X]`. -/
theorem condCE_Ex (π : P.Ω → P.Ω) (X : P.Ω → ℝ) :
    P.Ex (condCE P π X) = P.Ex X := by
  unfold Ex
  exact sum_measurable_mul_condCE π X univ (fun a _ b _ => mem_univ b)

/-- **Tower rule:** for `π₂` refining `π₁`, `E[E[X | π₂] | π₁] = E[X | π₁]`. -/
theorem condCE_tower (π₁ π₂ : P.Ω → P.Ω) (X : P.Ω → ℝ) (hsub : CSub P π₁ π₂) :
    condCE P π₁ (condCE P π₂ X) = condCE P π₁ X := by
  funext ω
  unfold condCE
  congr 1
  -- Numerators agree: `cell π₁ ω` is `π₂`-measurable since `π₂` refines `π₁`.
  exact sum_measurable_mul_condCE π₂ X (cell P π₁ ω)
    (fun a ha b hb => mem_cell.2 (by
      rw [hsub b a hb]; exact mem_cell.1 ha))

variable (P) in
/-- The concrete conditional-expectation operator packaged as a `HasCondExp P`:
a real object discharging the axiomatized interface of `CondExp.lean`. -/
noncomputable def mkCondExp : HasCondExp P where
  Filt := P.Ω → P.Ω
  Sub := CSub P
  Fixed := CFixed P
  cond := condCE P
  fixed_rule := condCE_fixed_rule
  tower := condCE_tower
  cond_Ex := condCE_Ex

end FinProb
end Arlib.Probability
