/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Reindexing and pushing forward a finite product law

Two structural identities for the product spaces of `Arlib.prodSpace`, both of
the "same measure, different coordinates" kind, and both proved by a single
change of summation variable.

* **Currying** (`Ex_prod_curry`, `Pr_prod_curry`).  A product indexed by a
  *pair* type `ι × J` is the `ι`-indexed product of the `J`-indexed product:
  refining every coordinate into a block of `J` coordinates does not change the
  law.  The change of variable is `Equiv.curry`, and the masses match by
  `Fintype.prod_prod_type`.
* **Coordinatewise pushforward** (`Ex_prod_map`, `Pr_prod_map`).  If `f : Y → X`
  pushes `μY` forward to `μX` *one coordinate at a time* — i.e.
  `∑_{y : f y = x} μY y = μX x` — then the `ι`-indexed product of `μY` pushes
  forward to the `ι`-indexed product of `μX` under `g ↦ f ∘ g`.  The proof sums
  over the fibres of `g ↦ f ∘ g`, which are exactly the boxes
  `∏ᵢ {y : f y = ω i}`, and multiplies the per-coordinate identities together
  with `Finset.prod_univ_sum`.

Together they let a statement proved in a *refined* model (each coordinate split
into a block, each coordinate resolved into finer randomness) be transported
verbatim to the coarse model it refines.  See `Arlib.Probability.BinaryLevel`
for the motivating instance.

Also proved here is the single-coordinate marginal in `Pr` form
(`Pr_prod_coord`).  Everything is `sorry`-free.
-/
import Arlib.Probability.IIDProduct

namespace Arlib

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The product law on tuples -/

/-- The product law on tuples `J → X` induced by a law `μ` on `X`. -/
def piMass {J X : Type} [Fintype J] (μ : X → ℝ) (c : J → X) : ℝ := ∏ j, μ (c j)

variable {J X Y : Type} [Fintype J] [DecidableEq J] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

omit [DecidableEq J] [Fintype X] [DecidableEq X] in
theorem piMass_nonneg (μ : X → ℝ) (h0 : ∀ x, 0 ≤ μ x) (c : J → X) : 0 ≤ piMass μ c :=
  Finset.prod_nonneg (fun j _ => h0 (c j))

theorem piMass_sum (μ : X → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1) :
    ∑ c : J → X, piMass μ c = 1 := by
  have h := (prodSpace (fun _ : J => μ) (fun _ x => h0 x)
    (fun _ => h1)).toFinProb.mass_sum
  simpa [piMass] using h

/-! ## Currying: a product over `ι × J` is an `ι`-product of `J`-products -/

/-- **Currying a product law.**  Sampling one `X` for every pair `(i, j)` is the
same as sampling, for every `i`, a whole tuple `J → X` from the product law
`piMass μ`. -/
theorem Ex_prod_curry (μ : X → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1)
    (F : (ι × J → X) → ℝ) :
    (prodSpace (fun _ : ι × J => μ) (fun _ x => h0 x) (fun _ => h1)).toFinProb.Ex F
      = (prodSpace (fun _ : ι => piMass (J := J) μ) (fun _ c => piMass_nonneg μ h0 c)
          (fun _ => piMass_sum μ h0 h1)).toFinProb.Ex
          (fun ω => F (fun p => ω p.1 p.2)) := by
  have key : (∑ g : ι × J → X, (∏ p : ι × J, μ (g p)) * F g)
      = ∑ ω : ι → (J → X), (∏ i, piMass μ (ω i)) * F (fun p => ω p.1 p.2) := by
    rw [← Equiv.sum_comp (Equiv.curry ι J X).symm
          (fun g : ι × J → X => (∏ p : ι × J, μ (g p)) * F g)]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have hg : (Equiv.curry ι J X).symm ω = fun p : ι × J => ω p.1 p.2 := rfl
    rw [hg]
    congr 1
    rw [Fintype.prod_prod_type]
    rfl
  simp only [FinProb.Ex, prodSpace_mass]
  exact key

/-- The `Pr` form of `Ex_prod_curry`: an event of the `ι × J`-indexed product
has the same probability as its curried version in the `ι`-indexed product of
`J`-tuples. -/
theorem Pr_prod_curry (μ : X → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1)
    (A : Finset (ι × J → X)) :
    (prodSpace (fun _ : ι × J => μ) (fun _ x => h0 x) (fun _ => h1)).toFinProb.Pr A
      = (prodSpace (fun _ : ι => piMass (J := J) μ) (fun _ c => piMass_nonneg μ h0 c)
          (fun _ => piMass_sum μ h0 h1)).toFinProb.Pr
          (Finset.univ.filter fun ω => (fun p : ι × J => ω p.1 p.2) ∈ A) := by
  rw [FinProb.Pr_eq_Ex_indicator, FinProb.Pr_eq_Ex_indicator]
  refine Eq.trans (Ex_prod_curry μ h0 h1 _) ?_
  congr 1
  funext ω
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ω, h1⟩) h2
  · exact absurd (Finset.mem_filter.1 h3).2 h1
  · rfl

/-! ## Coordinatewise pushforward -/

/-- **The product of a pushforward is the pushforward of the product.**  If
`f : Y → X` carries `μY` to `μX` coordinatewise (`hpush`), then averaging a
function of `ι` coordinates over the `μX`-product equals averaging its pullback
`g ↦ F (f ∘ g)` over the `μY`-product.

The proof groups the `Y`-sum by the fibres of `g ↦ f ∘ g`; a fibre over `ω` is
the box `∏ᵢ {y : f y = ω i}`, and `Finset.prod_univ_sum` turns the product of
the `ι` per-coordinate identities into the sum over that box. -/
theorem Ex_prod_map (μX : X → ℝ) (hX0 : ∀ x, 0 ≤ μX x) (hX1 : ∑ x, μX x = 1)
    (μY : Y → ℝ) (hY0 : ∀ y, 0 ≤ μY y) (hY1 : ∑ y, μY y = 1) (f : Y → X)
    (hpush : ∀ x, (∑ y ∈ Finset.univ.filter fun y => f y = x, μY y) = μX x)
    (F : (ι → X) → ℝ) :
    (prodSpace (fun _ : ι => μX) (fun _ x => hX0 x) (fun _ => hX1)).toFinProb.Ex F
      = (prodSpace (fun _ : ι => μY) (fun _ y => hY0 y) (fun _ => hY1)).toFinProb.Ex
          (fun g => F (fun i => f (g i))) := by
  have key : (∑ g : ι → Y, (∏ i, μY (g i)) * F (fun i => f (g i)))
      = ∑ ω : ι → X, (∏ i, μX (ω i)) * F ω := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (ι → Y)) (fun g i => f (g i))
          (fun g => (∏ i, μY (g i)) * F (fun i => f (g i)))]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have hval : ∀ g ∈ (Finset.univ.filter fun g : ι → Y => (fun i => f (g i)) = ω),
        (∏ i, μY (g i)) * F (fun i => f (g i)) = (∏ i, μY (g i)) * F ω := by
      intro g hg
      rw [(Finset.mem_filter.1 hg).2]
    have hfib : (Finset.univ.filter fun g : ι → Y => (fun i => f (g i)) = ω)
        = Fintype.piFinset (fun i => Finset.univ.filter fun y => f y = ω i) := by
      ext g
      simp [Fintype.mem_piFinset, funext_iff]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, hfib]
    congr 1
    rw [← Finset.prod_univ_sum]
    exact Finset.prod_congr rfl (fun i _ => hpush (ω i))
  simp only [FinProb.Ex, prodSpace_mass]
  exact key.symm

/-- The `Pr` form of `Ex_prod_map`: an event `A` of the coarse product has the
same probability as its preimage under the coordinatewise map `g ↦ f ∘ g`. -/
theorem Pr_prod_map (μX : X → ℝ) (hX0 : ∀ x, 0 ≤ μX x) (hX1 : ∑ x, μX x = 1)
    (μY : Y → ℝ) (hY0 : ∀ y, 0 ≤ μY y) (hY1 : ∑ y, μY y = 1) (f : Y → X)
    (hpush : ∀ x, (∑ y ∈ Finset.univ.filter fun y => f y = x, μY y) = μX x)
    (A : Finset (ι → X)) :
    (prodSpace (fun _ : ι => μX) (fun _ x => hX0 x) (fun _ => hX1)).toFinProb.Pr A
      = (prodSpace (fun _ : ι => μY) (fun _ y => hY0 y) (fun _ => hY1)).toFinProb.Pr
          (Finset.univ.filter fun g => (fun i => f (g i)) ∈ A) := by
  rw [FinProb.Pr_eq_Ex_indicator, FinProb.Pr_eq_Ex_indicator]
  refine Eq.trans (Ex_prod_map μX hX0 hX1 μY hY0 hY1 f hpush _) ?_
  congr 1
  funext g
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ g, h1⟩) h2
  · exact absurd (Finset.mem_filter.1 h3).2 h1
  · rfl

/-! ## The single-coordinate marginal -/

/-- **The marginal law of one coordinate**, in `Pr` form: the `i`-th coordinate
of the product has law `μ`. -/
theorem Pr_prod_coord (μ : X → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1)
    (i : ι) (S : Finset X) :
    (prodSpace (fun _ : ι => μ) (fun _ x => h0 x) (fun _ => h1)).toFinProb.Pr
        (Finset.univ.filter fun ω => ω i ∈ S) = ∑ x ∈ S, μ x := by
  have h2 : (prodSpace (fun _ : ι => μ) (fun _ x => h0 x) (fun _ => h1)).toFinProb.Ex
      (fun ω => (fun x => if x ∈ S then (1 : ℝ) else 0) (ω i)) = ∑ x ∈ S, μ x := by
    rw [Ex_apply (fun _ : ι => μ) (fun _ x => h0 x) (fun _ => h1) i
      (fun x => if x ∈ S then (1 : ℝ) else 0)]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => by
      show μ x * (if x ∈ S then (1 : ℝ) else 0) = if x ∈ S then μ x else 0
      by_cases hx : x ∈ S <;> simp [hx])]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [FinProb.Pr_eq_Ex_indicator]
  refine Eq.trans ?_ h2
  congr 1
  funext ω
  show _ = (if ω i ∈ S then (1 : ℝ) else 0)
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (Finset.mem_filter.1 h1).2 h2
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ω, h3⟩) h1
  · rfl

end Arlib
