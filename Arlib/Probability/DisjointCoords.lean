/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Events reading pairwise-disjoint blocks of coordinates are independent

For a product space `prodSpace μ` (outcomes `ω : ι → X`, `mass ω = ∏ j, μ j (ω j)`),
an event that only *reads* the coordinates in a block `C ⊆ ι` is independent of an
event that only reads a block disjoint from `C`.  Iterating over a family of
pairwise-disjoint blocks:

  `Pr[⋂_{a ∈ T} E a] = ∏_{a ∈ T} Pr[E a]`      when `E a` reads only `C a`, `C` disjoint.

## Why this file and not `ProductSpace.CoinSpace.Ex_prod_of_disjoint`

`CondExpProd.Ex_prod_of_disjoint` proves the same factorization for a general
`CoinSpace`, but it goes through *conditional expectations*, so it needs every coin
mass to be **strictly positive** (`hpos : ∀ i c, 0 < C.coinMass i c`) in order to
condition.  Sampling laws supported on a proper subset of `X` — e.g. a renormalized
oracle law that is `0` off its support — do not satisfy that, and the hypothesis is
not removable from that proof.

The proof here is elementary and needs **no positivity at all**: only
`IIDProduct.Ex_prod_apply` (the coordinate-wise factorization of the product mass)
and a splice/fiber argument.

## The argument

* `Pr_prodSpace_cylinder` — the mass of a cylinder:
  `Pr[∀ j ∈ C, ω j = z j] = ∏_{j ∈ C} μ j (z j)`.  This is `Ex_prod_apply` applied to
  the coordinate indicators `f j x = 𝟙[x = z j]`.
* `Pr_prodSpace_and_of_disjoint` — the two-event case.  Consider the *splice* map
  `patchOn C σ τ`, which reads `C` off `σ` and everything else off `τ`.  It maps
  `{P} × {Q}` into `{P ∧ Q}` (the splice agrees with `σ` on `C ⊇ dep P` and with `τ`
  off `C ⊇ dep Q`), and its fiber over `ω` is exactly the product of the two
  complementary cylinders through `ω`, whose masses multiply back to `mass ω` by
  `Finset.prod_sdiff`.  Summing fiberwise turns `Pr[P]·Pr[Q]` into `Pr[P ∧ Q]`.
* `Pr_prodSpace_iInter_of_disjoint` — induction on `T`, splitting off one block `C a`
  against the union `⋃_{b ∈ T} C b` of the others.

## The expectation form

`Ex_prodSpace_mul_of_disjoint` / `Ex_prodSpace_prod_of_disjoint` run the same argument on
*random variables*:

  `E[∏_{a ∈ T} f a] = ∏_{a ∈ T} E[f a]`      when `f a` reads only `C a`, `C` disjoint.

Again with **no positivity** on `μ`, and with no sign hypothesis on the `f a`.  The two
versions share `sum_mass_mul_cylinder_pair`, the fiber-mass computation; the expectation
version is the shorter of the two, since the splice map is defined on all of `Ω × Ω` and
there is no event bookkeeping.  Unlike the `Pr` statements, the `Ex` statements contain no
`Finset.filter`, hence carry no `Decidable` instances for a use site to mismatch on.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.IIDProduct

namespace Arlib

open scoped BigOperators
open Finset FinProb

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-! ## Cylinders -/

/-- **The mass of a cylinder.**  Prescribing the coordinates in `C` to agree with a
reference point `z` has probability `∏_{j ∈ C} μ j (z j)`; the coordinates outside
`C` are free and average away.  No positivity hypothesis. -/
theorem Pr_prodSpace_cylinder (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (C : Finset ι) (z : ι → X) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => ∀ j ∈ C, ω j = z j)
      = ∏ j ∈ C, μ j (z j) := by
  classical
  set f : ι → X → ℝ := fun j x => if x = z j then (1 : ℝ) else 0 with hf
  have hone : ∀ ω : ι → X,
      (∀ j ∈ C, ω j = z j) → (∏ j ∈ C, f j (ω j)) = 1 := by
    intro ω hω
    refine Finset.prod_eq_one ?_
    intro j hj
    simp only [hf, if_pos (hω j hj)]
  have hzero : ∀ ω : ι → X,
      ¬ (∀ j ∈ C, ω j = z j) → (∏ j ∈ C, f j (ω j)) = 0 := by
    intro ω hω
    push_neg at hω
    obtain ⟨j, hj, hne⟩ := hω
    refine Finset.prod_eq_zero hj ?_
    simp only [hf, if_neg hne]
  have step1 : (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => ∀ j ∈ C, ω j = z j)
      = (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ j ∈ C, f j (ω j)) := by
    unfold FinProb.Pr FinProb.Ex
    refine Eq.trans (Finset.sum_congr rfl ?_)
      (Finset.sum_subset (Finset.filter_subset _ _) ?_)
    · intro ω hω
      rw [Finset.mem_filter] at hω
      dsimp only
      rw [hone ω hω.2, mul_one]
    · intro ω _ hω
      rw [Finset.mem_filter] at hω
      dsimp only
      rw [hzero ω (fun h => hω ⟨Finset.mem_univ _, h⟩), mul_zero]
  rw [step1, Ex_prod_apply μ h0 h1 C f]
  refine Finset.prod_congr rfl ?_
  intro j _
  simp only [hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_pos]

/-! ## Splicing two outcomes along a block -/

/-- **The splice.**  `patchOn C σ τ` reads the coordinates in `C` off `σ` and all the
others off `τ`. -/
def patchOn (C : Finset ι) (σ τ : ι → X) : ι → X := fun j => if j ∈ C then σ j else τ j

omit [Fintype ι] [Fintype X] [DecidableEq X] in
@[simp] theorem patchOn_of_mem (C : Finset ι) (σ τ : ι → X) {j : ι} (hj : j ∈ C) :
    patchOn C σ τ j = σ j := if_pos hj

omit [Fintype ι] [Fintype X] [DecidableEq X] in
@[simp] theorem patchOn_of_not_mem (C : Finset ι) (σ τ : ι → X) {j : ι} (hj : j ∉ C) :
    patchOn C σ τ j = τ j := if_neg hj

/-- **The fiber of the splice carries exactly the mass of `ω`.**

The pairs `(σ, τ)` with `patchOn C σ τ = ω` are exactly the pairs in which `σ` runs over
the cylinder that fixes the coordinates in `C` to those of `ω` and `τ` runs over the
complementary cylinder.  Their masses multiply back to `mass ω`, because the two cylinder
masses are the two halves `∏_{j ∈ C} μ j (ω j)` and `∏_{j ∉ C} μ j (ω j)` of the product
`mass ω = ∏_j μ j (ω j)` (`Finset.prod_sdiff`).

This is the computational core shared by the probability and the expectation versions of
the disjoint-block independence statements below. -/
theorem sum_mass_mul_cylinder_pair (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (C : Finset ι) (ω : ι → X) :
    (∑ p ∈ (Finset.univ.filter fun σ : (prodSpace μ h0 h1).toFinProb.Ω => ∀ j ∈ C, σ j = ω j)
        ×ˢ (Finset.univ.filter fun τ : (prodSpace μ h0 h1).toFinProb.Ω =>
              ∀ j ∈ Finset.univ \ C, τ j = ω j),
        (prodSpace μ h0 h1).toFinProb.mass p.1 * (prodSpace μ h0 h1).toFinProb.mass p.2)
      = (prodSpace μ h0 h1).toFinProb.mass ω := by
  rw [Finset.sum_product]
  have hsplit : ∀ σ : (prodSpace μ h0 h1).toFinProb.Ω,
      (∑ τ ∈ (Finset.univ.filter fun τ : (prodSpace μ h0 h1).toFinProb.Ω =>
            ∀ j ∈ Finset.univ \ C, τ j = ω j),
        (prodSpace μ h0 h1).toFinProb.mass σ * (prodSpace μ h0 h1).toFinProb.mass τ)
      = (prodSpace μ h0 h1).toFinProb.mass σ * ∏ j ∈ Finset.univ \ C, μ j (ω j) := by
    intro σ
    rw [← Finset.mul_sum]
    congr 1
    exact Pr_prodSpace_cylinder μ h0 h1 (Finset.univ \ C) ω
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, ← Finset.sum_mul]
  have hC' : (∑ σ ∈ (Finset.univ.filter fun σ : (prodSpace μ h0 h1).toFinProb.Ω =>
        ∀ j ∈ C, σ j = ω j), (prodSpace μ h0 h1).toFinProb.mass σ)
      = ∏ j ∈ C, μ j (ω j) := Pr_prodSpace_cylinder μ h0 h1 C ω
  rw [hC', mul_comm, Finset.prod_sdiff (Finset.subset_univ C)]
  rfl

/-! ## Two events on disjoint blocks -/

/-- **Two events reading disjoint blocks of coordinates are independent.**

`P` reads only the coordinates in `C` (`hP`), `Q` reads only those in `D` (`hQ`), and
`C`, `D` are disjoint.  Then `Pr[P ∧ Q] = Pr[P] · Pr[Q]`.

There is **no positivity hypothesis** on `μ`: coordinates may well have atoms of mass
zero.  The proof splices a `P`-outcome and a `Q`-outcome along `C` and sums over the
fibers of the splice map. -/
theorem Pr_prodSpace_and_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {C D : Finset ι} (hCD : Disjoint C D)
    (P Q : (ι → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ ω ω' : ι → X, (∀ k ∈ C, ω k = ω' k) → (P ω ↔ P ω'))
    (hQ : ∀ ω ω' : ι → X, (∀ k ∈ D, ω k = ω' k) → (Q ω ↔ Q ω')) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω)
      = (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
        * (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω) := by
  classical
  -- `D` avoids `C`
  have hDC : ∀ k ∈ D, k ∉ C := by
    intro k hk hkC
    exact (Finset.disjoint_left.mp hCD) hkC hk
  -- the splice maps the product of the two events into their intersection
  have hmaps : ∀ p ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
        ×ˢ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω),
      patchOn C p.1 p.2 ∈
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact (hP (patchOn C p.1 p.2) p.1 (fun k hk => patchOn_of_mem C p.1 p.2 hk)).mpr hp.1.2
    · exact (hQ (patchOn C p.1 p.2) p.2
        (fun k hk => patchOn_of_not_mem C p.1 p.2 (hDC k hk))).mpr hp.2.2
  -- the fiber of the splice over `ω` is the product of the two complementary cylinders
  have hfiber : ∀ ω ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω),
      (((Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
          ×ˢ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω)).filter
        fun p => patchOn C p.1 p.2 = ω)
      = (Finset.univ.filter fun σ : (prodSpace μ h0 h1).toFinProb.Ω => ∀ j ∈ C, σ j = ω j)
          ×ˢ (Finset.univ.filter fun τ : (prodSpace μ h0 h1).toFinProb.Ω =>
                ∀ j ∈ Finset.univ \ C, τ j = ω j) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    ext p
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, -⟩, hpatch⟩
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩
      · intro j hj
        have := congrFun hpatch j
        rwa [patchOn_of_mem C p.1 p.2 hj] at this
      · intro j hj
        rw [Finset.mem_sdiff] at hj
        have := congrFun hpatch j
        rwa [patchOn_of_not_mem C p.1 p.2 hj.2] at this
    · rintro ⟨⟨-, h1'⟩, ⟨-, h2'⟩⟩
      have hpatch : patchOn C p.1 p.2 = ω := by
        funext j
        by_cases hj : j ∈ C
        · rw [patchOn_of_mem C p.1 p.2 hj]; exact h1' j hj
        · rw [patchOn_of_not_mem C p.1 p.2 hj]
          exact h2' j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
      refine ⟨⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩, hpatch⟩
      · exact (hP p.1 ω (fun k hk => h1' k hk)).mpr hω.2.1
      · exact (hQ p.2 ω (fun k hk => h2' k
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hDC k hk⟩))).mpr hω.2.2
  -- the fiber sum recovers the mass of `ω`
  have hfibersum : ∀ ω ∈ (Finset.univ.filter
        fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω),
      (∑ p ∈ (((Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
            ×ˢ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω)).filter
          fun p => patchOn C p.1 p.2 = ω),
        (prodSpace μ h0 h1).toFinProb.mass p.1 * (prodSpace μ h0 h1).toFinProb.mass p.2)
      = (prodSpace μ h0 h1).toFinProb.mass ω := by
    intro ω hω
    rw [hfiber ω hω]
    exact sum_mass_mul_cylinder_pair μ h0 h1 C ω
  -- assemble
  calc (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω)
      = ∑ ω ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω),
          (prodSpace μ h0 h1).toFinProb.mass ω := rfl
    _ = ∑ ω ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω),
          ∑ p ∈ (((Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
              ×ˢ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω)).filter
            fun p => patchOn C p.1 p.2 = ω),
          (prodSpace μ h0 h1).toFinProb.mass p.1 * (prodSpace μ h0 h1).toFinProb.mass p.2 :=
        (Finset.sum_congr rfl hfibersum).symm
    _ = ∑ p ∈ ((Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
            ×ˢ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω)),
          (prodSpace μ h0 h1).toFinProb.mass p.1 * (prodSpace μ h0 h1).toFinProb.mass p.2 :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = (∑ σ ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω),
            (prodSpace μ h0 h1).toFinProb.mass σ)
          * ∑ τ ∈ (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω),
            (prodSpace μ h0 h1).toFinProb.mass τ := by
        rw [Finset.sum_product, Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
    _ = (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
        * (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω) := rfl

/-! ## A family of events on pairwise-disjoint blocks -/

/-- **Events reading pairwise-disjoint blocks of coordinates are independent.**

`P a` reads only the coordinates in the block `C a` (`hdep`), and the blocks are
pairwise disjoint (`hC`).  Then for every finite index set `T`,

  `Pr[∀ a ∈ T, P a ω] = ∏_{a ∈ T} Pr[P a]`.

**No positivity hypothesis** on `μ`: the coordinate laws may vanish anywhere. -/
theorem Pr_prodSpace_iInter_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {κ : Type*} [DecidableEq κ]
    (C : κ → Finset ι) (hC : ∀ a b, a ≠ b → Disjoint (C a) (C b))
    (P : κ → (ι → X) → Prop) [∀ a, DecidablePred (P a)]
    (hdep : ∀ a, ∀ ω ω' : ι → X, (∀ k ∈ C a, ω k = ω' k) → (P a ω ↔ P a ω'))
    (T : Finset κ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => ∀ a ∈ T, P a ω)
      = ∏ a ∈ T, (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P a ω) := by
  induction T using Finset.induction_on with
  | empty =>
      have hev : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            ∀ a ∈ (∅ : Finset κ), P a ω) = Finset.univ := by
        refine Finset.filter_true_of_mem ?_
        intro ω _ a ha
        exact absurd ha (Finset.not_mem_empty a)
      rw [hev, Finset.prod_empty, FinProb.Pr_univ]
  | @insert a T ha ih =>
      have hev : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            ∀ b ∈ insert a T, P b ω)
          = (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            P a ω ∧ ∀ b ∈ T, P b ω) := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert]
      have hdisj : Disjoint (C a) (T.biUnion C) := by
        rw [Finset.disjoint_biUnion_right]
        intro b hb
        exact hC a b (fun hab => ha (hab ▸ hb))
      have hQdep : ∀ ω ω' : ι → X, (∀ k ∈ T.biUnion C, ω k = ω' k) →
          ((∀ b ∈ T, P b ω) ↔ ∀ b ∈ T, P b ω') := by
        intro ω ω' hagree
        constructor
        · intro h b hb
          exact (hdep b ω ω' (fun k hk =>
            hagree k (Finset.mem_biUnion.mpr ⟨b, hb, hk⟩))).mp (h b hb)
        · intro h b hb
          exact (hdep b ω ω' (fun k hk =>
            hagree k (Finset.mem_biUnion.mpr ⟨b, hb, hk⟩))).mpr (h b hb)
      rw [hev, Finset.prod_insert ha,
        Pr_prodSpace_and_of_disjoint μ h0 h1 hdisj (P a) (fun ω => ∀ b ∈ T, P b ω)
          (hdep a) hQdep, ih]

/-- The two-event corollary of `Pr_prodSpace_iInter_of_disjoint`, stated directly in
terms of the two blocks — this is `Pr_prodSpace_and_of_disjoint` under its more
memorable name. -/
theorem Pr_prodSpace_indep_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {C D : Finset ι} (hCD : Disjoint C D)
    (P Q : (ι → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ ω ω' : ι → X, (∀ k ∈ C, ω k = ω' k) → (P ω ↔ P ω'))
    (hQ : ∀ ω ω' : ι → X, (∀ k ∈ D, ω k = ω' k) → (Q ω ↔ Q ω')) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω ∧ Q ω)
      = (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => P ω)
        * (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω => Q ω) :=
  Pr_prodSpace_and_of_disjoint μ h0 h1 hCD P Q hP hQ

/-! ## The "block of coordinate conditions" form

The shape a caller usually has: the `a`-th event is a conjunction of one condition per
coordinate of a block `R a`, the blocks being pairwise disjoint.

**Do not** be tempted to generalise this to `p a r (ω (idx a r))` for a reindexing
`idx : κ → ρ → ι`.  Such a statement is provable (the proof below goes through
verbatim) but *unusable*: at a use site the `Decidable` instance inside
`Finset.filter` comes out as `… (ω (idx a r))` on the lemma side and `… (ω r)` on the
goal side, and the resulting instance-level defeq check sends `whnf` into
`Finset.univ` on the function type `ι → X`, which does not terminate in practice.
Keeping the coordinate literal keeps the two instance terms syntactically equal. -/

/-- **Blocks of coordinate conditions are independent.**  Each event
`E a = {ω : ∀ r ∈ R a, p a r (ω r)}` reads only the coordinates in `R a`; if the `R a`
are pairwise disjoint the events are independent:

  `Pr[∀ a ∈ T, ∀ r ∈ R a, p a r (ω r)] = ∏_{a ∈ T} Pr[∀ r ∈ R a, p a r (ω r)]`.

**No positivity hypothesis** on `μ`. -/
theorem Pr_prodSpace_iInter_forall_coord_of_disjoint (μ : ι → X → ℝ)
    (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)
    {κ : Type*} [DecidableEq κ] (R : κ → Finset ι)
    (hR : ∀ a b, a ≠ b → Disjoint (R a) (R b))
    (p : κ → ι → X → Prop) [∀ a r, DecidablePred (p a r)]
    (T : Finset κ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
          ∀ a ∈ T, ∀ r ∈ R a, p a r (ω r))
      = ∏ a ∈ T, (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            ∀ r ∈ R a, p a r (ω r)) := by
  refine Pr_prodSpace_iInter_of_disjoint μ h0 h1 R hR
    (fun a ω => ∀ r ∈ R a, p a r (ω r)) ?_ T
  intro a ω ω' hagree
  constructor
  · intro h r hr
    rw [← hagree r hr]
    exact h r hr
  · intro h r hr
    rw [hagree r hr]
    exact h r hr

/-! ## The expectation form

The same splice/fiber argument, run on *random variables* rather than events.  It is in
fact shorter than the event version: the splice map is defined on all of `Ω × Ω` (no event
bookkeeping, no `maps_to` side condition beyond `mem_univ`), and the fiber sum is
`sum_mass_mul_cylinder_pair` verbatim.

Note there are **no filters** in these statements, so no `Decidable` instances can leak
into them and there is nothing for a use site to mismatch on. -/

/-- **Two random variables reading disjoint blocks of coordinates are independent.**

`f` reads only the coordinates in `C` (`hf`), `g` only those in `D` (`hg`), and `C`, `D`
are disjoint.  Then `E[f · g] = E[f] · E[g]`.

**No positivity hypothesis** on `μ` and **no sign hypothesis** on `f`, `g`. -/
theorem Ex_prodSpace_mul_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {C D : Finset ι} (hCD : Disjoint C D)
    (f g : (ι → X) → ℝ)
    (hf : ∀ ω ω' : ι → X, (∀ k ∈ C, ω k = ω' k) → f ω = f ω')
    (hg : ∀ ω ω' : ι → X, (∀ k ∈ D, ω k = ω' k) → g ω = g ω') :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => f ω * g ω)
      = (prodSpace μ h0 h1).toFinProb.Ex f * (prodSpace μ h0 h1).toFinProb.Ex g := by
  -- `D` avoids `C`
  have hDC : ∀ k ∈ D, k ∉ C := by
    intro k hk hkC
    exact (Finset.disjoint_left.mp hCD) hkC hk
  -- the fiber of the splice over `ω` is the product of the two complementary cylinders
  have hfiber : ∀ ω : (prodSpace μ h0 h1).toFinProb.Ω,
      (Finset.univ.filter
          fun p : (prodSpace μ h0 h1).toFinProb.Ω × (prodSpace μ h0 h1).toFinProb.Ω =>
            patchOn C p.1 p.2 = ω)
      = (Finset.univ.filter fun σ : (prodSpace μ h0 h1).toFinProb.Ω => ∀ j ∈ C, σ j = ω j)
          ×ˢ (Finset.univ.filter fun τ : (prodSpace μ h0 h1).toFinProb.Ω =>
                ∀ j ∈ Finset.univ \ C, τ j = ω j) := by
    intro ω
    ext p
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨-, hpatch⟩
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩
      · intro j hj
        have := congrFun hpatch j
        rwa [patchOn_of_mem C p.1 p.2 hj] at this
      · intro j hj
        rw [Finset.mem_sdiff] at hj
        have := congrFun hpatch j
        rwa [patchOn_of_not_mem C p.1 p.2 hj.2] at this
    · rintro ⟨⟨-, hσ⟩, ⟨-, hτ⟩⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j ∈ C
      · rw [patchOn_of_mem C p.1 p.2 hj]; exact hσ j hj
      · rw [patchOn_of_not_mem C p.1 p.2 hj]
        exact hτ j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
  calc (prodSpace μ h0 h1).toFinProb.Ex (fun ω => f ω * g ω)
      = ∑ ω : (prodSpace μ h0 h1).toFinProb.Ω,
          (prodSpace μ h0 h1).toFinProb.mass ω * (f ω * g ω) := rfl
    _ = ∑ ω : (prodSpace μ h0 h1).toFinProb.Ω,
          ∑ p ∈ (Finset.univ.filter
              fun p : (prodSpace μ h0 h1).toFinProb.Ω × (prodSpace μ h0 h1).toFinProb.Ω =>
                patchOn C p.1 p.2 = ω),
            ((prodSpace μ h0 h1).toFinProb.mass p.1 * f p.1)
              * ((prodSpace μ h0 h1).toFinProb.mass p.2 * g p.2) := by
        refine Finset.sum_congr rfl ?_
        intro ω _
        have hval : ∀ p ∈ (Finset.univ.filter
              fun p : (prodSpace μ h0 h1).toFinProb.Ω × (prodSpace μ h0 h1).toFinProb.Ω =>
                patchOn C p.1 p.2 = ω),
            ((prodSpace μ h0 h1).toFinProb.mass p.1 * f p.1)
                * ((prodSpace μ h0 h1).toFinProb.mass p.2 * g p.2)
              = ((prodSpace μ h0 h1).toFinProb.mass p.1
                    * (prodSpace μ h0 h1).toFinProb.mass p.2) * (f ω * g ω) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hfp : f p.1 = f ω := by
            refine hf p.1 ω ?_
            intro k hk
            have := congrFun hp.2 k
            rwa [patchOn_of_mem C p.1 p.2 hk] at this
          have hgp : g p.2 = g ω := by
            refine hg p.2 ω ?_
            intro k hk
            have := congrFun hp.2 k
            rwa [patchOn_of_not_mem C p.1 p.2 (hDC k hk)] at this
          rw [hfp, hgp]; ring
        rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, hfiber ω,
          sum_mass_mul_cylinder_pair μ h0 h1 C ω]
    _ = ∑ p : (prodSpace μ h0 h1).toFinProb.Ω × (prodSpace μ h0 h1).toFinProb.Ω,
          ((prodSpace μ h0 h1).toFinProb.mass p.1 * f p.1)
            * ((prodSpace μ h0 h1).toFinProb.mass p.2 * g p.2) :=
        Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ = (prodSpace μ h0 h1).toFinProb.Ex f * (prodSpace μ h0 h1).toFinProb.Ex g := by
        unfold FinProb.Ex
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]

/-- **Random variables reading pairwise-disjoint blocks of coordinates are independent.**

`f a` reads only the coordinates in the block `C a` (`hdep`), and the blocks are pairwise
disjoint (`hC`).  Then for every finite index set `T`,

  `E[∏_{a ∈ T} f a] = ∏_{a ∈ T} E[f a]`.

**No positivity hypothesis** on `μ` and **no sign hypothesis** on the `f a`. -/
theorem Ex_prodSpace_prod_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {κ : Type*} [DecidableEq κ]
    (C : κ → Finset ι) (hC : ∀ a b, a ≠ b → Disjoint (C a) (C b))
    (f : κ → (ι → X) → ℝ)
    (hdep : ∀ a, ∀ ω ω' : ι → X, (∀ k ∈ C a, ω k = ω' k) → f a ω = f a ω')
    (T : Finset κ) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ a ∈ T, f a ω)
      = ∏ a ∈ T, (prodSpace μ h0 h1).toFinProb.Ex (f a) := by
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact FinProb.Ex_const _ 1
  | @insert a T ha ih =>
      have hdisj : Disjoint (C a) (T.biUnion C) := by
        rw [Finset.disjoint_biUnion_right]
        intro b hb
        exact hC a b (fun hab => ha (hab ▸ hb))
      have hgdep : ∀ ω ω' : ι → X, (∀ k ∈ T.biUnion C, ω k = ω' k) →
          (∏ b ∈ T, f b ω) = ∏ b ∈ T, f b ω' := by
        intro ω ω' hagree
        refine Finset.prod_congr rfl ?_
        intro b hb
        exact hdep b ω ω' (fun k hk => hagree k (Finset.mem_biUnion.mpr ⟨b, hb, hk⟩))
      have hstep : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ b ∈ insert a T, f b ω)
          = (prodSpace μ h0 h1).toFinProb.Ex (f a)
            * (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ b ∈ T, f b ω) := by
        refine Eq.trans ?_ (Ex_prodSpace_mul_of_disjoint μ h0 h1 hdisj (f a)
          (fun ω => ∏ b ∈ T, f b ω) (hdep a) hgdep)
        refine congrArg _ (funext fun ω => ?_)
        exact Finset.prod_insert ha
      rw [hstep, ih, Finset.prod_insert ha]

/-- The two-factor corollary of `Ex_prodSpace_prod_of_disjoint`, stated directly in terms
of the two blocks — this is `Ex_prodSpace_mul_of_disjoint` under its more memorable name. -/
theorem Ex_prodSpace_indep_of_disjoint (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) {C D : Finset ι} (hCD : Disjoint C D)
    (f g : (ι → X) → ℝ)
    (hf : ∀ ω ω' : ι → X, (∀ k ∈ C, ω k = ω' k) → f ω = f ω')
    (hg : ∀ ω ω' : ι → X, (∀ k ∈ D, ω k = ω' k) → g ω = g ω') :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => f ω * g ω)
      = (prodSpace μ h0 h1).toFinProb.Ex f * (prodSpace μ h0 h1).toFinProb.Ex g :=
  Ex_prodSpace_mul_of_disjoint μ h0 h1 hCD f g hf hg

end Arlib
