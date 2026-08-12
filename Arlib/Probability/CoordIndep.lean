/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Coordinate-block independence over the coin product

This file proves a pure product-measure independence fact, with no appeal to any
particular family of observables:

> events that depend on **pairwise-disjoint coordinate sets** of `C.toFinProb`
> are independent (`ProbSpace.IndepEvents` over `C.toFinProb.toProbSpace`).

This is the fact that makes functions reading disjoint coordinate blocks
independent, so that a family of observables allocated to disjoint blocks of the
coin product is a mutually independent family.

**Route.**  Condition on forgetting one block.  The crux is `condCE_forgetSet_full`:
averaging a function over *exactly* the coins it depends on returns its expectation
(a constant).  `condCE_fixed_rule` then pulls the other, measurable, factor out and
`condCE_Ex` collapses the outer expectation, giving the pairwise factorisation
`Pr[A ∩ B] = Pr[A]·Pr[B]`; a `Finset` induction lifts it to mutual independence.
Everything rests on the coordinate-subset **marginal** (`sum_forgetSet_cell` +
`mass_updOn`), the many-coin analogue of `sum_forget_cell`/`mass_update`.
-/
import Arlib.Probability.ProductSpace
import Arlib.Probability.Independence

namespace Arlib.Probability

open scoped BigOperators Classical
open Finset FinProb

namespace CoinSpace

variable (C : CoinSpace)

/-! ### The coordinate-subset marginal -/

/-- Overwrite `ω` on the block `U` by the partial assignment `c`. -/
def updOn (ω : ∀ i, C.Coin i) (U : Finset C.ι) (c : ∀ k : U, C.Coin k.1) : ∀ i, C.Coin i :=
  fun i => if h : i ∈ U then c ⟨i, h⟩ else ω i

theorem updOn_mem {U : Finset C.ι} (ω : ∀ i, C.Coin i) (c : ∀ k : U, C.Coin k.1) (k : U) :
    C.updOn ω U c k.1 = c k := by
  simp only [updOn, dif_pos k.2]

theorem updOn_not_mem {U : Finset C.ι} (ω : ∀ i, C.Coin i) (c : ∀ k : U, C.Coin k.1)
    {i : C.ι} (hi : i ∉ U) : C.updOn ω U c i = ω i := by
  simp only [updOn, dif_neg hi]

/-- **Summing over a `forgetSet U` cell is summing over the block `U`'s coins.**
The many-coin analogue of `sum_forget_cell`: the cell of `ω` under `forgetSet U`
is in bijection with the partial assignments to the coins of `U`. -/
theorem sum_forgetSet_cell (U : Finset C.ι) (G : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    ∑ ω' ∈ cell C.toFinProb (C.forgetSet U) ω, G ω'
      = ∑ c : (∀ k : U, C.Coin k.1), G (C.updOn ω U c) := by
  apply Finset.sum_bij' (fun ω' _ => (fun k : U => ω' k.1)) (fun c _ => C.updOn ω U c)
  · intro ω' _; exact mem_univ _
  · intro c _
    rw [C.mem_forgetSet_cell]; intro i hi; exact C.updOn_not_mem ω c hi
  · intro ω' hω'
    rw [C.mem_forgetSet_cell] at hω'
    funext i; by_cases hi : i ∈ U
    · simp only [updOn, dif_pos hi]
    · rw [C.updOn_not_mem ω _ hi]; exact (hω' i hi).symm
  · intro c _; funext k; exact C.updOn_mem ω c k
  · intro ω' hω'
    rw [C.mem_forgetSet_cell] at hω'
    congr 1; funext i; by_cases hi : i ∈ U
    · simp only [updOn, dif_pos hi]
    · rw [C.updOn_not_mem ω _ hi]; exact hω' i hi

/-- The mass of a block-update factors into the block's coins and the rest. -/
theorem mass_updOn (ω : ∀ i, C.Coin i) (U : Finset C.ι) (c : ∀ k : U, C.Coin k.1) :
    C.toFinProb.mass (C.updOn ω U c)
      = (∏ k : U, C.coinMass k.1 (c k)) * ∏ i ∈ Uᶜ, C.coinMass i (ω i) := by
  rw [toFinProb_mass, ← Finset.prod_mul_prod_compl U (fun i => C.coinMass i (C.updOn ω U c i))]
  congr 1
  · rw [Finset.univ_eq_attach, ← Finset.prod_attach U (fun i => C.coinMass i (C.updOn ω U c i))]
    exact Finset.prod_congr rfl (fun k _ => by rw [C.updOn_mem])
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_compl] at hi
    rw [C.updOn_not_mem ω _ hi]

/-- The block masses of a full block-assignment sum to `1`. -/
theorem sum_prod_coinMass_block (U : Finset C.ι) :
    (∑ c : (∀ k : U, C.Coin k.1), ∏ k : U, C.coinMass k.1 (c k)) = 1 := by
  rw [← Fintype.prod_sum]
  rw [Finset.prod_congr rfl (fun k _ => C.coinMass_sum k.1)]
  exact Finset.prod_const_one

/-! ### Averaging out exactly a function's coordinates -/

/-- **`condCE (forgetSet U) X = Ex[X]` when `X` depends only on the coins in `U`.**
Conditioning on forgetting *exactly* the coordinates a function reads returns its
expectation — a constant.  This is the key marginal identity behind independence. -/
theorem condCE_forgetSet_full (hpos : ∀ i c, 0 < C.coinMass i c) (U : Finset C.ι)
    (X : (∀ i, C.Coin i) → ℝ)
    (hdep : ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → X ω = X ω') :
    condCE C.toFinProb (C.forgetSet U) X = fun _ => C.toFinProb.Ex X := by
  -- the pointwise value of the conditional expectation, via the block marginal
  have hval : ∀ ω, condCE C.toFinProb (C.forgetSet U) X ω
      = ∑ c : (∀ k : U, C.Coin k.1), (∏ k : U, C.coinMass k.1 (c k)) * X (C.updOn ω U c) := by
    intro ω
    unfold condCE
    rw [C.sum_forgetSet_cell U (fun ω' => C.toFinProb.mass ω' * X ω') ω,
        C.sum_forgetSet_cell U (fun ω' => C.toFinProb.mass ω') ω]
    set M := ∏ i ∈ Uᶜ, C.coinMass i (ω i) with hM
    have hMpos : 0 < M := Finset.prod_pos (fun i _ => hpos i (ω i))
    have hden : (∑ c : (∀ k : U, C.Coin k.1), C.toFinProb.mass (C.updOn ω U c)) = M := by
      rw [Finset.sum_congr rfl (fun c _ => C.mass_updOn ω U c), ← Finset.sum_mul,
        C.sum_prod_coinMass_block U, one_mul]
    have hnum : (∑ c : (∀ k : U, C.Coin k.1),
          C.toFinProb.mass (C.updOn ω U c) * X (C.updOn ω U c))
        = M * ∑ c : (∀ k : U, C.Coin k.1),
            (∏ k : U, C.coinMass k.1 (c k)) * X (C.updOn ω U c) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [C.mass_updOn]; ring)
    rw [hnum, hden, mul_comm M, mul_div_assoc, div_self (ne_of_gt hMpos), mul_one]
  -- `X (updOn a U c)` does not depend on `a` (it reads only `U`, where it equals `c`)
  have hXindep : ∀ (a b : ∀ i, C.Coin i) (c : ∀ k : U, C.Coin k.1),
      X (C.updOn a U c) = X (C.updOn b U c) := by
    intro a b c
    refine hdep _ _ (fun k hk => ?_)
    rw [C.updOn_mem a c ⟨k, hk⟩, C.updOn_mem b c ⟨k, hk⟩]
  -- so the conditional expectation is a constant
  set ω₀ : (∀ i, C.Coin i) := fun i => C.coinPt i with hω₀
  set K := ∑ c : (∀ k : U, C.Coin k.1), (∏ k : U, C.coinMass k.1 (c k)) * X (C.updOn ω₀ U c)
    with hK
  have hconst : condCE C.toFinProb (C.forgetSet U) X = fun _ => K := by
    funext ω
    rw [hval ω, hK]
    exact Finset.sum_congr rfl (fun c _ => by rw [hXindep ω ω₀ c])
  -- and its expectation identifies the constant as `Ex[X]`
  have hExK : C.toFinProb.Ex X = K := by
    rw [← condCE_Ex (P := C.toFinProb) (C.forgetSet U) X, hconst]
    unfold FinProb.Ex
    rw [← Finset.sum_mul, C.toFinProb.mass_sum, one_mul]
  rw [hconst]; funext _; exact hExK.symm

/-! ### Events depending on coordinate blocks -/

/-- `A` depends only on the coins in `U`: it cannot tell apart two outcomes that
agree on `U`. -/
def EventDepOn (A : (∀ i, C.Coin i) → Prop) (U : Finset C.ι) : Prop :=
  ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → (A ω ↔ A ω')

/-- `Pr[A] = Ex[𝟙_A]` for the product space (unfolding the abstract `ProbSpace.Pr`
of `C.toFinProb.toProbSpace` to the finite expectation of the indicator). -/
theorem Pr_eq_Ex_ind (A : (∀ i, C.Coin i) → Prop) :
    C.toFinProb.toProbSpace.Pr A = C.toFinProb.Ex (indic A) := rfl

theorem ind_inter (A B : (∀ i, C.Coin i) → Prop) :
    indic (fun ω => A ω ∧ B ω) = fun ω => indic A ω * indic B ω := by
  funext ω
  simp only [indic_apply]
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

/-- If `A` depends only on `U`, its indicator does too (pointwise on `U`-agreement). -/
theorem ind_depOn {A : (∀ i, C.Coin i) → Prop} {U : Finset C.ι} (hA : C.EventDepOn A U) :
    ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → indic A ω = indic A ω' := by
  intro ω ω' h
  simp only [indic_apply]
  exact if_congr (hA ω ω' h) rfl rfl

/-- An event depending on a block `U` disjoint from `V` has a `forgetSet V`-fixed
indicator (forgetting `V`'s coins cannot change it). -/
theorem CFixed_ind_of_disjoint {A : (∀ i, C.Coin i) → Prop} {U V : Finset C.ι}
    (hA : C.EventDepOn A U) (hUV : Disjoint U V) :
    CFixed C.toFinProb (C.forgetSet V) (indic A) := by
  refine C.CFixed_forgetSet V (indic A) (fun ω ω' h => C.ind_depOn hA ω ω' (fun k hkU => ?_))
  exact h k (fun hkV => (Finset.disjoint_left.1 hUV hkU hkV))

/-! ### Pairwise and mutual independence -/

/-- **Pairwise factorisation.**  Events on disjoint coordinate blocks are
independent: `Pr[A ∩ B] = Pr[A]·Pr[B]`. -/
theorem Pr_inter_eq_mul (hpos : ∀ i c, 0 < C.coinMass i c)
    {A B : (∀ i, C.Coin i) → Prop} {T U : Finset C.ι}
    (hAT : C.EventDepOn A T) (hBU : C.EventDepOn B U) (hTU : Disjoint T U) :
    C.toFinProb.toProbSpace.Pr (fun ω => A ω ∧ B ω)
      = C.toFinProb.toProbSpace.Pr A * C.toFinProb.toProbSpace.Pr B := by
  -- pulling a constant factor out of an expectation
  have Ex_mul_const : ∀ (f : (∀ i, C.Coin i) → ℝ) (a : ℝ),
      C.toFinProb.Ex (fun ω => f ω * a) = C.toFinProb.Ex f * a := by
    intro f a
    unfold FinProb.Ex
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have hfix := condCE_fixed_rule (P := C.toFinProb) (C.forgetSet U) (indic A) (indic B)
    (C.CFixed_ind_of_disjoint hAT hTU)
  have hfull := C.condCE_forgetSet_full hpos U (indic B) (C.ind_depOn hBU)
  rw [Pr_eq_Ex_ind, Pr_eq_Ex_ind, Pr_eq_Ex_ind]
  -- rewrite the intersection indicator as a product, then
  -- condition on forgetting `B`'s block `U`; pull the `U`-fixed factor `ind A` out,
  -- then average `ind B` over its own block (a constant `Pr[B]`)
  calc C.toFinProb.Ex (indic (fun ω => A ω ∧ B ω))
      = C.toFinProb.Ex (fun ω => indic A ω * indic B ω) :=
        congrArg C.toFinProb.Ex (C.ind_inter A B)
    _ = C.toFinProb.Ex (condCE C.toFinProb (C.forgetSet U) (fun ω => indic A ω * indic B ω)) :=
        (condCE_Ex (P := C.toFinProb) (C.forgetSet U) _).symm
    _ = C.toFinProb.Ex (fun ω => indic A ω * condCE C.toFinProb (C.forgetSet U) (indic B) ω) :=
        congrArg C.toFinProb.Ex hfix
    _ = C.toFinProb.Ex (fun ω => indic A ω * C.toFinProb.Ex (indic B)) := by rw [hfull]
    _ = C.toFinProb.Ex (indic A) * C.toFinProb.Ex (indic B) := Ex_mul_const (indic A) _

/-- `interEvent E S` reads only the coins in `⋃_{i∈S} T i`. -/
theorem EventDepOn_interEvent {B : ℕ} (E : Fin B → (∀ i, C.Coin i) → Prop)
    (T : Fin B → Finset C.ι) (hdep : ∀ i, C.EventDepOn (E i) (T i)) (S : Finset (Fin B)) :
    C.EventDepOn (C.toFinProb.toProbSpace.interEvent E S) (S.biUnion T) := by
  intro ω ω' h
  simp only [ProbSpace.interEvent]
  constructor
  · intro hmem i hi
    exact (hdep i ω ω' (fun k hk => h k (Finset.mem_biUnion.2 ⟨i, hi, hk⟩))).1 (hmem i hi)
  · intro hmem i hi
    exact (hdep i ω ω' (fun k hk => h k (Finset.mem_biUnion.2 ⟨i, hi, hk⟩))).2 (hmem i hi)

/-- **Coordinate-block independence.**  A family of events depending on
*pairwise-disjoint* coordinate blocks of the coin product is (mutually)
independent.  This is the probability content that discharges `hindep`. -/
theorem indepEvents_of_disjoint (hpos : ∀ i c, 0 < C.coinMass i c) {B : ℕ}
    (E : Fin B → (∀ i, C.Coin i) → Prop) (T : Fin B → Finset C.ι)
    (hdep : ∀ i, C.EventDepOn (E i) (T i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j)) :
    C.toFinProb.toProbSpace.IndepEvents E := by
  intro S
  induction S using Finset.induction with
  | empty =>
      -- `interEvent E ∅` holds everywhere, so its probability is one
      rw [Finset.prod_empty]
      have hcongr : C.toFinProb.toProbSpace.Pr (C.toFinProb.toProbSpace.interEvent E ∅)
          = C.toFinProb.toProbSpace.Pr (fun _ : (∀ i, C.Coin i) => True) :=
        C.toFinProb.toProbSpace.Pr_congr (fun ω =>
          ⟨fun _ => trivial, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩)
      have hind : indic (fun _ : (∀ i, C.Coin i) => True) = (fun _ => (1 : ℝ)) := by
        funext ω; simp only [indic_apply]; rw [if_pos trivial]
      rw [hcongr]
      show C.toFinProb.toProbSpace.Ex (indic (fun _ : (∀ i, C.Coin i) => True)) = 1
      rw [hind]
      exact C.toFinProb.toProbSpace.Ex_const 1
  | @insert i₀ S' hi₀ ih =>
      -- split off `E i₀`; the rest reads a block disjoint from `T i₀`
      have hsplit : C.toFinProb.toProbSpace.Pr
              (C.toFinProb.toProbSpace.interEvent E (insert i₀ S'))
          = C.toFinProb.toProbSpace.Pr
              (fun ω => E i₀ ω ∧ C.toFinProb.toProbSpace.interEvent E S' ω) := by
        apply C.toFinProb.toProbSpace.Pr_congr
        intro ω
        simp only [ProbSpace.interEvent, Finset.mem_insert, forall_eq_or_imp]
      have hdisj₀ : Disjoint (T i₀) (S'.biUnion T) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i₀ j (fun h => hi₀ (h ▸ hj))
      rw [hsplit,
        C.Pr_inter_eq_mul hpos (hdep i₀) (C.EventDepOn_interEvent E T hdep S') hdisj₀,
        ih, Finset.prod_insert hi₀]

end CoinSpace
end Arlib.Probability
