/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Coordinate-block independence over the mixed coin product (`MixedCoinSpace`)

The `MixedCoinSpace` analogue of `Probability/CoordIndep.lean`.  It ports **only
the exposed downstream surface** — events depending on pairwise-disjoint
coordinate blocks of the continuous coin product are (mutually) independent
(`ProbSpace.IndepEvents` over `C.toProbSpace`).  The finite-sum internals of
`CoordIndep` (`updOn`, `sum_forgetSet_cell`, `mass_updOn`,
`sum_prod_coinMass_block`, `condCE_forgetSet_full`) do **not** port: their role is
played by the already-proven integral primitives of `MixedCoinSpace`
(`condCE_forgetSet_fixed_rule`, `condCE_forgetSet_full`, `condCE_forgetSet_cond_Ex`).

**Route.**  As in the finite file, condition on forgetting one block.
`Pr[A ∩ B] = Ex[𝟙_A · 𝟙_B]`; the intersection indicator factors as a product
(`ind_inter`); conditioning on forgetting `B`'s block `U` (`condCE_forgetSet_cond_Ex`,
the keystone Fubini identity) and pulling the `U`-fixed factor `𝟙_A` out
(`condCE_forgetSet_fixed_rule`), then averaging `𝟙_B` over exactly its own block
(`condCE_forgetSet_full`, the marginal-of-a-block-function collapse), gives the
pairwise factorisation `Pr[A ∩ B] = Pr[A]·Pr[B]`.  A `Finset` induction lifts it
to mutual independence.

The finite positivity hypothesis `hpos : ∀ i c, 0 < coinMass i c` is replaced by
`BddMeas` (bounded-measurable) obligations on the event indicators: on this
probability measure the mass is automatically one (no positivity needed), and the
only extra input over the finite model is the **measurability of the events**
(carried through `BddMeas (indic (E i))`).
-/
import Arlib.Probability.MixedRunProduct
import Arlib.Probability.Independence

namespace Arlib.Probability

open MeasureTheory
open scoped BigOperators Classical
open Finset

namespace MixedCoinSpace

variable (C : MixedCoinSpace)

/-! ### Events depending on coordinate blocks -/

/-- `A` depends only on the coins in `U`: it cannot tell apart two outcomes that
agree on `U`.  (Same shape as `CoinSpace.EventDepOn`, adapted to `C.Ω`.) -/
def EventDepOn (A : C.Ω → Prop) (U : Finset C.ι) : Prop :=
  ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → (A ω ↔ A ω')

/-- `Pr[A] = Ex[𝟙_A]` for the mixed product space (unfolding `ProbSpace.Pr` of
`C.toProbSpace` to the coin-product expectation of the indicator). -/
theorem Pr_eq_Ex_ind (A : C.Ω → Prop) :
    C.toProbSpace.Pr A = C.Ex (indic A) := rfl

/-- The indicator of an intersection is the product of the indicators. -/
theorem ind_inter (A B : C.Ω → Prop) :
    indic (fun ω => A ω ∧ B ω) = fun ω => indic A ω * indic B ω := by
  funext ω
  simp only [indic_apply]
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

/-- If `A` depends only on `U`, its indicator does too (pointwise on `U`-agreement). -/
theorem ind_depOn {A : C.Ω → Prop} {U : Finset C.ι} (hA : C.EventDepOn A U) :
    ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → indic A ω = indic A ω' := by
  intro ω ω' h
  simp only [indic_apply]
  exact if_congr (hA ω ω' h) rfl rfl

/-- An event depending on a block `U` disjoint from `V` has a `forgetSet V`-fixed
indicator (forgetting `V`'s coins cannot change it).  The mixed analogue of the
finite `CFixed_ind_of_disjoint`, over `forgetSet` of `MixedCoinSpace`. -/
theorem CFixed_ind_of_disjoint {A : C.Ω → Prop} {U V : Finset C.ι}
    (hA : C.EventDepOn A U) (hUV : Disjoint U V) :
    C.CFixed (C.forgetSet V) (indic A) := by
  refine C.CFixed_forgetSet V (indic A) (fun ω ω' h => C.ind_depOn hA ω ω' (fun k hkU => ?_))
  exact h k (fun hkV => (Finset.disjoint_left.1 hUV hkU hkV))

/-! ### Pairwise factorisation -/

/-- **Pairwise factorisation.**  Events on disjoint coordinate blocks are
independent: `Pr[A ∩ B] = Pr[A]·Pr[B]`.  The finite `hpos` is replaced by
`BddMeas` on the two indicators (indicators are bounded; measurability of the
events is the genuine extra hypothesis over the finite model).  Proof: the
integral factorises via `condCE_forgetSet_cond_Ex` (keystone Fubini),
`condCE_forgetSet_fixed_rule` (pull the fixed factor out), and
`condCE_forgetSet_full` (average the other over its own block). -/
theorem Pr_inter_eq_mul {A B : C.Ω → Prop} {T U : Finset C.ι}
    (hmA : C.BddMeas (indic A)) (hmB : C.BddMeas (indic B))
    (hAT : C.EventDepOn A T) (hBU : C.EventDepOn B U) (hTU : Disjoint T U) :
    C.toProbSpace.Pr (fun ω => A ω ∧ B ω)
      = C.toProbSpace.Pr A * C.toProbSpace.Pr B := by
  -- pulling a constant factor out of an expectation (via `Ex_smul`)
  have Ex_mul_const : ∀ (f : C.Ω → ℝ) (a : ℝ),
      C.Ex (fun ω => f ω * a) = C.Ex f * a := by
    intro f a
    have hcomm : (fun ω => f ω * a) = (fun ω => a * f ω) := by funext ω; ring
    rw [hcomm, C.Ex_smul, mul_comm]
  have hfix := C.condCE_forgetSet_fixed_rule U (indic A) (indic B)
    (C.CFixed_ind_of_disjoint hAT hTU)
  have hfull := C.condCE_forgetSet_full U (indic B) hmB (C.ind_depOn hBU)
  have hprod : C.BddMeas (fun ω => indic A ω * indic B ω) := C.BddMeas_mul hmA hmB
  rw [Pr_eq_Ex_ind, Pr_eq_Ex_ind, Pr_eq_Ex_ind]
  calc C.Ex (indic (fun ω => A ω ∧ B ω))
      = C.Ex (fun ω => indic A ω * indic B ω) :=
        congrArg C.Ex (C.ind_inter A B)
    _ = C.Ex (C.condCE_forgetSet U (fun ω => indic A ω * indic B ω)) :=
        (C.condCE_forgetSet_cond_Ex U _ hprod).symm
    _ = C.Ex (fun ω => indic A ω * C.condCE_forgetSet U (indic B) ω) :=
        congrArg C.Ex hfix
    _ = C.Ex (fun ω => indic A ω * C.Ex (indic B)) := by rw [hfull]
    _ = C.Ex (indic A) * C.Ex (indic B) := Ex_mul_const (indic A) _

/-! ### Almost-everywhere pairwise factorisation -/

/-- **Almost-everywhere pairwise factorisation.**  A weakening of
`Pr_inter_eq_mul` that only needs the two events to *agree almost everywhere* with
events `A'`, `B'` living on disjoint coordinate blocks.  This is the tool for the
`#DNNF` `×`-child independence, where the two children read a genuinely shared
(but almost-surely non-influential) block of variable-free coins: replacing the
child indicators by their non-shared restrictions (equal a.e.) makes the blocks
disjoint, and `integral_congr_ae` transports the factorisation back.

Concretely: given `indic A =ᵐ indic A'` and `indic B =ᵐ indic B'` with
`A' EventDepOn T`, `B' EventDepOn U`, `Disjoint T U`, the product expectation
`E[𝟙_A · 𝟙_B]` factors as `E[𝟙_A] · E[𝟙_B]`. -/
theorem Pr_inter_eq_mul_ae {A B A' B' : C.Ω → Prop} {T U : Finset C.ι}
    (hmA' : C.BddMeas (indic A')) (hmB' : C.BddMeas (indic B'))
    (hAT : C.EventDepOn A' T) (hBU : C.EventDepOn B' U) (hTU : Disjoint T U)
    (haeA : indic A =ᵐ[C.measure] indic A') (haeB : indic B =ᵐ[C.measure] indic B') :
    C.Ex (fun ω => indic A ω * indic B ω) = C.Ex (indic A) * C.Ex (indic B) := by
  have hExcongr : ∀ (f g : C.Ω → ℝ), f =ᵐ[C.measure] g → C.Ex f = C.Ex g := by
    intro f g h; unfold MixedCoinSpace.Ex; exact integral_congr_ae h
  have h1 : C.Ex (fun ω => indic A ω * indic B ω)
      = C.Ex (fun ω => indic A' ω * indic B' ω) :=
    hExcongr _ _ (haeA.mul haeB)
  have hmul : C.Ex (fun ω => indic A' ω * indic B' ω)
      = C.Ex (indic A') * C.Ex (indic B') := by
    have h := C.Pr_inter_eq_mul hmA' hmB' hAT hBU hTU
    simp only [Pr_eq_Ex_ind] at h
    rw [← C.ind_inter A' B']; exact h
  rw [h1, hmul, hExcongr _ _ haeA.symm, hExcongr _ _ haeB.symm]

/-! ### Mutual independence -/

/-- `interEvent E S` reads only the coins in `⋃_{i∈S} T i`. -/
theorem EventDepOn_interEvent {B : ℕ} (E : Fin B → C.Ω → Prop)
    (T : Fin B → Finset C.ι) (hdep : ∀ i, C.EventDepOn (E i) (T i)) (S : Finset (Fin B)) :
    C.EventDepOn (C.toProbSpace.interEvent E S) (S.biUnion T) := by
  intro ω ω' h
  simp only [ProbSpace.interEvent]
  constructor
  · intro hmem i hi
    exact (hdep i ω ω' (fun k hk => h k (Finset.mem_biUnion.2 ⟨i, hi, hk⟩))).1 (hmem i hi)
  · intro hmem i hi
    exact (hdep i ω ω' (fun k hk => h k (Finset.mem_biUnion.2 ⟨i, hi, hk⟩))).2 (hmem i hi)

/-- The indicator of a finite intersection is the product of the indicators — the
bridge that discharges `BddMeas (indic (interEvent E S))` from
`BddMeas (indic (E b))` (via `BddMeas_prod`). -/
theorem indic_interEvent {B : ℕ} (E : Fin B → C.Ω → Prop) (S : Finset (Fin B)) :
    indic (C.toProbSpace.interEvent E S) = fun ω => ∏ b ∈ S, indic (E b) ω := by
  funext ω
  by_cases h : ∀ b ∈ S, E b ω
  · have hleft : indic (C.toProbSpace.interEvent E S) ω = 1 := by
      simp only [indic_apply]; exact if_pos h
    rw [hleft]
    symm
    refine Finset.prod_eq_one (fun b hb => ?_)
    simp only [indic_apply]; exact if_pos (h b hb)
  · have hleft : indic (C.toProbSpace.interEvent E S) ω = 0 := by
      simp only [indic_apply]; exact if_neg h
    rw [hleft]
    push_neg at h
    obtain ⟨b, hb, hnb⟩ := h
    symm
    refine Finset.prod_eq_zero hb ?_
    simp only [indic_apply]; exact if_neg hnb

/-- **Coordinate-block independence.**  A family of events depending on
*pairwise-disjoint* coordinate blocks of the mixed coin product is (mutually)
independent.  This is the probability content that discharges `hindep`.

The finite `hpos` is replaced by `hmeas : ∀ i, BddMeas (indic (E i))`
(measurability of the events; the `BddMeas` of every finite intersection is
derived from it via `indic_interEvent` + `BddMeas_prod`). -/
theorem indepEvents_of_disjoint {B : ℕ}
    (E : Fin B → C.Ω → Prop) (T : Fin B → Finset C.ι)
    (hmeas : ∀ i, C.BddMeas (indic (E i)))
    (hdep : ∀ i, C.EventDepOn (E i) (T i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j)) :
    C.toProbSpace.IndepEvents E := by
  intro S
  induction S using Finset.induction with
  | empty =>
      -- `interEvent E ∅` holds everywhere, so its probability is one
      rw [Finset.prod_empty]
      have hcongr : C.toProbSpace.Pr (C.toProbSpace.interEvent E ∅)
          = C.toProbSpace.Pr (fun _ : C.Ω => True) :=
        C.toProbSpace.Pr_congr (fun ω =>
          ⟨fun _ => trivial, fun _ i hi => absurd hi (Finset.not_mem_empty i)⟩)
      have hind : indic (fun _ : C.Ω => True) = (fun _ => (1 : ℝ)) := by
        funext ω; simp only [indic_apply]; rw [if_pos trivial]
      rw [hcongr]
      show C.toProbSpace.Ex (indic (fun _ : C.Ω => True)) = 1
      rw [hind]
      exact C.toProbSpace.Ex_const 1
  | @insert i₀ S' hi₀ ih =>
      -- split off `E i₀`; the rest reads a block disjoint from `T i₀`
      have hsplit : C.toProbSpace.Pr
              (C.toProbSpace.interEvent E (insert i₀ S'))
          = C.toProbSpace.Pr
              (fun ω => E i₀ ω ∧ C.toProbSpace.interEvent E S' ω) := by
        apply C.toProbSpace.Pr_congr
        intro ω
        simp only [ProbSpace.interEvent, Finset.mem_insert, forall_eq_or_imp]
      have hdisj₀ : Disjoint (T i₀) (S'.biUnion T) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i₀ j (fun h => hi₀ (h ▸ hj))
      have hmInter : C.BddMeas (indic (C.toProbSpace.interEvent E S')) := by
        rw [C.indic_interEvent E S']
        exact C.BddMeas_prod S' (fun b => indic (E b)) (fun b _ => hmeas b)
      rw [hsplit,
        C.Pr_inter_eq_mul (hmeas i₀) hmInter (hdep i₀)
          (C.EventDepOn_interEvent E T hdep S') hdisj₀,
        ih, Finset.prod_insert hi₀]

end MixedCoinSpace
end Arlib.Probability
