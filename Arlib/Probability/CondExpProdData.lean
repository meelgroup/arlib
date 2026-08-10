/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The n-ary tower-rule product factorization `condCE_prod_data`

`ReduceModel.condCE_pair_data` factors a product of **two** data-dependent
keep-decisions with a shared, `𝓕̂`-fixed threshold, using the tower rule through
`forget j₁` (so it tolerates a shared threshold — no *global* `Disjoint` of the
coin blocks is required, only that each keep-coin is distinct from the others'
and that the cofactor does not read the peeled keep-coin).

This file supplies the `Finset`-indexed generalization: for a family of keep
decisions `keep i` with keep-coins `j i ∈ T`, pairwise keep-independence
(`hindep`: `keep i` is fixed by forgetting a *different* keep-coin `j i'`), and
per-factor average `condCE (forget (j i)) (keep i) = threshold i` with each
`threshold i` `forgetSet T`-fixed,

  `E[∏_{i∈s} keep i | forgetSet T] = ∏_{i∈s} threshold i`.

## Why not literally invoke the binary `condCE_pair_data`

The binary lemma's last hypothesis `hk2forget : condCE (forget j₂) keep₂ =
threshold₂` needs the *cofactor* `keep₂` to be a **single-coin-forget** average.
In the n-ary peel the cofactor is the product `∏_{i∈s'} keep i`, which is *not* a
single-coin function; its `forgetSet T`-average is the **inductive hypothesis**,
not a single-coin `forget`.  So we re-run the *same* tower argument as
`condCE_pair_data` (peel `keep i₀` through `forget (j i₀)`, pull the fixed
threshold out under `forgetSet T`, close the cofactor by IH) rather than calling
the binary lemma as a black box.  Mechanism identical; only the cofactor closure
differs (IH vs. `condCE_forgetSet_of_forget`).

No `sorry`, no new axioms.
-/
import Arlib.Probability.ReduceModel
import Arlib.Probability.CondExpProd

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

-- Keep the concrete `condCE` opaque: this file composes the abstract tower/fixed
-- lemmas and never unfolds `mass = ∏ᵢ coinMassᵢ`.
attribute [local irreducible] FinProb.condCE

namespace CoinSpace

variable (C : CoinSpace)

/-- **Product of `CFixed` functions is `CFixed`.**  If each `f i` is fixed by the
observable `π`, so is their `Finset` product. -/
theorem CFixed_prod {ι' : Type*} (π : (∀ i, C.Coin i) → (∀ i, C.Coin i))
    (s : Finset ι') (f : ι' → (∀ i, C.Coin i) → ℝ)
    (hf : ∀ i ∈ s, CFixed C.toFinProb π (f i)) :
    CFixed C.toFinProb π (fun ω => ∏ i ∈ s, f i ω) := by
  intro a b hab
  exact Finset.prod_congr rfl (fun i hi => hf i hi a b hab)

/-- **The n-ary tower-rule product factorization** (`condCE_pair_data`, generalized
from 2 factors to a `Finset`).  Each keep-decision `keep i` has keep-coin `j i ∈ T`
and averages to a `forgetSet T`-fixed threshold; distinct keep-decisions are
independent (`hindep`).  Then the `forgetSet T`-conditional of their product factors
into the product of thresholds — the shared threshold is handled by the tower step,
so no global `Disjoint` is needed. -/
theorem condCE_prod_data (hpos : ∀ i c, 0 < C.coinMass i c)
    {ι' : Type*} [DecidableEq ι'] {T : Finset C.ι} (s : Finset ι')
    (j : ι' → C.ι) (keep threshold : ι' → (∀ i, C.Coin i) → ℝ)
    (hjT : ∀ i ∈ s, j i ∈ T)
    (htfixed : ∀ i ∈ s, CFixed C.toFinProb (C.forgetSet T) (threshold i))
    (hindep : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' →
      CFixed C.toFinProb (C.forget (j i')) (keep i))
    (hforget : ∀ i ∈ s, condCE C.toFinProb (C.forget (j i)) (keep i) = threshold i) :
    condCE C.toFinProb (C.forgetSet T) (fun ω => ∏ i ∈ s, keep i ω)
      = fun ω => ∏ i ∈ s, threshold i ω := by
  induction s using Finset.induction with
  | empty =>
      funext ω
      simp only [Finset.prod_empty]
      exact C.condCE_const_of_pos hpos (C.forgetSet T) 1 ω
  | @insert i₀ s' hi₀ ih =>
      -- Restrict the four hypotheses to `s'` for the inductive hypothesis.
      have hjT' : ∀ i ∈ s', j i ∈ T := fun i hi => hjT i (Finset.mem_insert_of_mem hi)
      have htfixed' : ∀ i ∈ s', CFixed C.toFinProb (C.forgetSet T) (threshold i) :=
        fun i hi => htfixed i (Finset.mem_insert_of_mem hi)
      have hindep' : ∀ i ∈ s', ∀ i' ∈ s', i ≠ i' →
          CFixed C.toFinProb (C.forget (j i')) (keep i) :=
        fun i hi i' hi' => hindep i (Finset.mem_insert_of_mem hi) i'
          (Finset.mem_insert_of_mem hi')
      have hforget' : ∀ i ∈ s', condCE C.toFinProb (C.forget (j i)) (keep i) = threshold i :=
        fun i hi => hforget i (Finset.mem_insert_of_mem hi)
      have IH := ih hjT' htfixed' hindep' hforget'
      -- Abbreviations.
      set πT := C.forgetSet T with hπT
      set π0 := C.forget (j i₀) with hπ0
      set Pk := fun ω => ∏ i ∈ s', keep i ω with hPk
      set Pt := fun ω => ∏ i ∈ s', threshold i ω with hPt
      -- The cofactor product does not read the peeled keep-coin `j i₀`.
      have hcofix : CFixed C.toFinProb π0 Pk := by
        apply C.CFixed_prod π0 s' keep
        intro i hi
        exact hindep i (Finset.mem_insert_of_mem hi) i₀ (Finset.mem_insert_self _ _)
          (fun h => hi₀ (h ▸ hi))
      have hk0forget : condCE C.toFinProb π0 (keep i₀) = threshold i₀ :=
        hforget i₀ (Finset.mem_insert_self _ _)
      have ht0fixed : CFixed C.toFinProb πT (threshold i₀) :=
        htfixed i₀ (Finset.mem_insert_self _ _)
      have hsub0 : CSub C.toFinProb πT π0 := by
        rw [hπ0, forget_eq_forgetSet_singleton]
        exact C.CSub_forgetSet (Finset.singleton_subset_iff.mpr (hjT i₀ (Finset.mem_insert_self _ _)))
      -- Peel `keep i₀` through `forget (j i₀)`: the cofactor is fixed there.
      have step1 : condCE C.toFinProb π0 (fun ω => keep i₀ ω * Pk ω)
          = fun ω => threshold i₀ ω * Pk ω := by
        calc condCE C.toFinProb π0 (fun ω => keep i₀ ω * Pk ω)
            = condCE C.toFinProb π0 (fun ω => Pk ω * keep i₀ ω) :=
              congrArg (condCE C.toFinProb π0) (by funext ω; ring)
          _ = fun ω => Pk ω * condCE C.toFinProb π0 (keep i₀) ω :=
              condCE_fixed_rule (P := C.toFinProb) π0 Pk (keep i₀) hcofix
          _ = fun ω => Pk ω * threshold i₀ ω := by rw [hk0forget]
          _ = fun ω => threshold i₀ ω * Pk ω := by funext ω; ring
      -- Tower to `forgetSet T`, pull the fixed threshold out, close by IH.
      have hmain : condCE C.toFinProb πT (fun ω => keep i₀ ω * Pk ω)
          = fun ω => threshold i₀ ω * Pt ω := by
        calc condCE C.toFinProb πT (fun ω => keep i₀ ω * Pk ω)
            = condCE C.toFinProb πT
                (condCE C.toFinProb π0 (fun ω => keep i₀ ω * Pk ω)) :=
              (condCE_tower (P := C.toFinProb) πT π0 _ hsub0).symm
          _ = condCE C.toFinProb πT (fun ω => threshold i₀ ω * Pk ω) :=
              congrArg _ step1
          _ = fun ω => threshold i₀ ω * condCE C.toFinProb πT Pk ω :=
              condCE_fixed_rule (P := C.toFinProb) πT (threshold i₀) Pk ht0fixed
          _ = fun ω => threshold i₀ ω * Pt ω := by
              rw [show C.toFinProb.condCE πT Pk = Pt from IH]
      -- Reshape both products via `prod_insert`.
      calc condCE C.toFinProb πT (fun ω => ∏ i ∈ insert i₀ s', keep i ω)
          = condCE C.toFinProb πT (fun ω => keep i₀ ω * Pk ω) := by
            refine congrArg (condCE C.toFinProb πT) ?_
            funext ω; rw [Finset.prod_insert hi₀]
        _ = fun ω => threshold i₀ ω * Pt ω := hmain
        _ = fun ω => ∏ i ∈ insert i₀ s', threshold i ω := by
            funext ω; rw [Finset.prod_insert hi₀]

/-- **Block conditional factorization with a shared kept sub-σ-algebra.**  A
*relaxation* of `condCE_forgetSet_prod`: each factor `f b` may depend not only on its
own forgotten block `D b ⊆ U`, but also on the **kept** coins `Uᶜ` (the `forgetSet U`
sub-σ-algebra) — as long as the forgotten blocks `D b` are pairwise disjoint.

This covers the case where each block factor `f b` reads its own forgotten block
`D b ⊆ U` *and* a shared, `forgetSet U`-fixed quantity living in the kept coins
`Uᶜ`.  Since the shared quantity is frozen inside each `forgetSet U`-cell
(`condCE_forgetSet_apply`), the block average sees each `f b` as a function of
`D b` alone, so `Ex_prod_of_disjoint` applies directly.  No global `Disjoint` on
the shared coins is needed (they live in `Uᶜ`, not in any `D b`).

The `hdep` hypothesis is "`f b` reads only `D b ∪ Uᶜ`": agreeing off `U` and on `D b`
forces `f b` to agree. -/
theorem condCE_forgetSet_prod_shared (hpos : ∀ i c, 0 < C.coinMass i c) (U : Finset C.ι)
    {ι' : Type*} [DecidableEq ι'] (D : ι' → Finset C.ι)
    (f : ι' → (∀ i, C.Coin i) → ℝ) (s : Finset ι')
    (hDU : ∀ b ∈ s, D b ⊆ U)
    (hdep : ∀ b ∈ s, ∀ ω ω', (∀ i, i ∉ U → ω i = ω' i) →
      (∀ i ∈ D b, ω i = ω' i) → f b ω = f b ω')
    (hdisj : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (D b) (D b')) :
    condCE C.toFinProb (C.forgetSet U) (fun ω => ∏ b ∈ s, f b ω)
      = fun ω => ∏ b ∈ s, condCE C.toFinProb (C.forgetSet U) (f b) ω := by
  funext ω
  let D' : ι' → Finset (C.subCoin U).ι := fun b => Finset.univ.filter (fun k => k.1 ∈ D b)
  have hdep' : ∀ b ∈ s, ∀ c c' : (C.subCoin U).toFinProb.Ω,
      (∀ k ∈ D' b, c k = c' k) → f b (C.updOn ω U c) = f b (C.updOn ω U c') := by
    intro b hb c c' hcc
    refine hdep b hb (C.updOn ω U c) (C.updOn ω U c') (fun i hi => ?_) (fun i hi => ?_)
    · rw [C.updOn_not_mem ω c hi, C.updOn_not_mem ω c' hi]
    · have hiU : i ∈ U := hDU b hb hi
      have hk : (⟨i, hiU⟩ : {k // k ∈ U}) ∈ D' b := by
        simp only [D', Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      rw [C.updOn_mem ω c ⟨i, hiU⟩, C.updOn_mem ω c' ⟨i, hiU⟩, hcc _ hk]
  have hdisj' : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (D' b) (D' b') := by
    intro b hb b' hb' hbb'
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [D', Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact (Finset.disjoint_left.1 (hdisj b hb b' hb' hbb') hk) hk'
  have key := (C.subCoin U).Ex_prod_of_disjoint (fun i c => hpos i.1 c) D'
    (fun b c => f b (C.updOn ω U c)) s hdep' hdisj'
  simp only [C.condCE_forgetSet_apply hpos U]
  exact key

end CoinSpace
end Arlib.Probability
