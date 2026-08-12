/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conditional product factorization over disjoint coin blocks

The `SecondMoment` block-factorization fields (`fact_Xhat`/`fact_X`) require the
conditional-expectation analogue of `CoordIndep`'s event independence:

> `condCE (forgetSet U) (∏_b f_b) = ∏_b condCE (forgetSet U) f_b`
> when each `f_b` reads only the coins in a block `D b` and the blocks are
> **pairwise disjoint** (no constraint relating them to `U`).

The route mirrors `CoordIndep.indepEvents_of_disjoint`, lifted from `{0,1}`-valued
indicators (events) to arbitrary real-valued functions:

* `subCoin U` — the sub-coin-space on the block `U`;
* `condCE_forgetSet_apply` — the block-average formula: conditioning on
  `forgetSet U` at a point `ω` is expectation over `subCoin U` (the `ω`-cell);
* `Ex_prod_of_disjoint` — **`Ex[∏_b f_b] = ∏_b Ex[f_b]`** for functions on disjoint
  blocks (the function analogue of `indepEvents_of_disjoint`; proved by the same
  clean induction — condition on forgetting one block, pull the rest out as fixed,
  average the last to a constant);
* `condCE_forgetSet_prod` — the conditional factorization, obtained by applying
  `Ex_prod_of_disjoint` cell-wise over `subCoin U`.

No `sorry`.  Pure product-measure algebra, independent of any specific
application.
-/
import Arlib.Probability.CoordIndep

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

namespace CoinSpace

variable (C : CoinSpace)

/-- The **sub-coin-space** on a block `U`: the product of exactly `U`'s coins. -/
@[reducible] def subCoin (U : Finset C.ι) : CoinSpace where
  ι := {k : C.ι // k ∈ U}
  Coin := fun k => C.Coin k.1
  coinMass := fun k => C.coinMass k.1
  coinMass_nonneg := fun k => C.coinMass_nonneg k.1
  coinMass_sum := fun k => C.coinMass_sum k.1

/-- **Block-average formula.**  Conditioning `G` on `forgetSet U` at `ω` is the
expectation of `G` over the sub-coin-space `subCoin U`, with the coins outside `U`
held at `ω` (`updOn ω U ·`). -/
theorem condCE_forgetSet_apply (hpos : ∀ i c, 0 < C.coinMass i c) (U : Finset C.ι)
    (G : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forgetSet U) G ω
      = (C.subCoin U).toFinProb.Ex (fun c => G (C.updOn ω U c)) := by
  have hval : condCE C.toFinProb (C.forgetSet U) G ω
      = ∑ c : (∀ k : U, C.Coin k.1),
          (∏ k : U, C.coinMass k.1 (c k)) * G (C.updOn ω U c) := by
    unfold condCE
    rw [C.sum_forgetSet_cell U (fun ω' => C.toFinProb.mass ω' * G ω') ω,
        C.sum_forgetSet_cell U (fun ω' => C.toFinProb.mass ω') ω]
    set M := ∏ i ∈ Uᶜ, C.coinMass i (ω i) with hM
    have hMpos : 0 < M := Finset.prod_pos (fun i _ => hpos i (ω i))
    have hden : (∑ c : (∀ k : U, C.Coin k.1), C.toFinProb.mass (C.updOn ω U c)) = M := by
      rw [Finset.sum_congr rfl (fun c _ => C.mass_updOn ω U c), ← Finset.sum_mul,
        C.sum_prod_coinMass_block U, one_mul]
    have hnum : (∑ c : (∀ k : U, C.Coin k.1),
          C.toFinProb.mass (C.updOn ω U c) * G (C.updOn ω U c))
        = M * ∑ c : (∀ k : U, C.Coin k.1),
            (∏ k : U, C.coinMass k.1 (c k)) * G (C.updOn ω U c) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [C.mass_updOn]; ring)
    rw [hnum, hden, mul_comm M, mul_div_assoc, div_self (ne_of_gt hMpos), mul_one]
  rw [hval]
  unfold FinProb.Ex
  exact Finset.sum_congr rfl (fun c _ => rfl)

/-- **`Ex[∏_b f_b] = ∏_b Ex[f_b]` for functions on pairwise-disjoint blocks.**
The function analogue of `indepEvents_of_disjoint`. -/
theorem Ex_prod_of_disjoint (hpos : ∀ i c, 0 < C.coinMass i c)
    {ι' : Type*} [DecidableEq ι'] (D : ι' → Finset C.ι)
    (f : ι' → (∀ i, C.Coin i) → ℝ) (s : Finset ι')
    (hdep : ∀ b ∈ s, ∀ ω ω', (∀ i ∈ D b, ω i = ω' i) → f b ω = f b ω')
    (hdisj : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (D b) (D b')) :
    C.toFinProb.Ex (fun ω => ∏ b ∈ s, f b ω) = ∏ b ∈ s, C.toFinProb.Ex (f b) := by
  have Ex_mul_const : ∀ (g : (∀ i, C.Coin i) → ℝ) (a : ℝ),
      C.toFinProb.Ex (fun ω => g ω * a) = C.toFinProb.Ex g * a := by
    intro g a
    unfold FinProb.Ex
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  revert hdep hdisj
  induction s using Finset.induction with
  | empty => intro _ _; simp only [Finset.prod_empty]; exact C.toFinProb.Ex_const 1
  | @insert i₀ s' hi₀ ih =>
      intro hdep hdisj
      have hdep' : ∀ b ∈ s', ∀ ω ω', (∀ i ∈ D b, ω i = ω' i) → f b ω = f b ω' :=
        fun b hb => hdep b (Finset.mem_insert_of_mem hb)
      have hdisj' : ∀ b ∈ s', ∀ b' ∈ s', b ≠ b' → Disjoint (D b) (D b') :=
        fun b hb b' hb' => hdisj b (Finset.mem_insert_of_mem hb) b'
          (Finset.mem_insert_of_mem hb')
      -- the rest `R = ∏_{s'} f_b` reads `⋃_{s'} D b`, disjoint from `D i₀`
      have hdisj0 : Disjoint (D i₀) (s'.biUnion D) := by
        rw [Finset.disjoint_biUnion_right]
        intro b hb
        exact hdisj i₀ (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
          (fun h => hi₀ (h ▸ hb))
      have hRfix : CFixed C.toFinProb (C.forgetSet (D i₀)) (fun ω => ∏ b ∈ s', f b ω) := by
        apply C.CFixed_forgetSet
        intro ω ω' hoff
        apply Finset.prod_congr rfl
        intro b hb
        exact hdep b (Finset.mem_insert_of_mem hb) ω ω'
          (fun i hi => hoff i (Finset.disjoint_right.1 hdisj0 (Finset.mem_biUnion.2 ⟨b, hb, hi⟩)))
      have hfi0 : condCE C.toFinProb (C.forgetSet (D i₀)) (f i₀) = fun _ => C.toFinProb.Ex (f i₀) :=
        C.condCE_forgetSet_full hpos (D i₀) (f i₀) (hdep i₀ (Finset.mem_insert_self _ _))
      have hpull := condCE_fixed_rule (P := C.toFinProb) (C.forgetSet (D i₀))
        (fun ω => ∏ b ∈ s', f b ω) (f i₀) hRfix
      calc C.toFinProb.Ex (fun ω => ∏ b ∈ insert i₀ s', f b ω)
          = C.toFinProb.Ex (fun ω => (∏ b ∈ s', f b ω) * f i₀ ω) := by
            congr 1; funext ω; rw [Finset.prod_insert hi₀]; ring
        _ = C.toFinProb.Ex (condCE C.toFinProb (C.forgetSet (D i₀))
              (fun ω => (∏ b ∈ s', f b ω) * f i₀ ω)) :=
            (condCE_Ex (P := C.toFinProb) _ _).symm
        _ = C.toFinProb.Ex (fun ω => (∏ b ∈ s', f b ω)
              * condCE C.toFinProb (C.forgetSet (D i₀)) (f i₀) ω) := by rw [hpull]
        _ = C.toFinProb.Ex (fun ω => (∏ b ∈ s', f b ω) * C.toFinProb.Ex (f i₀)) := by rw [hfi0]
        _ = C.toFinProb.Ex (fun ω => ∏ b ∈ s', f b ω) * C.toFinProb.Ex (f i₀) :=
            Ex_mul_const _ _
        _ = (∏ b ∈ s', C.toFinProb.Ex (f b)) * C.toFinProb.Ex (f i₀) := by
            rw [ih hdep' hdisj']
        _ = ∏ b ∈ insert i₀ s', C.toFinProb.Ex (f b) := by
            rw [Finset.prod_insert hi₀]; ring

/-- **Conditional product factorization.**  If each `f b` reads only the coins in a
block `D b` and the blocks are pairwise disjoint, then conditioning the product on
`forgetSet U` factors through the blocks. -/
theorem condCE_forgetSet_prod (hpos : ∀ i c, 0 < C.coinMass i c) (U : Finset C.ι)
    {ι' : Type*} [DecidableEq ι'] (D : ι' → Finset C.ι)
    (f : ι' → (∀ i, C.Coin i) → ℝ) (s : Finset ι')
    (hdep : ∀ b ∈ s, ∀ ω ω', (∀ i ∈ D b, ω i = ω' i) → f b ω = f b ω')
    (hdisj : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (D b) (D b')) :
    condCE C.toFinProb (C.forgetSet U) (fun ω => ∏ b ∈ s, f b ω)
      = fun ω => ∏ b ∈ s, condCE C.toFinProb (C.forgetSet U) (f b) ω := by
  funext ω
  -- sub-blocks of `U` for each function, and the transported hypotheses
  let D' : ι' → Finset (C.subCoin U).ι := fun b => Finset.univ.filter (fun k => k.1 ∈ D b)
  have hdep' : ∀ b ∈ s, ∀ c c' : (C.subCoin U).toFinProb.Ω,
      (∀ k ∈ D' b, c k = c' k) → f b (C.updOn ω U c) = f b (C.updOn ω U c') := by
    intro b hb c c' hcc
    refine hdep b hb (C.updOn ω U c) (C.updOn ω U c') (fun i hi => ?_)
    by_cases hiU : i ∈ U
    · have hk : (⟨i, hiU⟩ : {k // k ∈ U}) ∈ D' b := by
        simp only [D', Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      rw [C.updOn_mem ω c ⟨i, hiU⟩, C.updOn_mem ω c' ⟨i, hiU⟩, hcc _ hk]
    · rw [C.updOn_not_mem ω c hiU, C.updOn_not_mem ω c' hiU]
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

/-- **Binary conditional factorization** (the pair case of `condCE_forgetSet_prod`).
For two functions on *disjoint* blocks, conditioning the product factors:
`E[f·g | 𝓕] = E[f | 𝓕]·E[g | 𝓕]` when `f` and `g` depend on disjoint blocks. -/
theorem condCE_forgetSet_mul (hpos : ∀ i c, 0 < C.coinMass i c) (U : Finset C.ι)
    {f g : (∀ i, C.Coin i) → ℝ} {Tf Tg : Finset C.ι}
    (hf : ∀ ω ω', (∀ i ∈ Tf, ω i = ω' i) → f ω = f ω')
    (hg : ∀ ω ω', (∀ i ∈ Tg, ω i = ω' i) → g ω = g ω')
    (hdisj : Disjoint Tf Tg) :
    condCE C.toFinProb (C.forgetSet U) (fun ω => f ω * g ω)
      = fun ω => condCE C.toFinProb (C.forgetSet U) f ω
                  * condCE C.toFinProb (C.forgetSet U) g ω := by
  have h := C.condCE_forgetSet_prod hpos U ![Tf, Tg] ![f, g] Finset.univ
    (fun b _ => by fin_cases b <;> assumption)
    (fun b _ b' _ hbb' => by
      fin_cases b <;> fin_cases b' <;>
        first
        | exact absurd rfl hbb'
        | exact hdisj
        | exact hdisj.symm)
  simpa [Fin.prod_univ_two] using h

end CoinSpace
end Arlib.Probability
