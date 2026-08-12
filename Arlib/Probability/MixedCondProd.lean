/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conditional disjoint-block product factorization over the continuous `MixedCoinSpace`

The continuous analogue of the finite `CoinSpace.condCE_forgetSet_mul`
(`Probability/CondExpProd.lean`).  For two bounded-measurable functions `f`, `g`
that read only the coins in **disjoint** blocks `Tf`, `Tg`, conditioning their
product on `forgetSet U` factors:

> `E[f·g | forgetSet U] = E[f | forgetSet U] · E[g | forgetSet U]`.

Route (mirrors the finite proof, but everything is a product-measure integral):

* `condCE_forgetSet U X ω = ∫ t, X (blockMerge U ω t) ∂(Measure.pi over U-block)`
  — definitional; `blockMerge` is the measure-preserving split's merge that keeps
  the coins outside `U` fixed at `ω` and takes the `U`-coins from `t`.
* `pi_prod_split` — the generic disjoint-block Fubini split (the function analogue
  of `MixedCoinSpace.Ex_prod_of_disjoint`, stated for an arbitrary probability
  family so the exact `Measure.pi` inside `condCE_forgetSet` is matched — no
  `Fintype`-instance folding), via `measurePreserving_piEquivPiSubtypeProd` +
  `integral_prod_mul` (both unconditional).
* `pi_integral_mul_of_disjoint` — `∫ F·G = (∫F)·(∫G)` for `F`, `G` on the full
  product depending on disjoint coordinate sets; obtained from `pi_prod_split`
  (once for the product, twice for the two marginals via a `const 1` block).
* `condCE_forgetSet_mul` — instantiate `pi_integral_mul_of_disjoint` inside the
  `U`-block integral with the predicate `(·.1 ∈ Tf)`; the disjointness of `Tf`,
  `Tg` gives the coordinate-set disjointness.

No `sorry`.  Pure product-measure algebra; no integrability side-condition
(`integral_prod_mul` is unconditional), so `hf`/`hg` are carried only to match the
finite statement's shape.

**Caller caveat (noted).**  The eventual `#DNNF` `cond_Alay` `×`-step has
`Tf`/`Tg` the coin-sets of the two children, which overlap on variable-free shared
subcircuits (threshold-1 coins, a.s. constant — see `DNNFChildIndep`).  That needs
an *a.e.-robust* variant `condCE_forgetSet_mul_ae` (given `f =ᵐ f'`, `g =ᵐ g'`
with `f'`/`g'` strictly disjoint-block-dependent), mirroring how
`Pr_inter_eq_mul_ae` upgraded `Pr_inter_eq_mul`.  This file ships the strict
version; the a.e. variant is the follow-up.
-/
import Arlib.Probability.MixedCoinSpace
import Arlib.Probability.MixedCondCELinear

namespace Arlib.Probability

open MeasureTheory
open scoped BigOperators

namespace MixedCoinSpace

/-! ## Generic disjoint-block Fubini split (measure-family generic)

Stated for an arbitrary probability family `ν` and predicate `q` (side-stepping
the in-context subtype folding, exactly like `MixedCoinSpace.condEx_aux`), so the
`Measure.pi` inside `condCE_forgetSet` is matched syntactically with its own
`Fintype` instance. -/

/-- **`pi_prod_split`** — the disjoint-block product split (function analogue of
`Ex_prod_of_disjoint`).  If `F` reads only the `q`-coordinates and `G` only the
`¬q`-coordinates, the full-product integral of `F·G` factors into the two block
integrals.  No integrability hypothesis (`integral_prod_mul` is unconditional). -/
private theorem pi_prod_split {ι : Type} [Fintype ι] {α : ι → Type}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (ν i)] (q : ι → Prop) [DecidablePred q]
    (F : ((i : Subtype q) → α i) → ℝ) (G : ((i : {i // ¬ q i}) → α i) → ℝ) :
    (∫ z, F (fun i : Subtype q => z i) * G (fun i : {i // ¬ q i} => z i)
        ∂(Measure.pi ν))
      = (∫ t, F t ∂(Measure.pi fun i : Subtype q => ν i))
        * (∫ r, G r ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := by
  have hmp := measurePreserving_piEquivPiSubtypeProd ν q
  rw [← integral_prod_mul F G, ← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  rfl

/-- **`pi_integral_mul_of_disjoint`** — the full-product form.  If `F` depends only
on the `q`-coordinates and `G` only on the `¬q`-coordinates, then
`∫ F·G = (∫F)·(∫G)` over the product measure.  No integrability side-condition. -/
private theorem pi_integral_mul_of_disjoint {ι : Type} [Fintype ι] {α : ι → Type}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (ν i)] (q : ι → Prop) [DecidablePred q]
    (F G : (∀ i, α i) → ℝ)
    (hFdep : ∀ z z', (∀ i, q i → z i = z' i) → F z = F z')
    (hGdep : ∀ z z', (∀ i, ¬ q i → z i = z' i) → G z = G z') :
    (∫ z, F z * G z ∂(Measure.pi ν))
      = (∫ z, F z ∂(Measure.pi ν)) * (∫ z, G z ∂(Measure.pi ν)) := by
  classical
  -- each coordinate space is nonempty (its measure is a probability measure)
  have hne : ∀ i, Nonempty (α i) := by
    intro i
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : (ν i) Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact one_ne_zero h1.symm
  set E := MeasurableEquiv.piEquivPiSubtypeProd α q with hE
  -- fixed reference points on the two blocks (irrelevant to `F`/`G` by dependence)
  set r₀ : (i : {i // ¬ q i}) → α i := fun i => (hne i.1).some with hr₀
  set a₀ : (i : Subtype q) → α i := fun i => (hne i.1).some with ha₀
  -- coordinate readout of the merge on the two blocks
  have hmem : ∀ (a : (i : Subtype q) → α i) (b : (i : {i // ¬ q i}) → α i)
      (i : ι) (hi : q i), (E.symm (a, b)) i = a ⟨i, hi⟩ := by
    intro a b i hi
    simp [hE, MeasurableEquiv.piEquivPiSubtypeProd, hi]
  have hnmem : ∀ (a : (i : Subtype q) → α i) (b : (i : {i // ¬ q i}) → α i)
      (i : ι) (hi : ¬ q i), (E.symm (a, b)) i = b ⟨i, hi⟩ := by
    intro a b i hi
    simp [hE, MeasurableEquiv.piEquivPiSubtypeProd, hi]
  -- `F` and `G` collapse to block functions
  have hFeq : ∀ z, F z = F (E.symm ((fun i : Subtype q => z i), r₀)) := by
    intro z
    apply hFdep
    intro i hi
    simp only [hmem (fun i : Subtype q => z i) r₀ i hi]
  have hGeq : ∀ z, G z = G (E.symm (a₀, (fun i : {i // ¬ q i} => z i))) := by
    intro z
    apply hGdep
    intro i hi
    simp only [hnmem a₀ (fun i : {i // ¬ q i} => z i) i hi]
  -- product
  have hA : (∫ z, F z * G z ∂(Measure.pi ν))
      = (∫ t, F (E.symm (t, r₀)) ∂(Measure.pi fun i : Subtype q => ν i))
        * (∫ r, G (E.symm (a₀, r)) ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := by
    rw [← pi_prod_split ν q (fun t => F (E.symm (t, r₀))) (fun r => G (E.symm (a₀, r)))]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [hFeq z, hGeq z]
  -- marginal of `F`
  have hB : (∫ z, F z ∂(Measure.pi ν))
      = (∫ t, F (E.symm (t, r₀)) ∂(Measure.pi fun i : Subtype q => ν i)) := by
    have hsplit := pi_prod_split ν q (fun t => F (E.symm (t, r₀)))
      (fun _ : (i : {i // ¬ q i}) → α i => (1 : ℝ))
    calc (∫ z, F z ∂(Measure.pi ν))
        = ∫ z, F (E.symm ((fun i : Subtype q => z i), r₀))
              * (fun _ : (i : {i // ¬ q i}) → α i => (1 : ℝ))
                  (fun i : {i // ¬ q i} => z i) ∂(Measure.pi ν) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall (fun z => ?_)
          simp only [mul_one]
          exact hFeq z
      _ = (∫ t, F (E.symm (t, r₀)) ∂(Measure.pi fun i : Subtype q => ν i))
            * (∫ r, (fun _ : (i : {i // ¬ q i}) → α i => (1 : ℝ)) r
                ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := hsplit
      _ = (∫ t, F (E.symm (t, r₀)) ∂(Measure.pi fun i : Subtype q => ν i)) * 1 := by
          congr 1; simp
      _ = _ := mul_one _
  -- marginal of `G`
  have hC : (∫ z, G z ∂(Measure.pi ν))
      = (∫ r, G (E.symm (a₀, r)) ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := by
    have hsplit := pi_prod_split ν q
      (fun _ : (i : Subtype q) → α i => (1 : ℝ)) (fun r => G (E.symm (a₀, r)))
    calc (∫ z, G z ∂(Measure.pi ν))
        = ∫ z, (fun _ : (i : Subtype q) → α i => (1 : ℝ))
                  (fun i : Subtype q => z i)
              * G (E.symm (a₀, (fun i : {i // ¬ q i} => z i))) ∂(Measure.pi ν) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall (fun z => ?_)
          simp only [one_mul]
          exact hGeq z
      _ = (∫ t, (fun _ : (i : Subtype q) → α i => (1 : ℝ)) t
                ∂(Measure.pi fun i : Subtype q => ν i))
            * (∫ r, G (E.symm (a₀, r)) ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := hsplit
      _ = 1 * (∫ r, G (E.symm (a₀, r)) ∂(Measure.pi fun i : {i // ¬ q i} => ν i)) := by
          congr 1; simp
      _ = _ := one_mul _
  rw [hA, hB, hC]

/-! ## The `U`-block merge and the `condCE_forgetSet` integral form -/

variable (C : MixedCoinSpace)

/-- The `U`-block **merge**: keeps the coins outside `U` fixed at `ω`, takes the
`U`-coins from `t`.  This is exactly the point integrated over in
`condCE_forgetSet U · ω`. -/
noncomputable def blockMerge (U : Finset C.ι) (ω : C.Ω)
    (t : (i : {i // i ∈ U}) → C.Coin i) : C.Ω :=
  (MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ U)).symm
    (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ U)) ω).2)

/-- `condCE_forgetSet` as an integral of `X ∘ blockMerge` over the `U`-block. -/
theorem condCE_forgetSet_eq_blockMerge (U : Finset C.ι) (X : C.Ω → ℝ) (ω : C.Ω) :
    C.condCE_forgetSet U X ω
      = ∫ t, X (C.blockMerge U ω t) ∂(Measure.pi fun i : {i // i ∈ U} => C.μ i) := rfl

/-- On the `U`-coins the merge reads `t`. -/
theorem blockMerge_mem (U : Finset C.ι) (ω : C.Ω)
    (t : (i : {i // i ∈ U}) → C.Coin i) {k : C.ι} (hk : k ∈ U) :
    C.blockMerge U ω t k = t ⟨k, hk⟩ :=
  C.forgetSet_merge_mem U t ω hk

/-- Off the `U`-coins the merge reads `ω`. -/
theorem blockMerge_outside (U : Finset C.ι) (ω : C.Ω)
    (t : (i : {i // i ∈ U}) → C.Coin i) {k : C.ι} (hk : k ∉ U) :
    C.blockMerge U ω t k = ω k :=
  C.forgetSet_merge_eq_outside U t ω hk

/-! ## The strict conditional disjoint-block product factorization -/

/-- **`condCE_forgetSet_mul`** — the continuous analogue of the finite
`CoinSpace.condCE_forgetSet_mul`.  If `f` reads only the coins in `Tf` and `g`
only the coins in `Tg` with `Tf`, `Tg` **disjoint**, then conditioning `f·g` on
`forgetSet U` factors into the two conditional expectations.  No integrability
side-condition is needed; `hf`/`hg` are carried only to match the finite shape. -/
theorem condCE_forgetSet_mul (U : Finset C.ι) {f g : C.Ω → ℝ} {Tf Tg : Finset C.ι}
    (_hf : C.BddMeas f) (_hg : C.BddMeas g)
    (hfdep : ∀ ω ω', (∀ i ∈ Tf, ω i = ω' i) → f ω = f ω')
    (hgdep : ∀ ω ω', (∀ i ∈ Tg, ω i = ω' i) → g ω = g ω')
    (hdisj : Disjoint Tf Tg) :
    C.condCE_forgetSet U (fun ω => f ω * g ω)
      = fun ω => C.condCE_forgetSet U f ω * C.condCE_forgetSet U g ω := by
  funext ω
  rw [condCE_forgetSet_eq_blockMerge, condCE_forgetSet_eq_blockMerge,
    condCE_forgetSet_eq_blockMerge]
  have hFdep : ∀ z z' : (i : {i // i ∈ U}) → C.Coin i,
      (∀ i, (i.1 ∈ Tf) → z i = z' i) →
      f (C.blockMerge U ω z) = f (C.blockMerge U ω z') := by
    intro z z' hzz
    apply hfdep
    intro k hk
    by_cases hkU : k ∈ U
    · rw [C.blockMerge_mem U ω z hkU, C.blockMerge_mem U ω z' hkU]
      exact hzz ⟨k, hkU⟩ hk
    · rw [C.blockMerge_outside U ω z hkU, C.blockMerge_outside U ω z' hkU]
  have hGdep : ∀ z z' : (i : {i // i ∈ U}) → C.Coin i,
      (∀ i, ¬ (i.1 ∈ Tf) → z i = z' i) →
      g (C.blockMerge U ω z) = g (C.blockMerge U ω z') := by
    intro z z' hzz
    apply hgdep
    intro k hk
    by_cases hkU : k ∈ U
    · rw [C.blockMerge_mem U ω z hkU, C.blockMerge_mem U ω z' hkU]
      exact hzz ⟨k, hkU⟩ (fun hkf => (Finset.disjoint_left.1 hdisj hkf) hk)
    · rw [C.blockMerge_outside U ω z hkU, C.blockMerge_outside U ω z' hkU]
  exact pi_integral_mul_of_disjoint (fun i : {i // i ∈ U} => C.μ i)
    (fun i => i.1 ∈ Tf) (fun t => f (C.blockMerge U ω t))
    (fun t => g (C.blockMerge U ω t)) hFdep hGdep

/-! ## The n-ary strict conditional disjoint-block product factorization -/

/-- **`condCE_forgetSet_prod_disjoint`** — the `n`-ary generalization of the binary
`condCE_forgetSet_mul`.  If the family `f i` (for `i ∈ s`) reads pairwise-**disjoint**
coordinate blocks `T i` (each `f i` depends only on the coins in `T i`), then
conditioning their finite product on `forgetSet U` factors into the finite product
of the per-factor conditional expectations:

> `E[∏ᵢ fᵢ | forgetSet U] = ∏ᵢ E[fᵢ | forgetSet U]`.

Proved by `Finset.induction` on `s`: peel one factor `a`; the remaining product
depends on `⋃_{i∈s} T i`, which is disjoint from `T a`, so the binary
`condCE_forgetSet_mul` splits off the head factor and the induction hypothesis
closes the tail.  No integrability side-condition (inherited from the binary
version); `hf` is carried for the binary-shape match and the product-boundedness. -/
theorem condCE_forgetSet_prod_disjoint (U : Finset C.ι) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → C.Ω → ℝ) (T : ι → Finset C.ι)
    (hf : ∀ i ∈ s, C.BddMeas (f i))
    (hdep : ∀ i ∈ s, ∀ ω ω' : C.Ω, (∀ k ∈ T i, ω k = ω' k) → f i ω = f i ω')
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (T i) (T i')) :
    C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f i ω)
      = fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f i) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty]
      exact C.condCE_of_forgetSet_CFixed U (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  | @insert a s ha ih =>
      have hf' : ∀ i ∈ s, C.BddMeas (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hdep' : ∀ i ∈ s, ∀ ω ω' : C.Ω, (∀ k ∈ T i, ω k = ω' k) → f i ω = f i ω' :=
        fun i hi => hdep i (Finset.mem_insert_of_mem hi)
      have hdisj' : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (T i) (T i') :=
        fun i hi i' hi' => hdisj i (Finset.mem_insert_of_mem hi) i'
          (Finset.mem_insert_of_mem hi')
      have ihs := ih hf' hdep' hdisj'
      set g : C.Ω → ℝ := fun ω => ∏ i ∈ s, f i ω with hg
      have hgbdd : C.BddMeas g := C.BddMeas_prod s f hf'
      have hgdep : ∀ ω ω' : C.Ω, (∀ k ∈ s.biUnion T, ω k = ω' k) → g ω = g ω' := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro i hi
        exact hdep' i hi ω ω' (fun k hk =>
          hagree k (Finset.mem_biUnion.mpr ⟨i, hi, hk⟩))
      have hdisjA : Disjoint (T a) (s.biUnion T) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact ha hi)
      have hbin := C.condCE_forgetSet_mul U (hf a (Finset.mem_insert_self a s)) hgbdd
        (hdep a (Finset.mem_insert_self a s)) hgdep hdisjA
      have hLrw : (fun ω => ∏ i ∈ insert a s, f i ω) = (fun ω => f a ω * g ω) := by
        funext ω; rw [Finset.prod_insert ha]
      rw [hLrw, hbin]
      funext ω
      rw [Finset.prod_insert ha]
      show C.condCE_forgetSet U (f a) ω * C.condCE_forgetSet U g ω = _
      rw [ihs]

/-! ## The *forgotten-block* refinement (disjointness only inside `U`)

The strict `condCE_forgetSet_mul` demands the two dependence blocks `Tf`, `Tg` be
**globally** disjoint.  For the `#DNNF` square collapse this is *too strong*: two cut
atoms at distinct level-`j` nodes share their *fixed* (non-forgotten) descendant
coins, yet each depends on a *disjoint forgotten coin* (its own top `S`-role coin at
level `j`).  Conditioning integrates only over the forgotten block `U`, so the
factorization needs disjointness of `Tf ∩ U` and `Tg ∩ U`, **not** of `Tf`, `Tg`.
The proof is the strict one verbatim, weakening the disjointness discharge. -/

/-- **`condCE_forgetSet_mul_forget`** — the forgotten-block binary factorization.  If
`f` reads only `Tf` and `g` only `Tg`, and the two blocks are disjoint *inside the
forgotten set `U`* (`Disjoint (Tf ∩ U) (Tg ∩ U)`), then conditioning `f·g` on
`forgetSet U` factors.  Strictly stronger than `condCE_forgetSet_mul`
(`Disjoint Tf Tg ⟹ Disjoint (Tf ∩ U) (Tg ∩ U)`). -/
theorem condCE_forgetSet_mul_forget (U : Finset C.ι) {f g : C.Ω → ℝ}
    {Tf Tg : Finset C.ι} (_hf : C.BddMeas f) (_hg : C.BddMeas g)
    (hfdep : ∀ ω ω', (∀ i ∈ Tf, ω i = ω' i) → f ω = f ω')
    (hgdep : ∀ ω ω', (∀ i ∈ Tg, ω i = ω' i) → g ω = g ω')
    (hdisj : Disjoint (Tf ∩ U) (Tg ∩ U)) :
    C.condCE_forgetSet U (fun ω => f ω * g ω)
      = fun ω => C.condCE_forgetSet U f ω * C.condCE_forgetSet U g ω := by
  funext ω
  rw [condCE_forgetSet_eq_blockMerge, condCE_forgetSet_eq_blockMerge,
    condCE_forgetSet_eq_blockMerge]
  have hFdep : ∀ z z' : (i : {i // i ∈ U}) → C.Coin i,
      (∀ i, (i.1 ∈ Tf) → z i = z' i) →
      f (C.blockMerge U ω z) = f (C.blockMerge U ω z') := by
    intro z z' hzz
    apply hfdep
    intro k hk
    by_cases hkU : k ∈ U
    · rw [C.blockMerge_mem U ω z hkU, C.blockMerge_mem U ω z' hkU]
      exact hzz ⟨k, hkU⟩ hk
    · rw [C.blockMerge_outside U ω z hkU, C.blockMerge_outside U ω z' hkU]
  have hGdep : ∀ z z' : (i : {i // i ∈ U}) → C.Coin i,
      (∀ i, ¬ (i.1 ∈ Tf) → z i = z' i) →
      g (C.blockMerge U ω z) = g (C.blockMerge U ω z') := by
    intro z z' hzz
    apply hgdep
    intro k hk
    by_cases hkU : k ∈ U
    · rw [C.blockMerge_mem U ω z hkU, C.blockMerge_mem U ω z' hkU]
      refine hzz ⟨k, hkU⟩ (fun hkf => ?_)
      exact Finset.disjoint_left.1 hdisj (Finset.mem_inter.2 ⟨hkf, hkU⟩)
        (Finset.mem_inter.2 ⟨hk, hkU⟩)
    · rw [C.blockMerge_outside U ω z hkU, C.blockMerge_outside U ω z' hkU]
  exact pi_integral_mul_of_disjoint (fun i : {i // i ∈ U} => C.μ i)
    (fun i => i.1 ∈ Tf) (fun t => f (C.blockMerge U ω t))
    (fun t => g (C.blockMerge U ω t)) hFdep hGdep

/-- **`condCE_forgetSet_prod_disjoint_forget`** — the `n`-ary forgotten-block
factorization.  If the family `f i` (for `i ∈ s`) reads blocks `T i` that are
pairwise disjoint *inside the forgotten set `U`* (`Disjoint (T i ∩ U) (T i' ∩ U)`),
then conditioning their finite product on `forgetSet U` factors into the finite
product of the per-factor conditionals.  `Finset.induction` peeling one factor, via
the binary `condCE_forgetSet_mul_forget`. -/
theorem condCE_forgetSet_prod_disjoint_forget (U : Finset C.ι) {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f : ι → C.Ω → ℝ) (T : ι → Finset C.ι)
    (hf : ∀ i ∈ s, C.BddMeas (f i))
    (hdep : ∀ i ∈ s, ∀ ω ω' : C.Ω, (∀ k ∈ T i, ω k = ω' k) → f i ω = f i ω')
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (T i ∩ U) (T i' ∩ U)) :
    C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f i ω)
      = fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f i) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty]
      exact C.condCE_of_forgetSet_CFixed U (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  | @insert a s ha ih =>
      have hf' : ∀ i ∈ s, C.BddMeas (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hdep' : ∀ i ∈ s, ∀ ω ω' : C.Ω, (∀ k ∈ T i, ω k = ω' k) → f i ω = f i ω' :=
        fun i hi => hdep i (Finset.mem_insert_of_mem hi)
      have hdisj' : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (T i ∩ U) (T i' ∩ U) :=
        fun i hi i' hi' => hdisj i (Finset.mem_insert_of_mem hi) i'
          (Finset.mem_insert_of_mem hi')
      have ihs := ih hf' hdep' hdisj'
      set g : C.Ω → ℝ := fun ω => ∏ i ∈ s, f i ω with hg
      have hgbdd : C.BddMeas g := C.BddMeas_prod s f hf'
      have hgdep : ∀ ω ω' : C.Ω, (∀ k ∈ s.biUnion T, ω k = ω' k) → g ω = g ω' := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro i hi
        exact hdep' i hi ω ω' (fun k hk =>
          hagree k (Finset.mem_biUnion.mpr ⟨i, hi, hk⟩))
      have hdisjA : Disjoint (T a ∩ U) ((s.biUnion T) ∩ U) := by
        rw [Finset.disjoint_left]
        intro k hka hks
        rw [Finset.mem_inter] at hka hks
        obtain ⟨hkTa, hkU⟩ := hka
        obtain ⟨hkbi, _⟩ := hks
        rw [Finset.mem_biUnion] at hkbi
        obtain ⟨i, hi, hkTi⟩ := hkbi
        exact Finset.disjoint_left.1
          (hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (by rintro rfl; exact ha hi))
          (Finset.mem_inter.2 ⟨hkTa, hkU⟩) (Finset.mem_inter.2 ⟨hkTi, hkU⟩)
      have hbin := C.condCE_forgetSet_mul_forget U
        (hf a (Finset.mem_insert_self a s)) hgbdd
        (hdep a (Finset.mem_insert_self a s)) hgdep hdisjA
      have hLrw : (fun ω => ∏ i ∈ insert a s, f i ω) = (fun ω => f a ω * g ω) := by
        funext ω; rw [Finset.prod_insert ha]
      rw [hLrw, hbin]
      funext ω
      rw [Finset.prod_insert ha]
      show C.condCE_forgetSet U (f a) ω * C.condCE_forgetSet U g ω = _
      rw [ihs]

/-- **`prod_congr_ae`** — a finite product respects pointwise a.e. equality of its
factors. -/
theorem prod_congr_ae {ι : Type} [DecidableEq ι] (s : Finset ι)
    (a b : ι → C.Ω → ℝ) (h : ∀ i ∈ s, a i =ᵐ[C.measure] b i) :
    (fun ω => ∏ i ∈ s, a i ω) =ᵐ[C.measure] (fun ω => ∏ i ∈ s, b i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; rfl
  | @insert x s hx ih =>
      have h1 := h x (Finset.mem_insert_self x s)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      filter_upwards [h1, h2] with ω e1 e2
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      show a x ω * ∏ i ∈ s, a i ω = b x ω * ∏ i ∈ s, b i ω
      rw [e1]
      exact congrArg (b x ω * ·) e2

/-- **`condCE_forgetSet_prod_disjoint_forget_ae`** — the a.e. forgotten-block
factorization.  Each factor `f i` is a.e. equal to a *strictly* block-dependent
`f' i` (depending only on `T i`), with the `T i` pairwise disjoint inside `U`.  Then
conditioning `∏ f i` factors a.e. into `∏ cond (f i)`.  Route (mirrors
`cond_Alay_mul_disjoint_ae`): a.e.-reduce the product to the `f'` version, apply the
strict `condCE_forgetSet_prod_disjoint_forget`, transport each factor back a.e. -/
theorem condCE_forgetSet_prod_disjoint_forget_ae (U : Finset C.ι) {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f f' : ι → C.Ω → ℝ) (T : ι → Finset C.ι)
    (hf : ∀ i ∈ s, C.BddMeas (f i)) (hf' : ∀ i ∈ s, C.BddMeas (f' i))
    (hae : ∀ i ∈ s, f i =ᵐ[C.measure] f' i)
    (hdep' : ∀ i ∈ s, ∀ ω ω' : C.Ω, (∀ k ∈ T i, ω k = ω' k) → f' i ω = f' i ω')
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (T i ∩ U) (T i' ∩ U)) :
    C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f i ω)
      =ᵐ[C.measure] fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f i) ω := by
  classical
  have hprodbdd : C.BddMeas (fun ω => ∏ i ∈ s, f i ω) := C.BddMeas_prod s f hf
  have hprodbdd' : C.BddMeas (fun ω => ∏ i ∈ s, f' i ω) := C.BddMeas_prod s f' hf'
  -- Step 1: a.e.-reduce `∏ f` to `∏ f'`.
  have hprodae : (fun ω => ∏ i ∈ s, f i ω) =ᵐ[C.measure] (fun ω => ∏ i ∈ s, f' i ω) :=
    C.prod_congr_ae s f f' hae
  have hstep1 : C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f i ω)
      =ᵐ[C.measure] C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f' i ω) :=
    C.condCE_forgetSet_congr_ae U hprodbdd hprodbdd' hprodae
  -- Step 2: strict forgotten-block factorization on the `f'` version.
  have hstep2 : C.condCE_forgetSet U (fun ω => ∏ i ∈ s, f' i ω)
      = fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f' i) ω :=
    C.condCE_forgetSet_prod_disjoint_forget U s f' T hf' hdep' hdisj
  -- Step 3: transport each conditioned factor back a.e.
  have hstep3 : (fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f' i) ω)
      =ᵐ[C.measure] fun ω => ∏ i ∈ s, C.condCE_forgetSet U (f i) ω :=
    C.prod_congr_ae s (fun i => C.condCE_forgetSet U (f' i))
      (fun i => C.condCE_forgetSet U (f i))
      (fun i hi => (C.condCE_forgetSet_congr_ae U (hf' i hi) (hf i hi)
        (hae i hi).symm))
  exact (hstep1.trans (hstep2 ▸ hstep3))

end MixedCoinSpace
end Arlib.Probability
