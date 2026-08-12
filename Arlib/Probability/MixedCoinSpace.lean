/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The mixed finite × [0,1] product space (`MixedCoinSpace`)

Generalizes `Probability/ProductSpace.lean`'s `CoinSpace` from a finite product
of counting-measure coins to a product of **arbitrary probability-measure**
coins — in particular allowing continuous `[0,1]`-uniform "keep-coins"
(`volume.restrict (Icc 0 1)`) alongside finite draw-coins.  The execution space
is `Ω = ∀ i, Coin i` and the expectation is the product integral
`Ex X = ∫ ω, X ω ∂(Measure.pi μ)` (a probability measure), exactly the shape of
`ContCoinProto.Ex`.

The pointwise coordinate marginal `condCE_forget j X ω = ∫ c, X(ω[j:=c]) ∂(μ j)`
mirrors `ContCoinProto.condCE_forget`; for a `[0,1]`-uniform coin it reduces to
the prototype's `Eu_threshold` step-function identity.

**Integrability note (see the ProbSpace-instance section).**  `Ex_const`,
`Ex_smul`, `Ex_nonneg` hold *unconditionally* and are proved here.  `Ex_add`,
`Ex_mono`, `Ex_sum` require `Integrable` hypotheses: Bochner integrals are only
linear / monotone on integrable functions (there is no unconditional Mathlib
result, and these statements are genuinely false without integrability).  They
are therefore proved here in their *integrable* forms, so a `ProbSpace` instance
demanding unconditional `Ex_add`/`Ex_mono`/`Ex_sum` cannot be built over this
space.
-/
import Arlib.Probability.ProbSpace
import Arlib.Probability.ContCoinProto
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace Arlib.Probability

open MeasureTheory
open scoped BigOperators

/-- A finite family of independent coins, each an arbitrary probability space.
Finite draw-coins take `Coin i = Fin K` with a counting/uniform probability
measure; continuous keep-coins take `Coin i = ℝ` with `volume.restrict
(Icc 0 1)`.  This is the measure-theoretic generalization of `CoinSpace`. -/
structure MixedCoinSpace where
  ι : Type
  [ιFin : Fintype ι]
  [ιDec : DecidableEq ι]
  Coin : ι → Type
  [coinMS : ∀ i, MeasurableSpace (Coin i)]
  μ : ∀ i, Measure (Coin i)
  [isProb : ∀ i, IsProbabilityMeasure (μ i)]

attribute [instance] MixedCoinSpace.ιFin MixedCoinSpace.ιDec
  MixedCoinSpace.coinMS MixedCoinSpace.isProb

namespace MixedCoinSpace

variable (C : MixedCoinSpace)

/-- The outcome space: joint coin assignments. -/
abbrev Ω : Type := ∀ i, C.Coin i

/-- The product `[0,1]`-uniform-style probability measure on `Ω`. -/
noncomputable def measure : Measure C.Ω := Measure.pi C.μ

instance : IsProbabilityMeasure C.measure := by
  unfold measure; infer_instance

/-- Every coin is nonempty (its measure is a probability measure). -/
theorem coin_nonempty (j : C.ι) : Nonempty (C.Coin j) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : (C.μ j) Set.univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
  exact one_ne_zero this.symm

/-- A canonical point of coin `j`. -/
noncomputable def coinPt (j : C.ι) : C.Coin j := (C.coin_nonempty j).some

/-! ## Expectation and the three *unconditional* `Ex` axioms -/

/-- Expectation `Ex[X] = ∫ ω, X ω ∂(Measure.pi μ)`. -/
noncomputable def Ex (X : C.Ω → ℝ) : ℝ := ∫ ω, X ω ∂C.measure

/-- **`Ex_const`** (unconditional): total mass one. -/
theorem Ex_const (c : ℝ) : C.Ex (fun _ => c) = c := by
  unfold Ex; rw [integral_const, MeasureTheory.measureReal_def, measure_univ]; simp

/-- **`Ex_smul`** (unconditional): `integral_const_mul` needs no integrability. -/
theorem Ex_smul (c : ℝ) (X : C.Ω → ℝ) : C.Ex (fun ω => c * X ω) = c * C.Ex X := by
  unfold Ex; exact integral_const_mul c X

/-- **`Ex_nonneg`** (unconditional): `integral_nonneg`. -/
theorem Ex_nonneg {X : C.Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ C.Ex X :=
  integral_nonneg h

/-! ## Admissibility = bounded + measurable

`Adm := BddMeas` (bounded and measurable).  On this probability measure every
such function is integrable, and `BddMeas` is closed under `+`, `•`, `*`, and
finite sums — giving the cleanest closure surface (products included). -/

/-- Bounded-and-measurable functions: the admissibility class of `MixedCoinSpace`. -/
def BddMeas (X : C.Ω → ℝ) : Prop := Measurable X ∧ ∃ C₀ : ℝ, ∀ ω, |X ω| ≤ C₀

/-- Bounded-measurable ⇒ integrable (finite/probability measure). -/
theorem BddMeas.integrable {X : C.Ω → ℝ} (h : C.BddMeas X) : Integrable X C.measure := by
  obtain ⟨hmeas, C₀, hb⟩ := h
  refine (integrable_const C₀).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro ω; rw [Real.norm_eq_abs]; exact hb ω

theorem BddMeas_const (c : ℝ) : C.BddMeas (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ => le_refl _⟩

theorem BddMeas_add {X Y : C.Ω → ℝ} (hX : C.BddMeas X) (hY : C.BddMeas Y) :
    C.BddMeas (fun ω => X ω + Y ω) := by
  obtain ⟨hmX, CX, hbX⟩ := hX; obtain ⟨hmY, CY, hbY⟩ := hY
  exact ⟨hmX.add hmY, CX + CY, fun ω => (abs_add_le _ _).trans (add_le_add (hbX ω) (hbY ω))⟩

theorem BddMeas_smul (c : ℝ) {X : C.Ω → ℝ} (hX : C.BddMeas X) :
    C.BddMeas (fun ω => c * X ω) := by
  obtain ⟨hmX, CX, hbX⟩ := hX
  refine ⟨hmX.const_mul c, |c| * CX, fun ω => ?_⟩
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbX ω) (abs_nonneg c)

theorem BddMeas_mul {X Y : C.Ω → ℝ} (hX : C.BddMeas X) (hY : C.BddMeas Y) :
    C.BddMeas (fun ω => X ω * Y ω) := by
  obtain ⟨hmX, CX, hbX⟩ := hX; obtain ⟨hmY, CY, hbY⟩ := hY
  refine ⟨hmX.mul hmY, CX * CY, fun ω => ?_⟩
  rw [abs_mul]
  have hCX : 0 ≤ CX := le_trans (abs_nonneg _) (hbX ω)
  exact mul_le_mul (hbX ω) (hbY ω) (abs_nonneg _) hCX

theorem BddMeas_sum {ι : Type} (s : Finset ι) (X : ι → C.Ω → ℝ)
    (hX : ∀ i ∈ s, C.BddMeas (X i)) : C.BddMeas (fun ω => ∑ i ∈ s, X i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using C.BddMeas_const 0
  | @insert a s ha ih =>
      have hrest := ih (fun i hi => hX i (Finset.mem_insert_of_mem hi))
      have hcomb := C.BddMeas_add (hX a (Finset.mem_insert_self a s)) hrest
      simpa [Finset.sum_insert ha] using hcomb

/-! ## The three *conditional* `Ex` axioms (integrable forms)

These are **false without `Integrable`** (see the file header), so they cannot
fill the unconditional `ProbSpace` fields.  They are recorded in their correct
integrable forms; on this probability space `Integrable` is discharged from
bounded-measurability for every bounded measurable function. -/

theorem Ex_add_of_integrable {X Y : C.Ω → ℝ}
    (hX : Integrable X C.measure) (hY : Integrable Y C.measure) :
    C.Ex (fun ω => X ω + Y ω) = C.Ex X + C.Ex Y := by
  unfold Ex; exact integral_add hX hY

theorem Ex_mono_of_integrable {X Y : C.Ω → ℝ}
    (hX : Integrable X C.measure) (hY : Integrable Y C.measure)
    (h : ∀ ω, X ω ≤ Y ω) : C.Ex X ≤ C.Ex Y := by
  unfold Ex; exact integral_mono hX hY h

theorem Ex_sum_of_integrable {ι : Type} (s : Finset ι) (X : ι → C.Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) C.measure) :
    C.Ex (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, C.Ex (X i) := by
  unfold Ex; exact integral_finsetSum s hX

/-! ## The pointwise coordinate marginal -/

/-- **Pointwise coordinate marginal.**  `condCE_forget j X ω` replaces coin `j`
by the `μ j`-integration variable and integrates — the exact analogue of
`ContCoinProto.condCE_forget` and of `CoinSpace.condCE_forget`, but for a general
probability coin.  Everywhere-defined; no a.e. class. -/
noncomputable def condCE_forget (j : C.ι) (X : C.Ω → ℝ) (ω : C.Ω) : ℝ :=
  ∫ c, X (Function.update ω j c) ∂(C.μ j)

/-! ## Coordinate-congruence predicates (`forgetSet`, `CFixed`, `CSub`)

Ported unchanged (same meaning) from `CoinSpace`. -/

/-- The observable that forgets all coins in `T` (observes the coins outside `T`). -/
noncomputable def forgetSet (T : Finset C.ι) : C.Ω → C.Ω :=
  fun ω i => if i ∈ T then C.coinPt i else ω i

/-- `forget j` is `forgetSet {j}`. -/
noncomputable def forget (j : C.ι) : C.Ω → C.Ω := C.forgetSet {j}

/-- `X` is fixed by `forgetSet T`: constant on the fibers of `forgetSet T`. -/
def CFixed (π : C.Ω → C.Ω) (X : C.Ω → ℝ) : Prop :=
  ∀ a b, π a = π b → X a = X b

/-- `π₂` refines `π₁`. -/
def CSub (π₁ π₂ : C.Ω → C.Ω) : Prop :=
  ∀ a b, π₂ a = π₂ b → π₁ a = π₁ b

theorem forgetSet_eq_iff (T : Finset C.ι) (ω ω' : C.Ω) :
    C.forgetSet T ω' = C.forgetSet T ω ↔ ∀ i, i ∉ T → ω' i = ω i := by
  unfold forgetSet
  constructor
  · intro h i hiT
    have := congrFun h i
    simpa [hiT] using this
  · intro h
    funext i
    by_cases hiT : i ∈ T
    · simp [hiT]
    · simp only [if_neg hiT]; exact h i hiT

/-- A function depending only on coins outside `T` is fixed by `forgetSet T`. -/
theorem CFixed_forgetSet (T : Finset C.ι) (X : C.Ω → ℝ)
    (h : ∀ ω ω', (∀ i, i ∉ T → ω i = ω' i) → X ω = X ω') :
    C.CFixed (C.forgetSet T) X := by
  intro a b hab
  rw [forgetSet_eq_iff] at hab
  exact h a b (fun i hi => hab i hi)

/-- Observing more coins is finer: `T₂ ⊆ T₁ ⟹ forgetSet T₁ ⊆ forgetSet T₂`. -/
theorem CSub_forgetSet {T₁ T₂ : Finset C.ι} (hT : T₂ ⊆ T₁) :
    C.CSub (C.forgetSet T₁) (C.forgetSet T₂) := by
  intro a b hab
  rw [forgetSet_eq_iff] at hab ⊢
  intro i hi
  exact hab i (fun h => hi (hT h))

theorem forget_eq_forgetSet_singleton (j : C.ι) : C.forget j = C.forgetSet {j} := rfl

/-! ## Single-coordinate marginal identities (reduce to the prototype)

`condCE_const_of_pos` becomes automatic (mass one, no positivity needed);
`condCE_of_CFixed` is the "reads only other coords" collapse. -/

/-- **`condCE_const_of_pos`** (mass one ⇒ no positivity hypothesis).  The
marginal of a constant is the constant. -/
theorem condCE_const (j : C.ι) (g : ℝ) (ω : C.Ω) :
    C.condCE_forget j (fun _ => g) ω = g := by
  unfold condCE_forget
  rw [integral_const, MeasureTheory.measureReal_def, measure_univ]; simp

/-- If `X` does not read coin `j` (invariant under overwriting it), its marginal
is itself — the continuous analogue of `condCE_const_of_pos`/`condCE_of_CFixed`
for a single coordinate. -/
theorem condCE_forget_indep (j : C.ι) (X : C.Ω → ℝ)
    (hX : ∀ ω c, X (Function.update ω j c) = X ω) (ω : C.Ω) :
    C.condCE_forget j X ω = X ω := by
  unfold condCE_forget
  have h : (fun c => X (Function.update ω j c)) = fun _ => X ω := by
    funext c; exact hX ω c
  rw [h, integral_const, MeasureTheory.measureReal_def, measure_univ]; simp

/-- Overwriting coin `j` does not change `forget j`. -/
theorem forget_update (j : C.ι) (ω : C.Ω) (c : C.Coin j) :
    C.forget j (Function.update ω j c) = C.forget j ω := by
  rw [forget_eq_forgetSet_singleton, forgetSet_eq_iff]
  intro i hi
  rw [Function.update_of_ne (by simpa using hi)]

/-- **`condCE_of_CFixed`** (single coordinate).  If `X` is fixed by `forget j`
(reads only the other coins), its coordinate marginal returns it, everywhere. -/
theorem condCE_of_CFixed (j : C.ι) (X : C.Ω → ℝ)
    (hX : C.CFixed (C.forget j) X) (ω : C.Ω) :
    C.condCE_forget j X ω = X ω :=
  C.condCE_forget_indep j X (fun ζ c => hX _ _ (C.forget_update j ζ c)) ω

/-! ## `MixedCoinSpace` as a `ProbSpace`

`Adm := BddMeas`; the three guarded axioms are `integral_add`/`mono`/`finset_sum`
under the discharged integrability of bounded-measurable functions. -/

/-- The `ProbSpace` structure carried by a `MixedCoinSpace`. -/
@[reducible] noncomputable def toProbSpace : ProbSpace where
  Ω := C.Ω
  Ex := C.Ex
  Adm := C.BddMeas
  Ex_const := C.Ex_const
  Ex_smul := C.Ex_smul
  Ex_nonneg := fun {_} h => C.Ex_nonneg h
  Ex_add_adm := fun {_ _} hX hY => C.Ex_add_of_integrable hX.integrable hY.integrable
  Ex_mono_adm := fun {_ _} hX hY h => C.Ex_mono_of_integrable hX.integrable hY.integrable h
  Ex_sum_adm := fun {_} s X hX =>
    C.Ex_sum_of_integrable s X (fun i hi => (hX i hi).integrable)
  Adm_const := C.BddMeas_const
  Adm_add := fun {_ _} hX hY => C.BddMeas_add hX hY
  Adm_smul := fun c {_} hX => C.BddMeas_smul c hX
  Adm_mul := fun {_ _} hX hY => C.BddMeas_mul hX hY
  Adm_sum := fun {_} s X hX => C.BddMeas_sum s X hX

@[simp] theorem toProbSpace_Ω : C.toProbSpace.Ω = C.Ω := rfl
@[simp] theorem toProbSpace_Ex (X : C.Ω → ℝ) : C.toProbSpace.Ex X = C.Ex X := rfl
@[simp] theorem toProbSpace_Adm (X : C.Ω → ℝ) : C.toProbSpace.Adm X ↔ C.BddMeas X := Iff.rfl

/-! ### `IsAdm` building-block instances over the continuous model

So `[IsAdm …]` binders auto-fill from bounded-measurable atoms
(coordinate projections, constants, indicators of measurable events) closed under
`+`, `•`, `*`, `∑`.  The closure instances are inherited from `ProbSpace`; here we
supply the atoms specific to the coin product. -/

/-- Constants are admissible (atom). -/
instance isAdm_const (c : ℝ) : IsAdm C.toProbSpace (fun _ => c) := ⟨C.BddMeas_const c⟩

/-- A coordinate projection composed with a bounded-measurable map is admissible;
in particular a bounded-measurable function of the coins is admissible. -/
theorem isAdm_of_bddMeas {X : C.Ω → ℝ} (h : C.BddMeas X) : IsAdm C.toProbSpace X := ⟨h⟩

/-! ## Coordinate independence — the 2-coord Fubini factorization

This is the one genuinely measure-theoretic step (flagged as the non-trivial
import).  It goes through `measurePreserving_piEquivPiSubtypeProd` (the
measure-preserving split `Ω ≅ (∏_{p} Coin) × (∏_{¬p} Coin)`) composed with
`integral_prod_mul` (`∫ f(z.1)·g(z.2) = (∫f)·(∫g)`).  **It held, and needs no
integrability side-condition** (`integral_prod_mul` is unconditional). -/

/-- **`Ex_prod_of_disjoint`** — coordinate independence.  If `F` reads only the
coins with `p i` and `G` only the coins with `¬ p i`, then `Ex[F·G] = Ex[F]·Ex[G]`.
The product-measure independence of the coin family; no integrability hypothesis. -/
theorem Ex_prod_of_disjoint (p : C.ι → Prop) [DecidablePred p]
    (F : ((i : Subtype p) → C.Coin i) → ℝ)
    (G : ((i : {i // ¬ p i}) → C.Coin i) → ℝ) :
    C.Ex (fun ω => F (fun i : Subtype p => ω i) * G (fun i : {i // ¬ p i} => ω i))
      = (∫ t, F t ∂(Measure.pi fun i : Subtype p => C.μ i))
        * (∫ r, G r ∂(Measure.pi fun i : {i // ¬ p i} => C.μ i)) := by
  unfold Ex measure
  have hmp := measurePreserving_piEquivPiSubtypeProd C.μ p
  rw [← integral_prod_mul F G, ← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  rfl

/-! ## The many-coord marginal `condCE_forgetSet` and its `cond_Ex`

`condCE_forgetSet T X ω` integrates out the coins in `T`, holding the coins
outside `T` fixed at `ω`.  It is the `cond` of the `HasCondExp` instance
(`Filt = Finset ι`, `Sub T₁ T₂ = T₂ ⊆ T₁`, `Fixed = CFixed ∘ forgetSet`).  Its
`cond_Ex` (`Ex[cond T X] = Ex X`) is the genuine Fubini identity, discharged from
`BddMeas` (→ integrable); it is *out of the statement below only in the sense
that admissibility, not integrability, is the hypothesis*. -/

/-- The `T`-marginal: integrate out the coins in `T` (via the measure-preserving
split), holding the `Tᶜ`-coins fixed at `ω`. -/
noncomputable def condCE_forgetSet (T : Finset C.ι) (X : C.Ω → ℝ) (ω : C.Ω) : ℝ :=
  ∫ t, X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
            (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2))
        ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)

/-- Generic Fubini keystone (copied verbatim from the validated recipe): taking
the full `Ω`-expectation of the `T`-marginal recovers the expectation.  Stated for
a generic probability family `μ` and predicate `p`, side-stepping the in-context
subtype folding; `condCE_forgetSet_cond_Ex` applies it with `μ := C.μ`,
`p := (· ∈ T)`. -/
private theorem condEx_aux {ι : Type} [Fintype ι] {α : ι → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (p : ι → Prop) [DecidablePred p]
    (X : (∀ i, α i) → ℝ) (hX : Integrable X (Measure.pi μ)) :
    ∫ ω, (∫ t, X ((MeasurableEquiv.piEquivPiSubtypeProd α p).symm
              (t, ((MeasurableEquiv.piEquivPiSubtypeProd α p) ω).2))
            ∂(Measure.pi fun i : Subtype p => μ i)) ∂(Measure.pi μ)
      = ∫ ω, X ω ∂(Measure.pi μ) := by
  set E := MeasurableEquiv.piEquivPiSubtypeProd α p with hE
  have hmp := measurePreserving_piEquivPiSubtypeProd μ p
  have hemb : MeasurableEmbedding E := E.measurableEmbedding
  set νT := Measure.pi fun i : Subtype p => μ i with hνT
  set νR := Measure.pi fun i : {i // ¬ p i} => μ i with hνR
  set H := fun r => ∫ t, X (E.symm (t, r)) ∂νT with hH
  have hcomp : ((fun z => X (E.symm z)) ∘ ⇑E) = X := by
    funext ω; simp [MeasurableEquiv.symm_apply_apply]
  have hXE : Integrable (fun z => X (E.symm z)) (νT.prod νR) := by
    refine (hmp.integrable_comp_emb hemb).mp ?_
    rw [hcomp]; exact hX
  calc ∫ ω, (∫ t, X (E.symm (t, (E ω).2)) ∂νT) ∂(Measure.pi μ)
      = ∫ z, (∫ t, X (E.symm (t, z.2)) ∂νT) ∂(νT.prod νR) :=
          hmp.integral_comp hemb (fun z => ∫ t, X (E.symm (t, z.2)) ∂νT)
    _ = ∫ z, (fun _ => (1:ℝ)) z.1 * H z.2 ∂(νT.prod νR) := by simp [hH]
    _ = (∫ _t, (1:ℝ) ∂νT) * ∫ r, H r ∂νR := integral_prod_mul (fun _ => (1:ℝ)) H
    _ = ∫ r, H r ∂νR := by simp
    _ = ∫ z, X (E.symm z) ∂(νT.prod νR) := by rw [hH]; rw [← integral_prod_symm _ hXE]
    _ = ∫ ω, X ω ∂(Measure.pi μ) := by
          rw [← hmp.integral_comp hemb (fun z => X (E.symm z))]
          exact integral_congr_ae (Filter.Eventually.of_forall
            (fun ω => congrArg X (E.symm_apply_apply ω)))

/-- Generic nested-marginal (tower) identity: integrating out `q`-coins then
`p`-coins (with `q ⊆ p`) equals integrating out `p`-coins.  Reduces, via a
`piCongrLeft` reindexing of the inner block, to `condEx_aux` applied to the
`p`-block sub-measure.  Stated generically to side-step subtype folding;
`condCE_forgetSet_tower` applies it with `p := (· ∈ T₁)`, `q := (· ∈ T₂)`. -/
private theorem tower_aux {ι : Type} [Fintype ι] {α : ι → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (p q : ι → Prop) [DecidablePred p]
    [DecidablePred q] (hqp : ∀ i, q i → p i) (X : (∀ i, α i) → ℝ)
    (hmeas : Measurable X) (C₀ : ℝ) (hbd : ∀ z, |X z| ≤ C₀) (ω : ∀ i, α i) :
    ∫ s, (∫ u, X ((MeasurableEquiv.piEquivPiSubtypeProd α q).symm
            (u, ((MeasurableEquiv.piEquivPiSubtypeProd α q)
                  ((MeasurableEquiv.piEquivPiSubtypeProd α p).symm
                    (s, ((MeasurableEquiv.piEquivPiSubtypeProd α p) ω).2))).2))
          ∂(Measure.pi fun i : Subtype q => μ i))
        ∂(Measure.pi fun i : Subtype p => μ i)
      = ∫ s, X ((MeasurableEquiv.piEquivPiSubtypeProd α p).symm
                  (s, ((MeasurableEquiv.piEquivPiSubtypeProd α p) ω).2))
            ∂(Measure.pi fun i : Subtype p => μ i) := by
  classical
  set Ep := MeasurableEquiv.piEquivPiSubtypeProd α p with hEp
  set Fq := MeasurableEquiv.piEquivPiSubtypeProd α q with hFq
  set b₀ := (Ep ω).2 with hb₀
  set Y : ((j : Subtype p) → α j.val) → ℝ := fun a => X (Ep.symm (a, b₀)) with hY
  set p' : Subtype p → Prop := fun j => q j.val with hp'
  set E' := MeasurableEquiv.piEquivPiSubtypeProd (fun j : Subtype p => α j.val) p' with hE'
  have hYmeas : Measurable Y := by
    apply hmeas.comp
    exact Ep.symm.measurable.comp (by fun_prop)
  have hYint : Integrable Y (Measure.pi fun j : Subtype p => μ j.val) := by
    refine (integrable_const C₀).mono' hYmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => ?_))
    rw [Real.norm_eq_abs]; exact hbd _
  have hinner : ∀ s : (j : Subtype p) → α j.val,
      (∫ u, X (Fq.symm (u, (Fq (Ep.symm (s, b₀))).2))
          ∂(Measure.pi fun i : Subtype q => μ i))
        = ∫ t, Y (E'.symm (t, (E' s).2))
            ∂(Measure.pi fun i : Subtype p' => μ i.val) := by
    intro s
    let φ : Subtype q ≃ Subtype p' :=
      { toFun := fun i => ⟨⟨i.val, hqp i.val i.property⟩, i.property⟩
        invFun := fun j => ⟨j.val.val, j.property⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    set g : ((j : Subtype p') → α j.val.val) → ℝ :=
      fun z => Y (E'.symm (z, (E' s).2)) with hg
    have hmpφ := measurePreserving_piCongrLeft (fun j : Subtype p' => μ j.val.val) φ
    have hembφ : MeasurableEmbedding
        (MeasurableEquiv.piCongrLeft (fun j : Subtype p' => α j.val.val) φ) :=
      (MeasurableEquiv.piCongrLeft _ φ).measurableEmbedding
    have hreindex : (∫ u, g (fun j => u ⟨j.val.val, j.property⟩)
          ∂(Measure.pi fun i : Subtype q => μ i.val))
        = ∫ z, g z ∂(Measure.pi fun j : Subtype p' => μ j.val.val) := by
      rw [← hmpφ.integral_comp hembφ g]; congr 1
    rw [← hreindex]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun u => ?_)
    show X (Fq.symm (u, (Fq (Ep.symm (s, b₀))).2))
        = Y (E'.symm ((fun j => u ⟨j.val.val, j.property⟩), (E' s).2))
    rw [hY]
    congr 1
    funext i
    by_cases hp : p i
    · by_cases hq : q i
      · simp [Ep, Fq, E', MeasurableEquiv.piEquivPiSubtypeProd, hp, hq, p']
      · simp [Ep, Fq, E', MeasurableEquiv.piEquivPiSubtypeProd, hp, hq, p']
    · have hnq : ¬ q i := fun h => hp (hqp i h)
      simp [Ep, Fq, E', MeasurableEquiv.piEquivPiSubtypeProd, hp, hnq, p']
  rw [show (fun i : Subtype q => μ i) = (fun i : Subtype q => μ i.val) from rfl] at *
  calc ∫ s, (∫ u, X (Fq.symm (u, (Fq (Ep.symm (s, b₀))).2))
              ∂(Measure.pi fun i : Subtype q => μ i.val))
            ∂(Measure.pi fun i : Subtype p => μ i.val)
      = ∫ s, (∫ t, Y (E'.symm (t, (E' s).2))
              ∂(Measure.pi fun i : Subtype p' => μ i.val))
            ∂(Measure.pi fun i : Subtype p => μ i.val) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ s, Y s ∂(Measure.pi fun i : Subtype p => μ i.val) :=
          condEx_aux (fun j : Subtype p => μ j.val) p' Y hYint
    _ = ∫ s, X (Ep.symm (s, b₀)) ∂(Measure.pi fun i : Subtype p => μ i.val) := rfl

/-- **`condCE_forgetSet_cond_Ex`** (the keystone).  Taking the full `Ω`-expectation
of the `T`-marginal `condCE_forgetSet T X` recovers `Ex X` — the Fubini identity
underlying the `HasCondExp` `cond_Ex` field.  Discharged from `BddMeas` (→
integrable). -/
theorem condCE_forgetSet_cond_Ex (T : Finset C.ι) (X : C.Ω → ℝ) (hX : C.BddMeas X) :
    C.Ex (C.condCE_forgetSet T X) = C.Ex X := by
  show ∫ ω, (∫ t, X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
              (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2))
            ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)) ∂(Measure.pi C.μ)
      = ∫ ω, X ω ∂(Measure.pi C.μ)
  have hfin : (Finset.Subtype.fintype T) = Subtype.fintype (fun x => x ∈ T) :=
    Subsingleton.elim _ _
  rw [hfin]
  exact condEx_aux C.μ (· ∈ T) X hX.integrable

/-! ### The `HasCondExp` fields: `fixed_rule`, `tower`, `cond_Ex` -/

/-- The `T`-merge `E.symm (t, (E ω).2)` used inside `condCE_forgetSet` keeps the
coins **outside** `T` at their `ω` values (only the `T`-coins come from `t`). -/
theorem forgetSet_merge_eq_outside (T : Finset C.ι)
    (t : (i : {i // i ∈ T}) → C.Coin i) (ω : C.Ω) {i : C.ι} (hi : i ∉ T) :
    ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)) i = ω i := by
  simp [MeasurableEquiv.piEquivPiSubtypeProd, hi]

/-- If `X` is fixed by `forgetSet T` (reads only the coins outside `T`), then the
`T`-merge does not change its value: `X (merge t ω) = X ω`.  The pointwise engine
behind `fixed_rule`. -/
theorem CFixed_merge (T : Finset C.ι) (X : C.Ω → ℝ)
    (hX : C.CFixed (C.forgetSet T) X)
    (t : (i : {i // i ∈ T}) → C.Coin i) (ω : C.Ω) :
    X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)) = X ω := by
  apply hX
  rw [forgetSet_eq_iff]
  intro i hi
  exact C.forgetSet_merge_eq_outside T t ω hi

/-- **Fixed-variable rule** (unconditional).  If `X` is fixed by `forgetSet T`,
pulling it out of the `T`-marginal is `integral_const_mul`. -/
theorem condCE_forgetSet_fixed_rule (T : Finset C.ι) (X Y : C.Ω → ℝ)
    (hX : C.CFixed (C.forgetSet T) X) :
    C.condCE_forgetSet T (fun ω => X ω * Y ω)
      = fun ω => X ω * C.condCE_forgetSet T Y ω := by
  funext ω
  show ∫ t, X _ * Y _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
      = X ω * ∫ t, Y _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [C.CFixed_merge T X hX t ω]

/-- **Tower rule** (guarded by `BddMeas`).  For `T₂ ⊆ T₁`, conditioning on the
coarser filtration after the finer one collapses: integrating out `T₂` then `T₁`
equals integrating out `T₁`.  The genuine nested-marginal Fubini identity,
discharged from `tower_aux`. -/
theorem condCE_forgetSet_tower {T₁ T₂ : Finset C.ι} (hsub : T₂ ⊆ T₁)
    (X : C.Ω → ℝ) (hX : C.BddMeas X) :
    C.condCE_forgetSet T₁ (C.condCE_forgetSet T₂ X) = C.condCE_forgetSet T₁ X := by
  obtain ⟨hXm, C₀, hbd⟩ := hX
  funext ω
  have hfin1 : (Finset.Subtype.fintype T₁) = Subtype.fintype (fun x => x ∈ T₁) :=
    Subsingleton.elim _ _
  have hfin2 : (Finset.Subtype.fintype T₂) = Subtype.fintype (fun x => x ∈ T₂) :=
    Subsingleton.elim _ _
  show ∫ t, (∫ u, X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₂)).symm
            (u, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₂))
                  ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₁)).symm
                    (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₁)) ω).2))).2))
          ∂(Measure.pi fun i : {i // i ∈ T₂} => C.μ i))
        ∂(Measure.pi fun i : {i // i ∈ T₁} => C.μ i)
      = ∫ t, X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₁)).symm
                  (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T₁)) ω).2))
            ∂(Measure.pi fun i : {i // i ∈ T₁} => C.μ i)
  rw [hfin1, hfin2]
  exact tower_aux C.μ (· ∈ T₁) (· ∈ T₂) (fun _ h => hsub h) X hXm C₀ hbd ω

/-- **The `HasCondExp` instance carried by a `MixedCoinSpace`.**  The filtration
type is `Finset ι` (the forgotten-coin set), `Sub T₁ T₂ := T₂ ⊆ T₁`, `Fixed` is
`CFixed ∘ forgetSet`, and `cond` is the many-coin marginal `condCE_forgetSet`.
The three facts are `condCE_forgetSet_fixed_rule` (unconditional), the nested-Fubini
`condCE_forgetSet_tower`, and the keystone `condCE_forgetSet_cond_Ex` (both
discharged from `BddMeas` via `IsAdm`). -/
noncomputable def toHasCondExp : ProbSpace.HasCondExp C.toProbSpace where
  Filt := Finset C.ι
  Sub := fun T₁ T₂ => T₂ ⊆ T₁
  Fixed := fun T X => C.CFixed (C.forgetSet T) X
  cond := fun T X => C.condCE_forgetSet T X
  fixed_rule := fun T X Y hfix => C.condCE_forgetSet_fixed_rule T X Y hfix
  tower := fun _ _ X _inst hsub => C.condCE_forgetSet_tower hsub X _inst.out
  cond_Ex := fun T X _inst => C.condCE_forgetSet_cond_Ex T X _inst.out

/-! ## B.3 — the many-coord marginal surface (mirrors `CoinSpace` in `ProductSpace`)

These carry the same names the finite coin model consumes: conditioning a
few-coin function on the many-coin filtration reduces to the few-coin marginal
(via the tower rule), and forgetting exactly a function's coins returns its
expectation.  All discharged from `BddMeas`; the single-coin bridge
`condCE_forget_eq_forgetSet_singleton` connects the pointwise coordinate marginal
`condCE_forget` to the `Finset`-indexed `condCE_forgetSet`. -/

/-- The `T`-merge keeps `t` on the `T`-coins (companion to `forgetSet_merge_eq_outside`). -/
theorem forgetSet_merge_mem (T : Finset C.ι)
    (t : (i : {i // i ∈ T}) → C.Coin i) (ω : C.Ω) {k : C.ι} (hk : k ∈ T) :
    ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)) k = t ⟨k, hk⟩ := by
  simp [MeasurableEquiv.piEquivPiSubtypeProd, hk]

/-- **`condCE_of_forgetSet_CFixed`** (many-coord).  Conditioning a
`forgetSet T`-fixed function returns it (the mass-one collapse; no positivity
needed). -/
theorem condCE_of_forgetSet_CFixed (T : Finset C.ι) (X : C.Ω → ℝ)
    (hX : C.CFixed (C.forgetSet T) X) : C.condCE_forgetSet T X = X := by
  funext ω
  unfold condCE_forgetSet
  rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun t => C.CFixed_merge T X hX t ω)), integral_const, MeasureTheory.measureReal_def, measure_univ]
  simp

/-- **Single-coin bridge.**  The pointwise coordinate marginal `condCE_forget j`
equals the `Finset`-indexed marginal `condCE_forgetSet {j}` (a `piUnique`
reindexing of the singleton block onto the coin `j`). -/
theorem condCE_forget_eq_forgetSet_singleton (j : C.ι) (X : C.Ω → ℝ) :
    C.condCE_forget j X = C.condCE_forgetSet {j} X := by
  funext ω
  unfold condCE_forget condCE_forgetSet
  set ν := fun i : {i // i ∈ ({j} : Finset C.ι)} => C.μ i.val with hν
  have hmp := measurePreserving_piUnique ν
  have hemb : MeasurableEmbedding
      (MeasurableEquiv.piUnique fun i : {i // i ∈ ({j} : Finset C.ι)} => C.Coin i.val) :=
    (MeasurableEquiv.piUnique _).measurableEmbedding
  have harg : ∀ t : (i : {i // i ∈ ({j} : Finset C.ι)}) → C.Coin i.val,
      ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ ({j} : Finset C.ι))).symm
          (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ ({j} : Finset C.ι))) ω).2))
        = Function.update ω j (t default) := by
    intro t; funext i
    by_cases hij : i = j
    · subst hij
      rw [C.forgetSet_merge_mem {i} t ω (Finset.mem_singleton_self i), Function.update_self]
      refine eq_of_heq ?_
      congr 1
    · rw [C.forgetSet_merge_eq_outside {j} t ω (by simpa using hij), Function.update_of_ne hij]
  calc ∫ c, X (Function.update ω j c) ∂(C.μ j)
      = ∫ c, X (Function.update ω j c) ∂(ν default) := rfl
    _ = ∫ t, X (Function.update ω j ((MeasurableEquiv.piUnique
              fun i : {i // i ∈ ({j} : Finset C.ι)} => C.Coin i.val) t)) ∂(Measure.pi ν) :=
          (hmp.integral_comp hemb (fun c => X (Function.update ω j c))).symm
    _ = ∫ t, X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ ({j} : Finset C.ι))).symm
              (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ ({j} : Finset C.ι))) ω).2))
            ∂(Measure.pi ν) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun t => congrArg X (harg t).symm)

/-- **`condCE_forgetSet_of_forget`** (mirrors `CoinSpace`).  If `E[X | forget j] = g`
(a `j`-marginal, `j ∈ T`) and `g` is `forgetSet T`-fixed, then `E[X | forgetSet T] = g`
— the extra forgotten coins wash out.  Proved by the tower rule. -/
theorem condCE_forgetSet_of_forget {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T)
    (X g : C.Ω → ℝ) (hX : C.BddMeas X)
    (hf : C.condCE_forget j X = g) (hg : C.CFixed (C.forgetSet T) g) :
    C.condCE_forgetSet T X = g := by
  have hf' : C.condCE_forgetSet {j} X = g := by
    rw [← C.condCE_forget_eq_forgetSet_singleton]; exact hf
  have hsub : ({j} : Finset C.ι) ⊆ T := Finset.singleton_subset_iff.mpr hjT
  calc C.condCE_forgetSet T X
      = C.condCE_forgetSet T (C.condCE_forgetSet {j} X) :=
        (C.condCE_forgetSet_tower hsub X hX).symm
    _ = C.condCE_forgetSet T g := by rw [hf']
    _ = g := C.condCE_of_forgetSet_CFixed T g hg

/-- **`condCE_forgetSet_single`** (mirrors `CoinSpace`).  If `X` reads only coin
`j ∈ T`, conditioning on `forgetSet T` is the single-coin marginal `condCE_forget j`. -/
theorem condCE_forgetSet_single {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T)
    (X : C.Ω → ℝ) (hX : C.BddMeas X)
    (hXdep : ∀ ω ω', ω j = ω' j → X ω = X ω') :
    C.condCE_forgetSet T X = C.condCE_forget j X := by
  refine C.condCE_forgetSet_of_forget hjT X (C.condCE_forget j X) hX rfl ?_
  refine C.CFixed_forgetSet T _ (fun a b _ => ?_)
  unfold condCE_forget
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (fun c => hXdep _ _ (by rw [Function.update_self, Function.update_self]))

/-- **`condCE_forgetSet_pair`** (mirrors `CoinSpace`).  If `E[X | forgetSet {j₁,j₂}] = g`
(both `j₁, j₂ ∈ T`) and `g` is `forgetSet T`-fixed, then `E[X | forgetSet T] = g`.
The two-coin analogue of `condCE_forgetSet_of_forget`, by the tower rule. -/
theorem condCE_forgetSet_pair {T : Finset C.ι} {j₁ j₂ : C.ι}
    (hj1 : j₁ ∈ T) (hj2 : j₂ ∈ T) (X g : C.Ω → ℝ) (hX : C.BddMeas X)
    (hf : C.condCE_forgetSet {j₁, j₂} X = g) (hg : C.CFixed (C.forgetSet T) g) :
    C.condCE_forgetSet T X = g := by
  have hsub : ({j₁, j₂} : Finset C.ι) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h <;> subst h <;> assumption
  calc C.condCE_forgetSet T X
      = C.condCE_forgetSet T (C.condCE_forgetSet {j₁, j₂} X) :=
        (C.condCE_forgetSet_tower hsub X hX).symm
    _ = C.condCE_forgetSet T g := by rw [hf]
    _ = g := C.condCE_of_forgetSet_CFixed T g hg

/-- **`condCE_forgetSet_full`** (mirrors `CoinSpace/CoordIndep`).  Forgetting
*exactly* the coins `U` that `X` reads returns the constant `Ex X` — the
independence-data identity.  Proved from the pointwise constancy of the `U`-marginal
plus the keystone `condCE_forgetSet_cond_Ex`. -/
theorem condCE_forgetSet_full (U : Finset C.ι) (X : C.Ω → ℝ) (hX : C.BddMeas X)
    (hdep : ∀ ω ω', (∀ k ∈ U, ω k = ω' k) → X ω = X ω') :
    C.condCE_forgetSet U X = fun _ => C.Ex X := by
  have hconst : ∀ ω ω', C.condCE_forgetSet U X ω = C.condCE_forgetSet U X ω' := by
    intro ω ω'
    unfold condCE_forgetSet
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun t => ?_)
    apply hdep
    intro k hk
    rw [C.forgetSet_merge_mem U t ω hk, C.forgetSet_merge_mem U t ω' hk]
  have hc : C.condCE_forgetSet U X = fun _ => C.Ex (C.condCE_forgetSet U X) := by
    funext ω
    have hEq : C.condCE_forgetSet U X = fun _ => C.condCE_forgetSet U X ω := by
      funext ω'; exact hconst ω' ω
    rw [hEq, C.Ex_const]
  rw [hc, C.condCE_forgetSet_cond_Ex U X hX]

/-- **`condCE_forgetPair`** (mirrors `CoinSpace`).  The two-coin marginal as an
iterated single-coin marginal: `E[X | forget j₁]∘E[·| forget j₂]` is the joint
double integral over the two coins (Fubini/`condCE_forget` unfolding; holds for
any `j₁, j₂`). -/
theorem condCE_forgetPair (j₁ j₂ : C.ι) (X : C.Ω → ℝ) (ω : C.Ω) :
    C.condCE_forget j₁ (C.condCE_forget j₂ X) ω
      = ∫ c₁, ∫ c₂, X (Function.update (Function.update ω j₁ c₁) j₂ c₂)
          ∂(C.μ j₂) ∂(C.μ j₁) := rfl

/-- **Fixed-variable rule at the single-coin marginal** (companion to
`condCE_forgetSet_fixed_rule`, via the single-coin bridge).  Pulls a
`forget j`-fixed factor out of the coin-`j` marginal. -/
theorem condCE_forget_fixed_rule (j : C.ι) (X Y : C.Ω → ℝ)
    (hX : C.CFixed (C.forget j) X) :
    C.condCE_forget j (fun ω => X ω * Y ω) = fun ω => X ω * C.condCE_forget j Y ω := by
  simp only [condCE_forget_eq_forgetSet_singleton]
  rw [forget_eq_forgetSet_singleton] at hX
  exact C.condCE_forgetSet_fixed_rule {j} X Y hX

/-- **Tower across a single kept coin**: conditioning `E[·| forget j]` under
`E[·| forgetSet T]` (with `j ∈ T`) collapses to `E[·| forgetSet T]`.  The
`forget`-level shadow of `condCE_forgetSet_tower`, via the single-coin bridge. -/
theorem condCE_forgetSet_forget_tower {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T)
    (X : C.Ω → ℝ) (hX : C.BddMeas X) :
    C.condCE_forgetSet T (C.condCE_forget j X) = C.condCE_forgetSet T X := by
  rw [condCE_forget_eq_forgetSet_singleton]
  exact C.condCE_forgetSet_tower (Finset.singleton_subset_iff.mpr hjT) X hX

/-- A `Finset` product of `π`-fixed functions is `π`-fixed. -/
theorem CFixed_prod {ι' : Type} (π : C.Ω → C.Ω) (s : Finset ι') (f : ι' → C.Ω → ℝ)
    (hf : ∀ i ∈ s, C.CFixed π (f i)) :
    C.CFixed π (fun ω => ∏ i ∈ s, f i ω) := by
  intro a b hab
  exact Finset.prod_congr rfl (fun i hi => hf i hi a b hab)

/-- Bounded-measurability is closed under finite products. -/
theorem BddMeas_prod {ι' : Type} (s : Finset ι') (f : ι' → C.Ω → ℝ)
    (hf : ∀ i ∈ s, C.BddMeas (f i)) : C.BddMeas (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using C.BddMeas_const 1
  | @insert a s ha ih =>
      have hrest := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hcomb := C.BddMeas_mul (hf a (Finset.mem_insert_self a s)) hrest
      simpa [Finset.prod_insert ha] using hcomb

/-- **`condCE_pair_data`** (mirrors `ReduceModel`).  For distinct coins
`j₁, j₂ ∈ T`, two keep-decisions with `forgetSet T`-fixed thresholds (`keep₂`
not reading coin `j₁`) factor under the `forgetSet T`-conditional into the two
thresholds.  The two-factor independence identity, via tower + fixed-rule. -/
theorem condCE_pair_data {T : Finset C.ι} {j₁ j₂ : C.ι} (hj1 : j₁ ∈ T) (hj2 : j₂ ∈ T)
    (keep₁ keep₂ threshold₁ threshold₂ : C.Ω → ℝ)
    (hk1 : C.BddMeas keep₁) (hk2 : C.BddMeas keep₂)
    (ht1fixed : C.CFixed (C.forgetSet T) threshold₁)
    (ht2fixed : C.CFixed (C.forgetSet T) threshold₂)
    (hk2fixedj1 : C.CFixed (C.forget j₁) keep₂)
    (hk1forget : C.condCE_forget j₁ keep₁ = threshold₁)
    (hk2forget : C.condCE_forget j₂ keep₂ = threshold₂) :
    C.condCE_forgetSet T (fun ω => keep₁ ω * keep₂ ω)
      = fun ω => threshold₁ ω * threshold₂ ω := by
  have hk12 : C.BddMeas (fun ω => keep₁ ω * keep₂ ω) := C.BddMeas_mul hk1 hk2
  have step1 : C.condCE_forget j₁ (fun ω => keep₁ ω * keep₂ ω)
      = fun ω => threshold₁ ω * keep₂ ω := by
    calc C.condCE_forget j₁ (fun ω => keep₁ ω * keep₂ ω)
        = C.condCE_forget j₁ (fun ω => keep₂ ω * keep₁ ω) :=
          congrArg (C.condCE_forget j₁) (by funext ω; ring)
      _ = fun ω => keep₂ ω * C.condCE_forget j₁ keep₁ ω :=
          C.condCE_forget_fixed_rule j₁ keep₂ keep₁ hk2fixedj1
      _ = fun ω => keep₂ ω * threshold₁ ω := by rw [hk1forget]
      _ = fun ω => threshold₁ ω * keep₂ ω := by funext ω; ring
  calc C.condCE_forgetSet T (fun ω => keep₁ ω * keep₂ ω)
      = C.condCE_forgetSet T (C.condCE_forget j₁ (fun ω => keep₁ ω * keep₂ ω)) :=
        (C.condCE_forgetSet_forget_tower hj1 _ hk12).symm
    _ = C.condCE_forgetSet T (fun ω => threshold₁ ω * keep₂ ω) := by rw [step1]
    _ = fun ω => threshold₁ ω * C.condCE_forgetSet T keep₂ ω :=
        C.condCE_forgetSet_fixed_rule T threshold₁ keep₂ ht1fixed
    _ = fun ω => threshold₁ ω * threshold₂ ω := by
        rw [C.condCE_forgetSet_of_forget hj2 keep₂ threshold₂ hk2 hk2forget ht2fixed]

/-- **`condCE_prod_data`** (mirrors `CondExpProdData`).  The n-ary tower-rule
product factorization: each keep-decision `keep i` has keep-coin `j i ∈ T` and
averages to a `forgetSet T`-fixed threshold; distinct keep-decisions are
independent (`hindep`).  The `forgetSet T`-conditional of their product factors
into the product of thresholds — the shared threshold is handled coin-by-coin by
the tower step, so no global disjointness is needed. -/
theorem condCE_prod_data {ι' : Type} [DecidableEq ι'] {T : Finset C.ι} (s : Finset ι')
    (j : ι' → C.ι) (keep threshold : ι' → C.Ω → ℝ)
    (hkeep : ∀ i ∈ s, C.BddMeas (keep i))
    (hjT : ∀ i ∈ s, j i ∈ T)
    (htfixed : ∀ i ∈ s, C.CFixed (C.forgetSet T) (threshold i))
    (hindep : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → C.CFixed (C.forget (j i')) (keep i))
    (hforget : ∀ i ∈ s, C.condCE_forget (j i) (keep i) = threshold i) :
    C.condCE_forgetSet T (fun ω => ∏ i ∈ s, keep i ω)
      = fun ω => ∏ i ∈ s, threshold i ω := by
  induction s using Finset.induction with
  | empty =>
      funext ω
      simp only [Finset.prod_empty]
      exact congrFun (C.condCE_of_forgetSet_CFixed T (fun _ => 1)
        (fun a b _ => rfl)) ω
  | @insert i₀ s' hi₀ ih =>
      have hkeep' : ∀ i ∈ s', C.BddMeas (keep i) :=
        fun i hi => hkeep i (Finset.mem_insert_of_mem hi)
      have hjT' : ∀ i ∈ s', j i ∈ T := fun i hi => hjT i (Finset.mem_insert_of_mem hi)
      have htfixed' : ∀ i ∈ s', C.CFixed (C.forgetSet T) (threshold i) :=
        fun i hi => htfixed i (Finset.mem_insert_of_mem hi)
      have hindep' : ∀ i ∈ s', ∀ i' ∈ s', i ≠ i' →
          C.CFixed (C.forget (j i')) (keep i) :=
        fun i hi i' hi' => hindep i (Finset.mem_insert_of_mem hi) i'
          (Finset.mem_insert_of_mem hi')
      have hforget' : ∀ i ∈ s', C.condCE_forget (j i) (keep i) = threshold i :=
        fun i hi => hforget i (Finset.mem_insert_of_mem hi)
      have IH := ih hkeep' hjT' htfixed' hindep' hforget'
      set Pk := fun ω => ∏ i ∈ s', keep i ω with hPk
      set Pt := fun ω => ∏ i ∈ s', threshold i ω with hPt
      have hPkbdd : C.BddMeas Pk := C.BddMeas_prod s' keep hkeep'
      have hk0bdd : C.BddMeas (keep i₀) := hkeep i₀ (Finset.mem_insert_self _ _)
      have hcofix : C.CFixed (C.forget (j i₀)) Pk := by
        apply C.CFixed_prod (C.forget (j i₀)) s' keep
        intro i hi
        exact hindep i (Finset.mem_insert_of_mem hi) i₀ (Finset.mem_insert_self _ _)
          (fun h => hi₀ (h ▸ hi))
      have hk0forget : C.condCE_forget (j i₀) (keep i₀) = threshold i₀ :=
        hforget i₀ (Finset.mem_insert_self _ _)
      have ht0fixed : C.CFixed (C.forgetSet T) (threshold i₀) :=
        htfixed i₀ (Finset.mem_insert_self _ _)
      have step1 : C.condCE_forget (j i₀) (fun ω => keep i₀ ω * Pk ω)
          = fun ω => threshold i₀ ω * Pk ω := by
        calc C.condCE_forget (j i₀) (fun ω => keep i₀ ω * Pk ω)
            = C.condCE_forget (j i₀) (fun ω => Pk ω * keep i₀ ω) :=
              congrArg (C.condCE_forget (j i₀)) (by funext ω; ring)
          _ = fun ω => Pk ω * C.condCE_forget (j i₀) (keep i₀) ω :=
              C.condCE_forget_fixed_rule (j i₀) Pk (keep i₀) hcofix
          _ = fun ω => Pk ω * threshold i₀ ω := by rw [hk0forget]
          _ = fun ω => threshold i₀ ω * Pk ω := by funext ω; ring
      have hk0Pk : C.BddMeas (fun ω => keep i₀ ω * Pk ω) := C.BddMeas_mul hk0bdd hPkbdd
      have hmain : C.condCE_forgetSet T (fun ω => keep i₀ ω * Pk ω)
          = fun ω => threshold i₀ ω * Pt ω := by
        calc C.condCE_forgetSet T (fun ω => keep i₀ ω * Pk ω)
            = C.condCE_forgetSet T
                (C.condCE_forget (j i₀) (fun ω => keep i₀ ω * Pk ω)) :=
              (C.condCE_forgetSet_forget_tower (hjT i₀ (Finset.mem_insert_self _ _)) _ hk0Pk).symm
          _ = C.condCE_forgetSet T (fun ω => threshold i₀ ω * Pk ω) := by rw [step1]
          _ = fun ω => threshold i₀ ω * C.condCE_forgetSet T Pk ω :=
              C.condCE_forgetSet_fixed_rule T (threshold i₀) Pk ht0fixed
          _ = fun ω => threshold i₀ ω * Pt ω := by
              rw [show C.condCE_forgetSet T Pk = Pt from IH]
      calc C.condCE_forgetSet T (fun ω => ∏ i ∈ insert i₀ s', keep i ω)
          = C.condCE_forgetSet T (fun ω => keep i₀ ω * Pk ω) := by
            refine congrArg (C.condCE_forgetSet T) ?_
            funext ω; rw [Finset.prod_insert hi₀]
        _ = fun ω => threshold i₀ ω * Pt ω := hmain
        _ = fun ω => ∏ i ∈ insert i₀ s', threshold i ω := by
            funext ω; rw [Finset.prod_insert hi₀]

end MixedCoinSpace

/-! ## The continuous keep-coin: threshold marginal reduces to `Eu_threshold`

For a `[0,1]`-uniform keep-coin (`Coin j = ℝ`, `μ j = unitMeasure`), the
per-coordinate integral `∫ · ∂(μ j)` is the prototype's `Eu`, so the reduce
step's step-function marginal `∫ (a·𝟙_{u<τ}+b) = a·τ+b` holds for ANY real
`τ ∈ [0,1]` — the continuous replacement for the finite `uniform_cdf_eq`
quantization.  These are stated over `unitMeasure` directly so the Wave-1 coin
model can drop them onto any keep-coordinate. -/

namespace MixedCoinSpace

open ContCoinProto

/-- `∫ f ∂unitMeasure = ∫₀¹ f` (bridge from the `Measure.pi` coordinate integral
to the prototype's `Eu`).  `{0}` is `volume`-null, so `Icc = Ioc` under the
integral. -/
theorem integral_unitMeasure_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂unitMeasure = ∫ x in (0:ℝ)..1, f x := by
  unfold unitMeasure
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- The keep-coin's threshold marginal value, over `unitMeasure`, equals
`Eu_threshold`: `∫ (a·𝟙_{u<τ}+b) ∂unitMeasure = a·τ+b` for real `τ ∈ [0,1]`. -/
theorem integral_unitMeasure_threshold (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (a b : ℝ) :
    ∫ u, (a * (if u < τ then (1:ℝ) else 0) + b) ∂unitMeasure = a * τ + b := by
  rw [integral_unitMeasure_eq]
  exact Eu_threshold τ h0 h1 a b

/-- **`condCE_forget_keepThreshold`** — the continuous keep-decision marginal
identity: the *unconditional* (no-quantization) analogue of the finite
grid keep-coin marginal.  It removes the quantization
(`IsQuant`/`∃ m ≤ K`) restriction on the threshold.

For a keep-coordinate `j` whose coin reads onto the real unit-interval coin via a
measurable equivalence `e : C.Coin j ≃ᵐ ℝ` that pushes `C.μ j` forward to
`unitMeasure = volume.restrict (Icc 0 1)`, and a threshold `τ` that does *not*
read coin `j` (`C.CFixed (C.forget j) τ`) with `0 ≤ τ ω ≤ 1` everywhere,
conditioning the keep-indicator `𝟙_{e (coin j) < τ}` on forgetting coin `j`
returns exactly the threshold `τ` — for ANY real `τ ∈ [0,1]`, with no
quantization hypothesis whatsoever.

Specializing `e := MeasurableEquiv.refl ℝ` (a genuine real unit keep-coin, where
`C.Coin j = ℝ` and `C.μ j = unitMeasure`) recovers the literal statement
`C.condCE_forget j (fun ω => if (ω j : ℝ) < τ ω then 1 else 0) = τ`. -/
theorem condCE_forget_keepThreshold (C : MixedCoinSpace) (j : C.ι)
    (e : C.Coin j ≃ᵐ ℝ) (hμ : (C.μ j).map e = unitMeasure)
    (τ : C.Ω → ℝ) (hτ : C.CFixed (C.forget j) τ)
    (h0 : ∀ ω, 0 ≤ τ ω) (h1 : ∀ ω, τ ω ≤ 1) :
    C.condCE_forget j (fun ω => if e (ω j) < τ ω then (1:ℝ) else 0) = τ := by
  funext ω
  unfold condCE_forget
  -- After forgetting coin `j`: `(update ω j c) j = c` and `τ (update ω j c) = τ ω`
  -- (the latter by `CFixed` + `forget_update`), so the integrand collapses to
  -- the pure indicator `𝟙_{e c < τ ω}`.
  have hstep : ∀ c : C.Coin j,
      (if e ((Function.update ω j c) j) < τ (Function.update ω j c) then (1:ℝ) else 0)
        = (if e c < τ ω then (1:ℝ) else 0) := by
    intro c
    rw [Function.update_self,
      hτ (Function.update ω j c) ω (C.forget_update j ω c)]
  -- The reduced indicator on `ℝ` is measurable (indicator of `Iio (τ ω)`).
  have hg : Measurable (fun u : ℝ => if u < τ ω then (1:ℝ) else 0) := by
    have hset : MeasurableSet {u : ℝ | u < τ ω} := measurableSet_Iio
    have hrw : (fun u : ℝ => if u < τ ω then (1:ℝ) else 0)
        = Set.indicator {u : ℝ | u < τ ω} (fun _ => 1) := by
      funext u; simp [Set.indicator_apply]
    rw [hrw]; exact measurable_const.indicator hset
  calc ∫ c, (if e ((Function.update ω j c) j) < τ (Function.update ω j c) then (1:ℝ) else 0)
          ∂(C.μ j)
      = ∫ c, (if e c < τ ω then (1:ℝ) else 0) ∂(C.μ j) :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = ∫ u, (if u < τ ω then (1:ℝ) else 0) ∂((C.μ j).map e) :=
        (integral_map e.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ u, (if u < τ ω then (1:ℝ) else 0) ∂unitMeasure := by rw [hμ]
    _ = τ ω := by
        have hthr := integral_unitMeasure_threshold (τ ω) (h0 ω) (h1 ω) 1 0
        simpa using hthr

/-- **`condCE_reduceStep_data`** (the `MixedCoinSpace` analogue of the finite
`ReduceModel.condCE_reduceStep_data`).  One faithful "reduce step" for the
continuous coin model: an `𝓕̂`-measurable indicator `indHat` times a
data-dependent keep-decision `keep`, conditioned on forgetting a set `T` that
contains the keep-coin `j`, collapses to `indHat · threshold`.  The keep-decision
depends on both its coin `j` and the (`𝓕̂`-measurable) `threshold`; the only
probabilistic input is the single-coin bridge `E[keep | forget j] = threshold`.

Proof: pull the `forgetSet T`-fixed factor `indHat` out of the `forgetSet T`
conditional (`condCE_forgetSet_fixed_rule`), then turn the inner
`condCE_forgetSet T keep` into `threshold` via `condCE_forgetSet_of_forget`
(the extra forgotten coins in `T ∖ {j}` wash out by the tower rule). -/
theorem condCE_reduceStep_data (C : MixedCoinSpace) {T : Finset C.ι} {j : C.ι}
    (hjT : j ∈ T) (indHat keep threshold : C.Ω → ℝ)
    (hHatFixed : C.CFixed (C.forgetSet T) indHat)
    (hThreshFixed : C.CFixed (C.forgetSet T) threshold)
    (hkeepBdd : C.BddMeas keep)
    (hKeepForget : C.condCE_forget j keep = threshold) :
    C.condCE_forgetSet T (fun ω => indHat ω * keep ω)
      = fun ω => indHat ω * threshold ω := by
  have hfr := C.condCE_forgetSet_fixed_rule T indHat keep hHatFixed
  have havg := C.condCE_forgetSet_of_forget hjT keep threshold hkeepBdd hKeepForget hThreshFixed
  rw [hfr, havg]

end MixedCoinSpace
end Arlib.Probability
