/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Linearity of the `MixedCoinSpace` conditional expectation `condCE_forgetSet`

`condCE_forgetSet T X ω = ∫ t, X (merge t ω) ∂(Measure.pi (T-coins))` is the
`T`-marginal conditional expectation of the continuous coin model.  Being an
integral, it is **linear** — subtractive, additive, scalar-homogeneous, and
finite-sum-additive — under integrability, which `BddMeas` supplies (bounded +
measurable over a probability measure).  These are the mixed replacements for the
finite `FinProb.condCE_sub`/`condCE_add`/`condCE_smul`/`condCE_sum`.

`M.ce.cond (M.Fhat j) = M.C.condCE_forgetSet (M.Fhatfor j)` definitionally (the
`HasCondExp` instance sets `cond := fun T X => condCE_forgetSet T X`), so these
lemmas discharge the `hsub`/`hadd` obligations on `M.ce.cond` directly.
-/
import Arlib.Probability.MixedCoinSpace

namespace Arlib.Probability

namespace MixedCoinSpace

open MeasureTheory

variable {C : MixedCoinSpace}

/-- The `T`-merge map `t ↦ (piEquiv).symm (t, (piEquiv ω).2)` is measurable. -/
theorem measurable_merge (T : Finset C.ι) (ω : C.Ω) :
    Measurable (fun t : (i : {i // i ∈ T}) → C.Coin i =>
      (MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm.measurable.comp
    (measurable_id.prodMk measurable_const)

/-- **Slice integrability.**  `t ↦ X (merge t ω)` is integrable over the `T`-marginal
probability measure whenever `X` is bounded + measurable (`BddMeas`). -/
theorem slice_integrable (T : Finset C.ι) {X : C.Ω → ℝ} (hX : C.BddMeas X) (ω : C.Ω) :
    Integrable (fun t : (i : {i // i ∈ T}) → C.Coin i =>
        X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
            (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)))
      (Measure.pi fun i : {i // i ∈ T} => C.μ i) := by
  obtain ⟨hmeas, M, hbd⟩ := hX
  have hm : Measurable (fun t : (i : {i // i ∈ T}) → C.Coin i =>
      X ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2))) :=
    hmeas.comp (measurable_merge T ω)
  exact Integrable.mono' (integrable_const M) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hbd _))

/-- **Additivity** of `condCE_forgetSet` (`BddMeas`-guarded). -/
theorem condCE_forgetSet_add (T : Finset C.ι) (X Y : C.Ω → ℝ)
    (hX : C.BddMeas X) (hY : C.BddMeas Y) :
    C.condCE_forgetSet T (fun ω => X ω + Y ω)
      = fun ω => C.condCE_forgetSet T X ω + C.condCE_forgetSet T Y ω := by
  funext ω
  show ∫ t, (X _ + Y _) ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
      = (∫ t, X _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i))
        + ∫ t, Y _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
  exact integral_add (slice_integrable T hX ω) (slice_integrable T hY ω)

/-- **Subtractivity** of `condCE_forgetSet` (`BddMeas`-guarded). -/
theorem condCE_forgetSet_sub (T : Finset C.ι) (X Y : C.Ω → ℝ)
    (hX : C.BddMeas X) (hY : C.BddMeas Y) :
    C.condCE_forgetSet T (fun ω => X ω - Y ω)
      = fun ω => C.condCE_forgetSet T X ω - C.condCE_forgetSet T Y ω := by
  funext ω
  show ∫ t, (X _ - Y _) ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
      = (∫ t, X _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i))
        - ∫ t, Y _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
  exact integral_sub (slice_integrable T hX ω) (slice_integrable T hY ω)

/-- **`BddMeas_condCE_forgetSet`** — the `T`-marginal of a bounded-measurable
function is bounded-measurable.  Boundedness is the slice bound; measurability is
the parametric-integral measurability `Measurable.integral_prod_right'` through the
measure-preserving split `Ω ≅ (∏_T) × (∏_{Tᶜ})`. -/
theorem BddMeas_condCE_forgetSet (T : Finset C.ι) {V : C.Ω → ℝ} (hV : C.BddMeas V) :
    C.BddMeas (C.condCE_forgetSet T V) := by
  have hVbdd := hV
  obtain ⟨hmeas, C₀, hbd⟩ := hV
  set E := MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T) with hE
  set νT := Measure.pi fun i : {i // i ∈ T} => C.μ i with hνT
  -- `f (r, t) = V (E.symm (t, r))` is measurable on the swapped product.
  have hG : Measurable
      (fun rt : ((i : {i // ¬ (i ∈ T)}) → C.Coin i) × ((i : {i // i ∈ T}) → C.Coin i) =>
        V (E.symm (rt.2, rt.1))) :=
    hmeas.comp (E.symm.measurable.comp (measurable_snd.prodMk measurable_fst))
  -- integrating out the first (`T`-block) coordinate is measurable in the rest.
  have hH : Measurable (fun r : (i : {i // ¬ (i ∈ T)}) → C.Coin i =>
      ∫ t, V (E.symm (t, r)) ∂νT) :=
    (hG.stronglyMeasurable.integral_prod_right').measurable
  refine ⟨?_, C₀, ?_⟩
  · exact hH.comp (measurable_snd.comp E.measurable)
  · intro ω
    show |∫ t, V (E.symm (t, (E ω).2)) ∂νT| ≤ C₀
    have hint : Integrable (fun t => V (E.symm (t, (E ω).2))) νT :=
      slice_integrable T hVbdd ω
    have hstep1 : |∫ t, V (E.symm (t, (E ω).2)) ∂νT|
        ≤ ∫ t, |V (E.symm (t, (E ω).2))| ∂νT := by
      have := norm_integral_le_integral_norm (μ := νT)
        (fun t => V (E.symm (t, (E ω).2)))
      simpa only [Real.norm_eq_abs] using this
    calc |∫ t, V (E.symm (t, (E ω).2)) ∂νT|
        ≤ ∫ t, |V (E.symm (t, (E ω).2))| ∂νT := hstep1
      _ ≤ ∫ _t, C₀ ∂νT := integral_mono hint.abs (integrable_const C₀) (fun t => hbd _)
      _ = C₀ := by rw [integral_const, MeasureTheory.measureReal_def, measure_univ]; simp

/-- **`condCE_forgetSet_congr_ae`** — the `T`-marginal respects a.e. equality:
if `X =ᵐ Y` (both bounded-measurable), then `condCE_forgetSet T X =ᵐ condCE_forgetSet T Y`.
This is the a.e. transport that upgrades the strict disjoint-block product
factorization (`MixedCondProd.condCE_forgetSet_mul`) to an a.e.-robust variant.
Proof: dominate `|E[X−Y | T]|` by `E[|X−Y| | T]`, which is nonnegative with mean
`Ex|X−Y| = 0`, hence a.e. `0`. -/
theorem condCE_forgetSet_congr_ae (T : Finset C.ι) {X Y : C.Ω → ℝ}
    (hX : C.BddMeas X) (hY : C.BddMeas Y) (hXY : X =ᵐ[C.measure] Y) :
    C.condCE_forgetSet T X =ᵐ[C.measure] C.condCE_forgetSet T Y := by
  set Z := fun ω => X ω - Y ω with hZdef
  have hZbdd : C.BddMeas Z := by
    have hshape : Z = fun ω => X ω + (-1 : ℝ) * Y ω := by funext ω; rw [hZdef]; ring
    rw [hshape]; exact C.BddMeas_add hX (C.BddMeas_smul (-1) hY)
  have hZ0 : Z =ᵐ[C.measure] (0 : C.Ω → ℝ) := by
    filter_upwards [hXY] with ω h; rw [hZdef]; simp [h]
  set W := fun ω => |Z ω| with hWdef
  have hWbdd : C.BddMeas W := by
    obtain ⟨hm, C1, hb⟩ := hZbdd
    exact ⟨(_root_.continuous_abs.measurable).comp hm, C1,
      fun ω => by rw [hWdef, abs_abs]; exact hb ω⟩
  have hW0 : W =ᵐ[C.measure] (0 : C.Ω → ℝ) := by
    filter_upwards [hZ0] with ω h; rw [hWdef]; simp [h]
  -- `E[|Z| | T]` is nonnegative and has mean zero, hence a.e. zero.
  have hWnn : 0 ≤ᵐ[C.measure] C.condCE_forgetSet T W := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    show 0 ≤ ∫ t, W _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
    exact integral_nonneg (fun t => by simp only [hWdef]; exact abs_nonneg _)
  have hExW : C.Ex W = 0 := by
    unfold MixedCoinSpace.Ex; rw [integral_congr_ae hW0]; simp
  have hExcond : C.Ex (C.condCE_forgetSet T W) = 0 := by
    rw [C.condCE_forgetSet_cond_Ex T W hWbdd, hExW]
  have hcondW0 : C.condCE_forgetSet T W =ᵐ[C.measure] (0 : C.Ω → ℝ) :=
    (integral_eq_zero_iff_of_nonneg_ae hWnn
      (C.BddMeas_condCE_forgetSet T hWbdd).integrable).mp hExcond
  -- `|E[Z | T]| ≤ E[|Z| | T]` pointwise, so `E[Z | T]` is a.e. zero too.
  have hdom : ∀ ω, |C.condCE_forgetSet T Z ω| ≤ C.condCE_forgetSet T W ω := by
    intro ω
    show |∫ t, Z _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)|
        ≤ ∫ t, W _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
    have := norm_integral_le_integral_norm
      (μ := Measure.pi fun i : {i // i ∈ T} => C.μ i)
      (fun t => Z ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)).symm
        (t, ((MeasurableEquiv.piEquivPiSubtypeProd C.Coin (· ∈ T)) ω).2)))
    simpa only [Real.norm_eq_abs, hWdef] using this
  have hcondZ0 : C.condCE_forgetSet T Z =ᵐ[C.measure] (0 : C.Ω → ℝ) := by
    filter_upwards [hcondW0] with ω h
    have hle := hdom ω
    rw [h] at hle
    simp only [Pi.zero_apply]
    exact abs_nonpos_iff.mp (le_of_le_of_eq hle (by simp))
  -- transport `E[X−Y | T] = E[X|T] − E[Y|T]`.
  have hsub : (fun ω => C.condCE_forgetSet T X ω - C.condCE_forgetSet T Y ω)
      = C.condCE_forgetSet T Z := (C.condCE_forgetSet_sub T X Y hX hY).symm
  filter_upwards [hcondZ0] with ω h
  have hZω : C.condCE_forgetSet T X ω - C.condCE_forgetSet T Y ω = 0 := by
    rw [show C.condCE_forgetSet T X ω - C.condCE_forgetSet T Y ω
          = C.condCE_forgetSet T Z ω from congrFun hsub ω, h, Pi.zero_apply]
  linarith [hZω]

/-- **Scalar homogeneity** of `condCE_forgetSet` (unconditional). -/
theorem condCE_forgetSet_smul (T : Finset C.ι) (c : ℝ) (X : C.Ω → ℝ) :
    C.condCE_forgetSet T (fun ω => c * X ω)
      = fun ω => c * C.condCE_forgetSet T X ω := by
  funext ω
  show ∫ t, c * X _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
      = c * ∫ t, X _ ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i)
  rw [integral_const_mul]

/-- **Conditional expectation of `0`** is `0` (unconditional). -/
theorem condCE_forgetSet_zero (T : Finset C.ι) :
    C.condCE_forgetSet T (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext ω
  show ∫ _t, (0 : ℝ) ∂(Measure.pi fun i : {i // i ∈ T} => C.μ i) = 0
  rw [integral_zero]

/-- **Finite-sum additivity** of `condCE_forgetSet` (`BddMeas`-guarded per summand). -/
theorem condCE_forgetSet_sum {ι : Type} [DecidableEq ι] (T : Finset C.ι)
    (s : Finset ι) (f : ι → C.Ω → ℝ) (hf : ∀ i ∈ s, C.BddMeas (f i)) :
    C.condCE_forgetSet T (fun ω => ∑ i ∈ s, f i ω)
      = fun ω => ∑ i ∈ s, C.condCE_forgetSet T (f i) ω := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact condCE_forgetSet_zero T
  | @insert a s ha ih =>
    have hfa : C.BddMeas (f a) := hf a (Finset.mem_insert_self a s)
    have hrest : ∀ i ∈ s, C.BddMeas (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsumbdd : C.BddMeas (fun ω => ∑ i ∈ s, f i ω) := C.BddMeas_sum s f hrest
    have hstep : C.condCE_forgetSet T (fun ω => ∑ i ∈ insert a s, f i ω)
        = fun ω => C.condCE_forgetSet T (f a) ω
                    + C.condCE_forgetSet T (fun ω => ∑ i ∈ s, f i ω) ω := by
      have hrw : (fun ω => ∑ i ∈ insert a s, f i ω)
          = fun ω => f a ω + ∑ i ∈ s, f i ω := by
        funext ω; rw [Finset.sum_insert ha]
      rw [hrw]; exact condCE_forgetSet_add T (f a) (fun ω => ∑ i ∈ s, f i ω) hfa hsumbdd
    rw [hstep, ih hrest]
    funext ω; rw [Finset.sum_insert ha]

end MixedCoinSpace

end Arlib.Probability
