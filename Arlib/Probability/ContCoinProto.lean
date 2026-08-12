/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A continuous [0,1] "keep-coin": a self-contained prototype

**Standalone, self-contained** (imports only Mathlib).  This file shows that
replacing a discrete `Fin K` keep-coin (`IsQuant`, `uniform_cdf_eq`) by a
continuous `[0,1]`-uniform keep-coin gives a **pointwise, everywhere-defined**
coordinate-marginal conditional expectation whose one computational primitive is

  `∫₀¹ 𝟙_{u < τ} du = τ`   for ANY real `τ ∈ [0,1]`.

Nothing here is `sorry`; the marginal identities are stated and proved with **no
a.e./integrability side-condition in the STATEMENTS** — integrability is
discharged internally from boundedness (the indicator is antitone, hence interval
integrable) and never leaks out.

The continuous analogues, without any quantization hypothesis:
  * `Eu_threshold`               — the 2-point step-function marginal
  * `condCE_forget_threshold`    — the continuous analogue of the reduce step
  * `condCE_forget_const`        — conditioning a constant returns the constant
  * iterated marginals compose pointwise (tower-rule shape)
  * `Ex` / `Ex_const`            — total-mass-1 expectation over the product
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Arlib.Probability.ContCoinProto

open MeasureTheory Set

/-! ## 1. One continuous coin: the `[0,1]`-uniform coordinate expectation -/

/-- The coordinate expectation of one `[0,1]`-uniform keep-coin: integrate over
`[0,1]` (which has total mass 1, so this is a genuine average). -/
noncomputable def Eu (f : ℝ → ℝ) : ℝ := ∫ u in (0:ℝ)..1, f u

/-- Marginal of a constant is itself (the coin has total mass 1). -/
theorem Eu_const (c : ℝ) : Eu (fun _ => c) = c := by
  unfold Eu; rw [intervalIntegral.integral_const]; simp

/-- The two-point step function `𝟙_{u < τ}` is antitone in `u` (jumps `1 → 0` at
`τ`), hence interval integrable on any interval — **the only place integrability
is used, and it is discharged from monotonicity, never surfacing in a statement**. -/
theorem indicator_antitone (τ : ℝ) :
    Antitone (fun u : ℝ => if u < τ then (1:ℝ) else 0) := by
  intro a b hab
  by_cases hb : b < τ
  · have ha : a < τ := lt_of_le_of_lt hab hb
    simp [ha, hb]
  · simp only [hb, if_false]
    split_ifs <;> norm_num

/-! ## 2. THE KEY LEMMA: `∫₀¹ 𝟙_{u<τ} du = τ` for any real `τ ∈ [0,1]`. -/

/-- **The linchpin (indicator form).**  For real `τ ∈ [0,1]`,
`∫₀¹ 𝟙_{u < τ} du = τ`.  Proved as an equality of set integrals — *no
integrability hypothesis*: `integral_of_le`, `setIntegral_indicator`,
`setIntegral_const`, `Real.volume_Ioo`. -/
theorem Eu_indicator (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    Eu (fun u => if u < τ then (1:ℝ) else 0) = τ := by
  have hset : Set.Ioc (0:ℝ) 1 ∩ Set.Iio τ = Set.Ioo 0 τ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hx0, _⟩, hxτ⟩; exact ⟨hx0, hxτ⟩
    · rintro ⟨hx0, hxτ⟩; exact ⟨⟨hx0, le_of_lt (lt_of_lt_of_le hxτ h1)⟩, hxτ⟩
  have hfun : (fun u => if u < τ then (1:ℝ) else 0)
      = Set.indicator (Set.Iio τ) (fun _ => (1:ℝ)) := by
    funext u; rw [Set.indicator_apply]; simp [Set.mem_Iio]
  unfold Eu
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    MeasureTheory.setIntegral_indicator measurableSet_Iio,
    MeasureTheory.setIntegral_const, hset, MeasureTheory.measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith)]
  simp

/-- **THE KEY LEMMA — `Eu_threshold`.**  The 2-point step-function marginal that
every estimator reduces to: each keep-coin is compared to exactly one threshold.
For real `τ ∈ [0,1]` and reals `a b`,
`∫₀¹ (a · 𝟙_{u<τ} + b) du = a·τ + b`.  Everywhere; no a.e., no integrability in
the statement. -/
theorem Eu_threshold (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (a b : ℝ) :
    Eu (fun u => a * (if u < τ then (1:ℝ) else 0) + b) = a * τ + b := by
  have hind : IntervalIntegrable (fun u => if u < τ then (1:ℝ) else 0) volume 0 1 :=
    (indicator_antitone τ).intervalIntegrable
  have hInd : (∫ u in (0:ℝ)..1, if u < τ then (1:ℝ) else 0) = τ := Eu_indicator τ h0 h1
  unfold Eu
  rw [intervalIntegral.integral_add (hind.const_mul a) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hInd, intervalIntegral.integral_const]
  simp

/-! ## 3. The mixed `finite × [0,1]` product space and its pointwise marginal

A mixed outcome space has finite "draw" coordinates and continuous
`[0,1]` "keep" coordinates.  We model a tiny instance and show the coordinate
marginal over one keep-coordinate is **pointwise, everywhere-defined**. -/

/-- Finite draw coordinates (e.g. sampled elements). -/
abbrev Draw (m : ℕ) := Fin m → Bool
/-- Continuous `[0,1]` keep coordinates (the keep-coins). -/
abbrev Keep (k : ℕ) := Fin k → ℝ
/-- One point of the mixed execution space. -/
abbrev Space (m k : ℕ) := Draw m × Keep k

/-- **Pointwise coordinate marginal.**  `condCE(forget keep-coord j) X ω` replaces
keep-coord `j` by the `[0,1]`-uniform integration variable and integrates — the
exact analogue of `CoinSpace.condCE_forget`, but with a continuous coin.  It is a
plain function of `ω`: everywhere-defined, no a.e. equivalence class. -/
noncomputable def condCE_forget {m k : ℕ} (j : Fin k) (X : Space m k → ℝ)
    (ω : Space m k) : ℝ :=
  Eu (fun u => X (ω.1, Function.update ω.2 j u))

/-- **`CFixed`-style "reads only the other coordinates".**  `f` does not read
keep-coord `j`: it is invariant under overwriting that coordinate.  This is the
continuous analogue of `CFixed C.toFinProb (C.forget j)`. -/
def KFixed {m k : ℕ} (j : Fin k) (f : Space m k → ℝ) : Prop :=
  ∀ ω u, f (ω.1, Function.update ω.2 j u) = f ω

/-- **Sanity — `condCE_const`.**  The marginal of a coord-`j`-independent function
is itself, everywhere.  Mirrors `condCE_const_of_pos` with no positivity/measure
hypothesis. -/
theorem condCE_forget_const {m k : ℕ} (j : Fin k) (X : Space m k → ℝ)
    (hX : KFixed j X) (ω : Space m k) : condCE_forget j X ω = X ω := by
  unfold condCE_forget
  have h : (fun u => X (ω.1, Function.update ω.2 j u)) = fun _ => X ω := by
    funext u; exact hX ω u
  rw [h, Eu_const]

/-- **PROTOTYPE `condCE_forget_threshold`** (the payload).  For
`X ω = A ω · 𝟙_{ω.keep j < τ ω} + B ω` where `A, B, τ` do **not** read keep-coord
`j`, the coordinate marginal is `A ω · τ ω + B ω`, **EVERYWHERE** (no a.e.), for
any real `τ ω ∈ [0,1]` — no quantization.  This is the continuous replacement for
the finite reduce step `ReduceModel.condCE_reduceStep`. -/
theorem condCE_forget_threshold {m k : ℕ} (j : Fin k) (A B τ : Space m k → ℝ)
    (hA : KFixed j A) (hB : KFixed j B) (hτ : KFixed j τ)
    (ω : Space m k) (h0 : 0 ≤ τ ω) (h1 : τ ω ≤ 1) :
    condCE_forget j (fun ω' => A ω' * (if ω'.2 j < τ ω' then (1:ℝ) else 0) + B ω') ω
      = A ω * τ ω + B ω := by
  unfold condCE_forget
  have key : (fun u => (fun ω' => A ω' * (if ω'.2 j < τ ω' then (1:ℝ) else 0) + B ω')
                (ω.1, Function.update ω.2 j u))
           = (fun u => A ω * (if u < τ ω then (1:ℝ) else 0) + B ω) := by
    funext u
    show A (ω.1, Function.update ω.2 j u)
          * (if (Function.update ω.2 j u) j < τ (ω.1, Function.update ω.2 j u)
             then (1:ℝ) else 0)
          + B (ω.1, Function.update ω.2 j u)
        = A ω * (if u < τ ω then (1:ℝ) else 0) + B ω
    rw [hA ω u, hB ω u, hτ ω u, Function.update_self]
  rw [key]
  exact Eu_threshold (τ ω) h0 h1 (A ω) (B ω)

/-! ## 4. Iterated marginals compose pointwise (the tower-rule shape) -/

/-- Iterated marginals of a function independent of two keep-coords return it,
everywhere.  Confirms the pointwise operators compose (the shape of
`condCE_tower`). -/
theorem condCE_forget_forget_const {m k : ℕ} (j₁ j₂ : Fin k) (X : Space m k → ℝ)
    (hX1 : KFixed j₁ X) (hX2 : KFixed j₂ X) (ω : Space m k) :
    condCE_forget j₁ (condCE_forget j₂ X) ω = X ω := by
  have hinner : condCE_forget j₂ X = X := by
    funext ω'; exact condCE_forget_const j₂ X hX2 ω'
  rw [hinner]
  exact condCE_forget_const j₁ X hX1 ω

/-- **Composition mirroring a real reduce step then coarser conditioning.**  A
reduce over keep-coord `j₂` produces `A·τ + B` (via `condCE_forget_threshold`);
conditioning that on a filtration that also forgets `j₁` returns it, since `A,B,τ`
read neither coord.  Two pointwise marginals chained with a clean closed form. -/
theorem condCE_forget_threshold_then_forget {m k : ℕ} (j₁ j₂ : Fin k)
    (A B τ : Space m k → ℝ)
    (hA2 : KFixed j₂ A) (hB2 : KFixed j₂ B) (hτ2 : KFixed j₂ τ)
    (hA1 : KFixed j₁ A) (hB1 : KFixed j₁ B) (hτ1 : KFixed j₁ τ)
    (h0 : ∀ ω, 0 ≤ τ ω) (h1 : ∀ ω, τ ω ≤ 1) (ω : Space m k) :
    condCE_forget j₁
        (condCE_forget j₂
          (fun ω' => A ω' * (if ω'.2 j₂ < τ ω' then (1:ℝ) else 0) + B ω')) ω
      = A ω * τ ω + B ω := by
  have hinner : condCE_forget j₂
        (fun ω' => A ω' * (if ω'.2 j₂ < τ ω' then (1:ℝ) else 0) + B ω')
      = fun ω' => A ω' * τ ω' + B ω' := by
    funext ω'
    exact condCE_forget_threshold j₂ A B τ hA2 hB2 hτ2 ω' (h0 ω') (h1 ω')
  rw [hinner]
  have hfix : KFixed j₁ (fun ω' => A ω' * τ ω' + B ω') := by
    intro ζ u
    show A (ζ.1, Function.update ζ.2 j₁ u) * τ (ζ.1, Function.update ζ.2 j₁ u)
          + B (ζ.1, Function.update ζ.2 j₁ u)
        = A ζ * τ ζ + B ζ
    rw [hA1 ζ u, hτ1 ζ u, hB1 ζ u]
  exact condCE_forget_const j₁ (fun ω' => A ω' * τ ω' + B ω') hfix ω

/-! ## 5. The full product expectation `Ex` (shape of the `CoinSpace` rebuild)

`Ex X = ∑_draws mass(draw) · ∫_{[0,1]^k} X(draw, keep) dkeep`, using the product
`[0,1]`-uniform measure on the keep-coords (a probability measure).  We confirm
`Ex 1 = 1` (total mass 1) — the continuous analogue of `CoinSpace.toFinProb`'s
`mass_sum`. -/

/-- The `[0,1]`-uniform probability measure on one keep-coordinate. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  unfold unitMeasure
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simp

/-- The product `[0,1]`-uniform measure on all `k` keep-coordinates. -/
noncomputable def keepMeasure (k : ℕ) : Measure (Keep k) :=
  Measure.pi (fun _ => unitMeasure)

instance (k : ℕ) : IsProbabilityMeasure (keepMeasure k) := by
  unfold keepMeasure; infer_instance

/-- The full mixed-product expectation: finite sum over draws (with an arbitrary
draw distribution) times the product `[0,1]` integral over the keep-coords. -/
noncomputable def Ex {m k : ℕ} (drawMass : Draw m → ℝ) (X : Space m k → ℝ) : ℝ :=
  ∑ d : Draw m, drawMass d * ∫ u : Keep k, X (d, u) ∂(keepMeasure k)

/-- **`Ex 1 = 1`.**  The mixed product has total mass 1: the keep integral of a
constant is the constant (probability measure), and the draw masses sum to 1.
Analogue of `CoinSpace.toFinProb`'s `mass_sum`. -/
theorem Ex_const {m k : ℕ} (drawMass : Draw m → ℝ) (hsum : ∑ d, drawMass d = 1)
    (c : ℝ) : Ex drawMass (fun _ : Space m k => c) = c := by
  unfold Ex
  have hint : ∀ d : Draw m,
      (∫ _u : Keep k, (fun _ : Space m k => c) (d, _u) ∂(keepMeasure k)) = c := by
    intro d
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def, measure_univ]; simp
  rw [Finset.sum_congr rfl (fun d _ => by rw [hint d]), ← Finset.sum_mul, hsum, one_mul]

end Arlib.Probability.ContCoinProto
