/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The product of `m` independent uniforms: identifying `tpaTail`

`Arlib.Algorithms.TPA.Count` introduces the closed form

  `tpaTail m c = 1 - c · ∑_{j < m} (ln(1/c))^j / j!`

and proves the one-dimensional recursion `∫_c^1 tpaTail m (c/u) du = tpaTail (m+1) c`
that characterises it.  This file closes the remaining gap: it proves that the
*intended* reading of `tpaTail` is correct, namely

  `P(U₁ ⋯ U_m > c) = tpaTail m c`   for independent `Uniform(0,1)` variables.

Without this identification the whole TPA analysis rests on an unproved reading
of a formula.

## The set-up

The uniform law on `[0,1]` is `unifUnit = volume.restrict (Set.Icc 0 1)`; since
`Real.volume_Icc` gives it total mass `1` it is a probability measure, and
`MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit)` is the law of `m`
independent uniforms.  The event `{U₁ ⋯ U_m > c}` is the measurable set
`{u : Fin m → ℝ | c < ∏ i, u i}`, and `volume_prod_gt` computes its measure.

## The argument

Induction on `m`.

* `m = 0`: the empty product is `1`, so the event is everything when `c < 1` and
  the measure is `1 = tpaTail 0 c`.  **This is the only place `c < 1` is used**,
  and it is genuinely needed: at `c = 1` the event `{1 > 1}` is empty while
  `tpaTail 0 1 = 1`.  See the discussion under "Sharpness" below.

* `m+1`: `MeasureTheory.measurePreserving_piFinSuccAbove` with `i = 0` identifies
  the product measure on `Fin (m+1)` with `unifUnit.prod (Measure.pi …)`, under
  which the event becomes `{p | c < p.1 * ∏ j, p.2 j}` (`Fin.prod_univ_succ`).
  Tonelli (`MeasureTheory.Measure.prod_apply`) turns its measure into
  `∫⁻ u₀, μ_m {v | c < u₀ * ∏ v} ∂unifUnit`.  The inner measure is:
  - `0` for `u₀ ≤ c`, because `μ_m` lives on `[0,1]^m` where the product is at
    most `1`, so `u₀ · ∏ v ≤ u₀ ≤ c` (`measure_setOf_mul_prod_gt_eq_zero`); this
    is the "set is null" route, which avoids ever evaluating `tpaTail` outside
    `(0,1)`;
  - `ENNReal.ofReal (tpaTail m (c/u₀))` for `c < u₀ ≤ 1` by the induction
    hypothesis, since then `0 < c/u₀ < 1`.
  So the `lintegral` collapses to one over `Set.Ioc c 1`, which converts to the
  Bochner interval integral `∫ u in c..1, tpaTail m (c/u)` — this needs
  `tpaTail_nonneg` and the integrability supplied by
  `Arlib.Algorithms.TPA.continuousOn_tpaTail_div` — and `Arlib.Algorithms.TPA.tpaTail_succ` finishes.

## Sharpness of the hypotheses

`Count.lean` records neither `c < 1` nor `c ≤ 1`, and both boundaries matter:

* At `c = 1` the identification **fails, and exactly at `m = 0`**:
  `tpaTail m 1 = 1 - 1 = 0` for `m ≥ 1`, which is the correct value of
  `P(U₁ ⋯ U_m > 1)`, but `tpaTail 0 1 = 1` whereas
  `P(empty product > 1) = P(1 > 1) = 0`.  So `m = 0` is the sole obstruction and
  `hc1 : c < 1` is exactly what removes it.
* For `c > 1` the closed form is not a probability at all (it can be negative),
  while the true probability is `0`.

Both `0 < c` and `c < 1` are therefore assumed throughout.

## The payoff

`prob_exactly_eq_poissonPMF`: the probability that a run needs *exactly* `m`
contractions — the difference of two consecutive tails — is the Poisson mass
`Arlib.poissonPMF (ln(1/c)) m`.  This is `Arlib.Algorithms.TPA.tpaTail_sub` transported
along the identification, and it is the statement the TPA analysis actually uses.
-/
import Arlib.Algorithms.TPA.Count
import Arlib.Probability.Poisson
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.SetIntegral

namespace Arlib.Algorithms.TPA

open scoped BigOperators ENNReal
open MeasureTheory

/-! ## Nonnegativity of the closed form

To move between `ENNReal.ofReal` and reals we need `tpaTail m c ≥ 0` on the
intended domain `(0, 1]`.  Deriving this from the probabilistic meaning would be
circular, so we prove it directly from the exponential series: with
`A = -log c ≥ 0`, every partial sum of `∑ A^j/j!` is at most `e^A = 1/c`. -/

/-- **The closed form is a probability.**  For `c ∈ (0, 1]`, `tpaTail m c ≥ 0`,
because `c · ∑_{j<m} A^j/j! ≤ c · e^A = 1` with `A = -log c ≥ 0`. -/
theorem tpaTail_nonneg (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ tpaTail m c := by
  set A : ℝ := -Real.log c with hA
  have hA0 : 0 ≤ A := by
    have := Real.log_nonpos (le_of_lt hc) hc1
    simpa [hA] using this
  have hterm : ∀ j : ℕ, 0 ≤ A ^ j / (Nat.factorial j : ℝ) := by
    intro j
    positivity
  have hpart : ∑ j ∈ Finset.range m, A ^ j / (Nat.factorial j : ℝ) ≤ Real.exp A :=
    sum_le_hasSum _ (fun j _ => hterm j) (Arlib.hasSum_exp_series A)
  have hexp : Real.exp A = c⁻¹ := by
    rw [hA, Real.exp_neg, Real.exp_log hc]
  have hmul : c * ∑ j ∈ Finset.range m, A ^ j / (Nat.factorial j : ℝ) ≤ c * c⁻¹ := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hpart (le_of_lt hc)
  rw [mul_inv_cancel₀ (ne_of_gt hc)] at hmul
  simpa [tpaTail, hA, sub_nonneg] using hmul

/-! ## The uniform law on `[0,1]` and the event `{∏ Uᵢ > c}` -/

/-- The `Uniform(0,1)` law, as Lebesgue measure restricted to `[0,1]`.  It is a
probability measure because `Real.volume_Icc` gives `volume (Icc 0 1) = 1`. -/
noncomputable def unifUnit : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The uniform law puts all its mass on `[0,1]`. -/
@[simp] theorem unifUnit_apply_Icc : unifUnit (Set.Icc (0 : ℝ) 1) = 1 := by
  rw [unifUnit, Measure.restrict_apply_self, Real.volume_Icc]
  norm_num

/-- Integrating against `unifUnit` is integrating over `[0,1]` against `volume`.
Stated so that the outer measure of an iterated integral can be unfolded without
also unfolding the `unifUnit`s occurring in the integrand. -/
theorem lintegral_unifUnit (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, f t ∂unifUnit = ∫⁻ t in Set.Icc (0 : ℝ) 1, f t := rfl

/-- `unifUnit` is a probability measure, so `Measure.pi (fun _ => unifUnit)` is
one too and `Measure.prod_apply` (Tonelli) applies. -/
instance : IsProbabilityMeasure unifUnit := by
  constructor
  rw [unifUnit, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- The event that the product of `m` coordinates exceeds `c`. -/
def prodGt (m : ℕ) (c : ℝ) : Set (Fin m → ℝ) := {u : Fin m → ℝ | c < ∏ i, u i}

/-- The event `{∏ uᵢ > c}` is measurable: the coordinate product is a finite
product of measurable coordinate projections. -/
theorem measurableSet_prodGt (m : ℕ) (c : ℝ) : MeasurableSet (prodGt m c) := by
  have hmeas : Measurable fun u : Fin m → ℝ => ∏ i, u i :=
    Finset.univ.measurable_prod fun i _ => measurable_pi_apply i
  exact measurableSet_lt measurable_const hmeas

/-! ## The product measure lives on the unit box -/

/-- The unit box `[0,1]^m`, on which `Measure.pi (fun _ => unifUnit)` is carried. -/
def unitBox (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi fun _ : Fin m => Set.Icc (0 : ℝ) 1

/-- The unit box is measurable, being a product of intervals. -/
theorem measurableSet_unitBox (m : ℕ) : MeasurableSet (unitBox m) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The unit box has full measure: it is the whole support of the product of
uniform laws. -/
theorem measure_unitBox (m : ℕ) :
    Measure.pi (fun _ : Fin m => unifUnit) (unitBox m) = 1 := by
  rw [unitBox, Measure.pi_pi]
  simp

/-- Everything outside the unit box is null. -/
theorem measure_compl_unitBox (m : ℕ) :
    Measure.pi (fun _ : Fin m => unifUnit) (unitBox m)ᶜ = 0 := by
  rw [measure_compl (measurableSet_unitBox m) (by rw [measure_unitBox]; exact ENNReal.one_ne_top),
    measure_univ, measure_unitBox, tsub_self]

/-- A product of numbers in `[0,1]` again lies in `[0,1]`. -/
theorem prod_mem_Icc_of_mem_unitBox {m : ℕ} {v : Fin m → ℝ} (hv : v ∈ unitBox m) :
    (∏ i, v i) ∈ Set.Icc (0 : ℝ) 1 := by
  have hv' : ∀ i : Fin m, v i ∈ Set.Icc (0 : ℝ) 1 := fun i => hv i (Set.mem_univ i)
  constructor
  · exact Finset.prod_nonneg fun i _ => (hv' i).1
  · exact Finset.prod_le_one (fun i _ => (hv' i).1) (fun i _ => (hv' i).2)

/-- **The event is null when the first factor is too small.**  If `0 ≤ t ≤ c`
then no point of the unit box satisfies `c < t · ∏ vᵢ`, since the product is at
most `1`.  This is the "set is null" route: it never evaluates `tpaTail` outside
its intended domain. -/
theorem measure_setOf_mul_prod_gt_eq_zero (m : ℕ) {c t : ℝ} (ht0 : 0 ≤ t) (htc : t ≤ c) :
    Measure.pi (fun _ : Fin m => unifUnit) {v : Fin m → ℝ | c < t * ∏ i, v i} = 0 := by
  refine measure_mono_null ?_ (measure_compl_unitBox m)
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_compl_iff]
  intro hbox
  have hp := prod_mem_Icc_of_mem_unitBox hbox
  have : t * ∏ i, v i ≤ t := by
    calc t * ∏ i, v i ≤ t * 1 := by
          exact mul_le_mul_of_nonneg_left hp.2 ht0
      _ = t := mul_one t
  exact absurd hv (not_lt.mpr (le_trans this htc))

/-! ## Splitting off the first coordinate -/

/-- The image of `prodGt (m+1) c` under the "first coordinate / rest" splitting. -/
def prodGtPair (m : ℕ) (c : ℝ) : Set (ℝ × (Fin m → ℝ)) :=
  {p | c < p.1 * ∏ j, p.2 j}

/-- The split form of the event is measurable. -/
theorem measurableSet_prodGtPair (m : ℕ) (c : ℝ) : MeasurableSet (prodGtPair m c) := by
  have hmeas : Measurable fun p : ℝ × (Fin m → ℝ) => p.1 * ∏ j, p.2 j :=
    measurable_fst.mul (Finset.univ.measurable_prod fun j _ =>
      (measurable_pi_apply j).comp measurable_snd)
  exact measurableSet_lt measurable_const hmeas

/-- **Tonelli after splitting off the first coordinate.**  Transporting the
product measure along `MeasurableEquiv.piFinSuccAbove … 0` and applying
`Measure.prod_apply` expresses the measure of `{∏ uᵢ > c}` on `Fin (m+1)` as an
integral over the first coordinate of the measure of the conditional event. -/
theorem measure_prodGt_succ (m : ℕ) (c : ℝ) :
    Measure.pi (fun _ : Fin (m + 1) => unifUnit) (prodGt (m + 1) c)
      = ∫⁻ t, Measure.pi (fun _ : Fin m => unifUnit)
          {v : Fin m → ℝ | c < t * ∏ i, v i} ∂unifUnit := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => unifUnit)
      (unifUnit.prod (Measure.pi fun _ : Fin m => unifUnit)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => unifUnit) 0
  have hpre : e ⁻¹' prodGtPair m c = prodGt (m + 1) c := by
    ext u
    simp [he, prodGtPair, prodGt, Fin.prod_univ_succ, Fin.tail]
  rw [← hpre, hmp.measure_preimage_equiv,
    Measure.prod_apply (measurableSet_prodGtPair m c)]
  rfl

/-! ## From the `lintegral` back to the recursion of `Count.lean` -/

/-- On `(c, 1]` the argument `c/t` of `tpaTail` lies in `(0, 1)`, so the
integrand is a genuine probability. -/
theorem tpaTail_div_nonneg (m : ℕ) {c t : ℝ} (hc : 0 < c) (ht : t ∈ Set.Ioc c 1) :
    0 ≤ tpaTail m (c / t) := by
  have ht0 : 0 < t := lt_trans hc ht.1
  exact tpaTail_nonneg m (div_pos hc ht0) ((div_le_one ht0).mpr (le_of_lt ht.1))

/-- **The `lintegral` form of the recursion.**  Converting `ENNReal.ofReal` to a
Bochner integral over `Set.Ioc c 1` — legitimate by `tpaTail_nonneg` and the
integrability supplied by `continuousOn_tpaTail_div` — turns the
`lintegral` into `∫ u in c..1, tpaTail m (c/u)`, which is `tpaTail (m+1) c` by
`Arlib.Algorithms.TPA.tpaTail_succ`. -/
theorem lintegral_ofReal_tpaTail_div (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫⁻ t in Set.Ioc c 1, ENNReal.ofReal (tpaTail m (c / t)))
      = ENNReal.ofReal (tpaTail (m + 1) c) := by
  have hint : IntegrableOn (fun t => tpaTail m (c / t)) (Set.Ioc c 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc1).mp
      ((continuousOn_tpaTail_div m hc).intervalIntegrable)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc c 1)] fun t => tpaTail m (c / t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact tpaTail_div_nonneg m hc ht
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hc1,
    tpaTail_succ m hc]

/-- For a positive first factor `t`, the conditional event is again an event of
the same shape, with `c` replaced by `c/t`. -/
theorem setOf_mul_prod_gt_eq_prodGt (m : ℕ) {c t : ℝ} (ht : 0 < t) :
    {v : Fin m → ℝ | c < t * ∏ i, v i} = prodGt m (c / t) := by
  ext v
  simp only [Set.mem_setOf_eq, prodGt, div_lt_iff₀ ht, mul_comm]

/-- **The inductive step, as a computation of the conditional integral.**  Split
`[0,1]` at `c`: below `c` the conditional event is null
(`measure_setOf_mul_prod_gt_eq_zero`), above `c` the induction hypothesis
applies because `0 < c/t < 1`. -/
theorem lintegral_cond_measure (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ih : ∀ d : ℝ, 0 < d → d < 1 →
      Measure.pi (fun _ : Fin m => unifUnit) (prodGt m d) = ENNReal.ofReal (tpaTail m d)) :
    (∫⁻ t, Measure.pi (fun _ : Fin m => unifUnit)
        {v : Fin m → ℝ | c < t * ∏ i, v i} ∂unifUnit)
      = ∫⁻ t in Set.Ioc c 1, ENNReal.ofReal (tpaTail m (c / t)) := by
  rw [lintegral_unifUnit]
  have hsplit : Set.Icc (0 : ℝ) 1 = Set.Icc 0 c ∪ Set.Ioc c 1 :=
    (Set.Icc_union_Ioc_eq_Icc hc.le hc1).symm
  have hdisj : Disjoint (Set.Icc (0 : ℝ) c) (Set.Ioc c 1) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht'.1 (not_lt.mpr ht.2)
  rw [hsplit, lintegral_union measurableSet_Ioc hdisj]
  have hlow : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0 : ℝ) c →
      Measure.pi (fun _ : Fin m => unifUnit) {v : Fin m → ℝ | c < t * ∏ i, v i} = 0 :=
    ae_of_all _ fun t ht => measure_setOf_mul_prod_gt_eq_zero m ht.1 ht.2
  have hhigh : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc c 1 →
      Measure.pi (fun _ : Fin m => unifUnit) {v : Fin m → ℝ | c < t * ∏ i, v i}
        = ENNReal.ofReal (tpaTail m (c / t)) := by
    refine ae_of_all _ fun t ht => ?_
    have ht0 : 0 < t := lt_trans hc ht.1
    rw [setOf_mul_prod_gt_eq_prodGt m ht0]
    exact ih (c / t) (div_pos hc ht0) ((div_lt_one ht0).mpr ht.1)
  rw [setLIntegral_congr_fun measurableSet_Icc hlow, lintegral_zero, zero_add,
    setLIntegral_congr_fun measurableSet_Ioc hhigh]

/-! ## The identification -/

/-- **The product of `m` independent uniforms exceeds `c` with probability
`tpaTail m c`**, in terms of `prodGt`.  Induction on `m`: the base case is the
empty product `1 > c` (this is the only use of `c < 1`), and the step is
`measure_prodGt_succ`, `lintegral_cond_measure`, `lintegral_ofReal_tpaTail_div`. -/
theorem measure_prodGt (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Measure.pi (fun _ : Fin m => unifUnit) (prodGt m c) = ENNReal.ofReal (tpaTail m c) := by
  induction m generalizing c with
  | zero =>
    have hset : prodGt 0 c = Set.univ := by
      ext u
      simp [prodGt, hc1]
    rw [hset, measure_univ, tpaTail_zero, ENNReal.ofReal_one]
  | succ m ih =>
    rw [measure_prodGt_succ, lintegral_cond_measure m hc (le_of_lt hc1)
        (fun d hd hd1 => ih hd hd1),
      lintegral_ofReal_tpaTail_div m hc (le_of_lt hc1)]

/-- **The product of `m` independent uniforms exceeds `c` with probability
`tpaTail m c`.**  This is the identification that the closed form of
`Arlib.Algorithms.TPA.Count` was designed to have; `Count.lean` proves only the
one-dimensional recursion, and this theorem is what licenses reading `tpaTail m c`
as `P(U₁ ⋯ U_m > c)`.

The hypothesis `c < 1` is genuinely needed, and only at `m = 0`: at `c = 1` the
event `{1 > 1}` is empty while `tpaTail 0 1 = 1`. -/
theorem volume_prod_gt (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}
      = ENNReal.ofReal (tpaTail m c) :=
  measure_prodGt m hc hc1

/-- The real-valued form of `volume_prod_gt`. -/
theorem volume_prod_gt_toReal (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ((MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}).toReal
      = tpaTail m c := by
  rw [volume_prod_gt m hc hc1, ENNReal.toReal_ofReal (tpaTail_nonneg m hc (le_of_lt hc1))]

/-! ## The payoff: the TPA counter is Poisson -/

/-- **The TPA counter is Poisson.**  The probability that a run needs exactly `m`
contractions — the difference `P(N ≥ m) − P(N ≥ m+1)` of two consecutive
uniform-product tail probabilities — is the Poisson mass
`e^{-A} A^m / m!` with `A = ln(1/c) = -Real.log c`.

This is `Arlib.Algorithms.TPA.tpaTail_sub` transported along `volume_prod_gt`, together with
`Real.exp_log`, which turns the factor `c` into `e^{-A}`. -/
theorem prob_exactly_eq_poissonPMF (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ((MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}).toReal
      - ((MeasureTheory.Measure.pi (fun _ : Fin (m + 1) => unifUnit))
        {u : Fin (m + 1) → ℝ | c < ∏ i, u i}).toReal
      = Arlib.poissonPMF (-Real.log c) m := by
  rw [volume_prod_gt_toReal m hc hc1, volume_prod_gt_toReal (m + 1) hc hc1, tpaTail_sub m c,
    Arlib.poissonPMF, neg_neg, Real.exp_log hc]

end Arlib.Algorithms.TPA
