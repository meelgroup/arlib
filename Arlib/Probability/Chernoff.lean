/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Multiplicative Chernoff bounds for fully independent indicators

`KWiseChernoff` gives exponential tail bounds under a *budgeted* independence
assumption, at the price of a lossy constant (`1/35`) and side conditions.  When
the coordinates are **fully** independent — which is exactly the situation over
`Arlib.prodSpace` — the sharp classical bounds are available, and this file
proves them.

The setting is a finite product `∏_j μ j` of finite distributions on a common
outcome type `X`, a block `s : Finset ι` of coordinates, and a "success" set
`A j ⊆ X` for each coordinate.  Writing

* `indicCount s A ω = #{j ∈ s | ω j ∈ A j}` — how many coordinates succeed,
* `indicMean μ s A = ∑_{j ∈ s} ∑_{x ∈ A j} μ j x` — its mean `m`,

the file proves, in order:

* `Ex_indicCount` — `E[indicCount] = indicMean`.
* `mgf_indicCount` — the **moment generating function**, and the only place
  independence is used: `E[e^{r·indicCount}] = ∏_{j ∈ s} (1 + (e^r - 1) q_j)`
  with `q_j = ∑_{x ∈ A j} μ j x`.  It is `Ex_prod_apply` applied to the
  factorization `e^{r·#} = ∏_j (if ω j ∈ A j then e^r else 1)`.
* `chernoff_upper` — `Pr[count ≥ (1+t)m] ≤ exp (-t²m / (2+t))` for `t > 0`.
* `chernoff_lower` — `Pr[count ≤ (1-t)m] ≤ exp (-t²m / 2)` for `t > 0`.
* `chernoff_two_sided` — `Pr[|count - m| > tm] ≤ 2 exp (-t²m / 3)` for
  `0 < t ≤ 1`.

The exponents come from two elementary calculus facts, proved here from the mean
value theorem (`log_ineq_upper`, `log_ineq_lower`):

  `t²/(2+t) ≤ (1+t) log (1+t) - t`  and  `t²/2 ≤ (1-t) log (1-t) + t`.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.IIDProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Calculus preliminaries -/

/-- If `f` vanishes at `a` and has a nonnegative derivative throughout `Ico a b`,
then `f` is nonnegative on `Ico a b`. -/
private theorem nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Ico a b, HasDerivAt f (f' x) x)
    (h0 : f a = 0) (hd : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) :
    ∀ x ∈ Set.Ico a b, 0 ≤ f x := by
  intro x hx
  have hab : a < b := lt_of_le_of_lt hx.1 hx.2
  have hmono : MonotoneOn f (Set.Ico a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico a b) ?_ ?_ ?_
    · exact fun y hy => (hf y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      exact ((hf y ⟨hy.1.le, hy.2⟩).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      rw [(hf y ⟨hy.1.le, hy.2⟩).deriv]
      exact hd y hy
  have hmem : a ∈ Set.Ico a b := ⟨le_rfl, hab⟩
  have := hmono hmem hx hx.1
  rw [h0] at this
  exact this

/-- The derivative of `x ↦ log (1 + x) - 2 + 4 / (2 + x)`, which is `x²/((1+x)(2+x)²)`. -/
private theorem hasDerivAt_upperAux {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y) - 2 + 4 / (2 + y))
      (x ^ 2 / ((1 + x) * (2 + x) ^ 2)) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by positivity
  have h2 : (2 : ℝ) + x ≠ 0 := by positivity
  have hlin1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id' (x := x)).const_add (1 : ℝ)
  have hlin2 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
    simpa using (hasDerivAt_id' (x := x)).const_add (2 : ℝ)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := hlin1.log h1
  have hdiv : HasDerivAt (fun y : ℝ => 4 / (2 + y))
      ((0 * (2 + x) - 4 * 1) / (2 + x) ^ 2) x :=
    (hasDerivAt_const x (4 : ℝ)).div hlin2 h2
  exact ((hlog.sub_const (2 : ℝ)).add hdiv).congr_deriv (by field_simp; ring)

/-- The derivative of `x ↦ (1 - x) log (1 - x) + x - x²/2`, which is `-log (1 - x) - x`. -/
private theorem hasDerivAt_lowerAux {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2)
      (-Real.log (1 - x) - x) x := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt hpos
  have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' (x := x)).const_sub (1 : ℝ)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x := hlin.log hne
  exact (((hlin.mul hlog).add (hasDerivAt_id' (x := x))).sub
    ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv (by field_simp; ring)

/-- `2t / (2 + t) ≤ log (1 + t)` for `t ≥ 0`. -/
private theorem log_lower_aux {t : ℝ} (ht : 0 ≤ t) :
    2 * t / (2 + t) ≤ Real.log (1 + t) := by
  have hmain := nonneg_of_hasDerivAt_nonneg
    (f := fun y : ℝ => Real.log (1 + y) - 2 + 4 / (2 + y))
    (f' := fun y : ℝ => y ^ 2 / ((1 + y) * (2 + y) ^ 2)) (a := 0) (b := t + 1)
    (fun x hx => hasDerivAt_upperAux hx.1)
    (by norm_num)
    (fun x hx => by
      have hx0 : (0 : ℝ) < x := hx.1
      show (0 : ℝ) ≤ x ^ 2 / ((1 + x) * (2 + x) ^ 2)
      exact div_nonneg (sq_nonneg x) (mul_nonneg (by linarith) (sq_nonneg _)))
  have hval : (0 : ℝ) ≤ Real.log (1 + t) - 2 + 4 / (2 + t) := hmain t ⟨ht, by linarith⟩
  have h2 : (0 : ℝ) < 2 + t := by linarith
  have hEq : 2 * t / (2 + t) = 2 - 4 / (2 + t) := by field_simp; ring
  rw [hEq]
  linarith

/-- **Upper-tail log inequality.**  `t² / (2 + t) ≤ (1 + t) log (1 + t) - t` for `t ≥ 0`. -/
private theorem log_ineq_upper (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 / (2 + t) ≤ (1 + t) * Real.log (1 + t) - t := by
  have h2 : (0 : ℝ) < 2 + t := by linarith
  have hkey : (1 + t) * (2 * t / (2 + t)) ≤ (1 + t) * Real.log (1 + t) :=
    mul_le_mul_of_nonneg_left (log_lower_aux ht) (by linarith)
  have hval : (1 + t) * (2 * t / (2 + t)) - t = t ^ 2 / (2 + t) := by
    field_simp; ring
  linarith

/-- **Lower-tail log inequality.**  `t² / 2 ≤ (1 - t) log (1 - t) + t` for `0 ≤ t < 1`. -/
private theorem log_ineq_lower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t ^ 2 / 2 ≤ (1 - t) * Real.log (1 - t) + t := by
  have hmain := nonneg_of_hasDerivAt_nonneg
    (f := fun y : ℝ => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2)
    (f' := fun y : ℝ => -Real.log (1 - y) - y) (a := 0) (b := 1)
    (fun x hx => hasDerivAt_lowerAux hx.2)
    (by norm_num)
    (fun x hx => by
      have hpos : (0 : ℝ) < 1 - x := by linarith [hx.2]
      have := Real.log_le_sub_one_of_pos hpos
      show (0 : ℝ) ≤ -Real.log (1 - x) - x
      linarith)
  have hval : (0 : ℝ) ≤ (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2 := hmain t ⟨ht0, ht1⟩
  linarith

/-! ## The indicator count and its mean -/

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-- The number of coordinates of the block `s` that land in their success set. -/
def indicCount (s : Finset ι) (A : ι → Finset X) (ω : ι → X) : ℕ :=
  (s.filter fun j => ω j ∈ A j).card

/-- The mean of `indicCount`. -/
def indicMean (μ : ι → X → ℝ) (s : Finset ι) (A : ι → Finset X) : ℝ :=
  ∑ j ∈ s, ∑ x ∈ A j, μ j x

omit [Fintype ι] [DecidableEq ι] [Fintype X] in
/-- `indicCount` as a sum of `{0,1}`-indicators. -/
theorem indicCount_eq_sum (s : Finset ι) (A : ι → Finset X) (ω : ι → X) :
    (indicCount s A ω : ℝ) = ∑ j ∈ s, (if ω j ∈ A j then (1 : ℝ) else 0) := by
  rw [indicCount, Finset.card_filter]
  push_cast
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] in
/-- The mean of the indicator count is nonnegative. -/
theorem indicMean_nonneg (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (s : Finset ι) (A : ι → Finset X) : 0 ≤ indicMean μ s A :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun x _ => h0 j x

omit [Fintype ι] [DecidableEq ι] [DecidableEq X] in
/-- Each block coordinate's success probability is at most `1`. -/
theorem sum_success_le_one (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (A : ι → Finset X) (j : ι) :
    ∑ x ∈ A j, μ j x ≤ 1 := by
  rw [← h1 j]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun x _ _ => h0 j x

/-! ## Expectation and moment generating function -/

variable (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x) (h1 : ∀ j, ∑ x, μ j x = 1)

/-- **The mean of the indicator count.** -/
theorem Ex_indicCount (s : Finset ι) (A : ι → Finset X) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => (indicCount s A ω : ℝ))
      = indicMean μ s A := by
  have hfun : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => (indicCount s A ω : ℝ))
      = (prodSpace μ h0 h1).toFinProb.Ex
          (fun ω => ∑ j ∈ s, (if ω j ∈ A j then (1 : ℝ) else 0)) := by
    unfold FinProb.Ex
    exact Finset.sum_congr rfl fun ω _ => by dsimp only; rw [indicCount_eq_sum]
  rw [hfun, FinProb.Ex_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Ex_apply μ h0 h1 j (fun x => if x ∈ A j then (1 : ℝ) else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The moment generating function of the indicator count.**  Full independence
of the coordinates turns the expectation of a product into a product of
expectations, one honest factor `1 + (e^r - 1) q_j` per coordinate. -/
theorem mgf_indicCount (s : Finset ι) (A : ι → Finset X) (r : ℝ) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (r * indicCount s A ω))
      = ∏ j ∈ s, (1 + (Real.exp r - 1) * (∑ x ∈ A j, μ j x)) := by
  have hpt : ∀ ω : ι → X, Real.exp (r * indicCount s A ω)
      = ∏ j ∈ s, (if ω j ∈ A j then Real.exp r else 1) := by
    intro ω
    have hlin : r * (indicCount s A ω : ℝ) = ∑ j ∈ s, (if ω j ∈ A j then r else 0) := by
      rw [indicCount_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by split <;> ring
    rw [hlin, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by split <;> simp
  have hfun : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (r * indicCount s A ω))
      = ∏ j ∈ s, ∑ x, μ j x * (if x ∈ A j then Real.exp r else 1) := by
    refine Eq.trans ?_ (Ex_prod_apply μ h0 h1 s (fun j x => if x ∈ A j then Real.exp r else 1))
    unfold FinProb.Ex
    exact Finset.sum_congr rfl fun ω _ => by dsimp only; rw [hpt ω]
  rw [hfun]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hsplit : ∀ x : X, μ j x * (if x ∈ A j then Real.exp r else 1)
      = μ j x + (Real.exp r - 1) * (if x ∈ A j then μ j x else 0) := by
    intro x; split <;> ring
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib, h1 j,
    ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

/-! ## The exponential-moment (Chernoff) method -/

omit [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] in
/-- Factorwise `1 + y ≤ exp y` turns the moment generating function of the
indicator count into a single exponential. -/
private theorem prod_one_add_le_exp (s : Finset ι) (q : ι → ℝ) (r : ℝ)
    (hq0 : ∀ j ∈ s, 0 ≤ q j) (hq1 : ∀ j ∈ s, q j ≤ 1) :
    ∏ j ∈ s, (1 + (Real.exp r - 1) * q j) ≤ Real.exp ((Real.exp r - 1) * ∑ j ∈ s, q j) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
  · have ha : 0 ≤ q j := hq0 j hj
    have hb : q j ≤ 1 := hq1 j hj
    nlinarith [Real.exp_pos r, mul_nonneg ha (Real.exp_pos r).le]
  · linarith [Real.add_one_le_exp ((Real.exp r - 1) * q j)]

/-- **Markov's inequality applied to `exp (r · c)` for `r > 0`.** -/
private theorem markov_exp_upper (P : FinProb) (c : P.Ω → ℝ) {r a : ℝ} (hr : 0 < r) :
    P.Pr (univ.filter fun ω => a ≤ c ω)
      ≤ P.Ex (fun ω => Real.exp (r * c ω)) / Real.exp (r * a) := by
  have hsub : (univ.filter fun ω => a ≤ c ω)
      ⊆ (univ.filter fun ω => Real.exp (r * a) ≤ Real.exp (r * c ω)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω.2 hr.le)⟩
  refine le_trans (P.Pr_mono hsub) ?_
  exact P.markov (fun ω => Real.exp (r * c ω)) (fun ω => (Real.exp_pos _).le) (Real.exp_pos _)

/-- **Markov's inequality applied to `exp (r · c)` for `r < 0`.**  The event
direction flips because `r` is negative. -/
private theorem markov_exp_lower (P : FinProb) (c : P.Ω → ℝ) {r a : ℝ} (hr : r < 0) :
    P.Pr (univ.filter fun ω => c ω ≤ a)
      ≤ P.Ex (fun ω => Real.exp (r * c ω)) / Real.exp (r * a) := by
  have hsub : (univ.filter fun ω => c ω ≤ a)
      ⊆ (univ.filter fun ω => Real.exp (r * a) ≤ Real.exp (r * c ω)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hω.2 hr.le)⟩
  refine le_trans (P.Pr_mono hsub) ?_
  exact P.markov (fun ω => Real.exp (r * c ω)) (fun ω => (Real.exp_pos _).le) (Real.exp_pos _)

/-- The raw exponential tail bound for the upper tail, at an arbitrary `r > 0`. -/
private theorem chernoff_mgf_upper (s : Finset ι) (A : ι → Finset X) {r a : ℝ} (hr : 0 < r) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω => a ≤ (indicCount s A ω : ℝ))
      ≤ Real.exp ((Real.exp r - 1) * indicMean μ s A - r * a) := by
  have hmgf : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (r * indicCount s A ω))
      ≤ Real.exp ((Real.exp r - 1) * indicMean μ s A) := by
    rw [mgf_indicCount μ h0 h1 s A r]
    exact prod_one_add_le_exp s (fun j => ∑ x ∈ A j, μ j x) r
      (fun j _ => Finset.sum_nonneg fun x _ => h0 j x)
      (fun j _ => sum_success_le_one μ h0 h1 A j)
  refine le_trans (markov_exp_upper (prodSpace μ h0 h1).toFinProb
    (fun ω => (indicCount s A ω : ℝ)) hr) ?_
  rw [Real.exp_sub]
  exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).2 hmgf

/-- The raw exponential tail bound for the lower tail, at an arbitrary `r < 0`. -/
private theorem chernoff_mgf_lower (s : Finset ι) (A : ι → Finset X) {r a : ℝ} (hr : r < 0) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω => ((indicCount s A ω : ℝ)) ≤ a)
      ≤ Real.exp ((Real.exp r - 1) * indicMean μ s A - r * a) := by
  have hmgf : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (r * indicCount s A ω))
      ≤ Real.exp ((Real.exp r - 1) * indicMean μ s A) := by
    rw [mgf_indicCount μ h0 h1 s A r]
    exact prod_one_add_le_exp s (fun j => ∑ x ∈ A j, μ j x) r
      (fun j _ => Finset.sum_nonneg fun x _ => h0 j x)
      (fun j _ => sum_success_le_one μ h0 h1 A j)
  refine le_trans (markov_exp_lower (prodSpace μ h0 h1).toFinProb
    (fun ω => (indicCount s A ω : ℝ)) hr) ?_
  rw [Real.exp_sub]
  exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).2 hmgf

/-! ## The multiplicative Chernoff bounds -/

/-- **Multiplicative Chernoff bound, upper tail.** -/
theorem chernoff_upper (s : Finset ι) (A : ι → Finset X) {t : ℝ} (ht : 0 < t) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω => (1 + t) * indicMean μ s A ≤ (indicCount s A ω : ℝ))
      ≤ Real.exp (-(t ^ 2 * indicMean μ s A) / (2 + t)) := by
  have hm : 0 ≤ indicMean μ s A := indicMean_nonneg μ h0 s A
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hr : 0 < Real.log (1 + t) := Real.log_pos (by linarith)
  have hexp : Real.exp (Real.log (1 + t)) = 1 + t := Real.exp_log h1t
  refine le_trans (chernoff_mgf_upper μ h0 h1 s A (r := Real.log (1 + t))
    (a := (1 + t) * indicMean μ s A) hr) (Real.exp_le_exp.2 ?_)
  rw [hexp]
  have h2 : (0 : ℝ) < 2 + t := by linarith
  have hkey : indicMean μ s A * (t ^ 2 / (2 + t))
      ≤ indicMean μ s A * ((1 + t) * Real.log (1 + t) - t) :=
    mul_le_mul_of_nonneg_left (log_ineq_upper t ht.le) hm
  have hgoal : -(t ^ 2 * indicMean μ s A) / (2 + t)
      = -(indicMean μ s A * (t ^ 2 / (2 + t))) := by
    rw [neg_div, mul_comm (t ^ 2) (indicMean μ s A), mul_div_assoc]
  have hlhs : (1 + t - 1) * indicMean μ s A
        - Real.log (1 + t) * ((1 + t) * indicMean μ s A)
      = -(indicMean μ s A * ((1 + t) * Real.log (1 + t) - t)) := by ring
  rw [hgoal, hlhs]
  exact neg_le_neg hkey

/-- **Multiplicative Chernoff bound, lower tail.** -/
theorem chernoff_lower (s : Finset ι) (A : ι → Finset X) {t : ℝ} (ht : 0 < t) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω => ((indicCount s A ω : ℝ)) ≤ (1 - t) * indicMean μ s A)
      ≤ Real.exp (-(t ^ 2 * indicMean μ s A) / 2) := by
  have hm : 0 ≤ indicMean μ s A := indicMean_nonneg μ h0 s A
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have h1t : (0 : ℝ) < 1 - t := by linarith
    have hr : Real.log (1 - t) < 0 := Real.log_neg h1t (by linarith)
    have hexp : Real.exp (Real.log (1 - t)) = 1 - t := Real.exp_log h1t
    refine le_trans (chernoff_mgf_lower μ h0 h1 s A (r := Real.log (1 - t))
      (a := (1 - t) * indicMean μ s A) hr) (Real.exp_le_exp.2 ?_)
    rw [hexp]
    have hkey : indicMean μ s A * (t ^ 2 / 2)
        ≤ indicMean μ s A * ((1 - t) * Real.log (1 - t) + t) :=
      mul_le_mul_of_nonneg_left (log_ineq_lower t ht.le hlt) hm
    have hgoal : -(t ^ 2 * indicMean μ s A) / 2
        = -(indicMean μ s A * (t ^ 2 / 2)) := by ring
    have hlhs : (1 - t - 1) * indicMean μ s A
          - Real.log (1 - t) * ((1 - t) * indicMean μ s A)
        = -(indicMean μ s A * ((1 - t) * Real.log (1 - t) + t)) := by ring
    rw [hgoal, hlhs]
    exact neg_le_neg hkey
  · subst heq
    have hr : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    have hexp : Real.exp (Real.log (1 / 2 : ℝ)) = 1 / 2 := Real.exp_log (by norm_num)
    refine le_trans (chernoff_mgf_lower μ h0 h1 s A (r := Real.log (1 / 2 : ℝ))
      (a := (1 - 1) * indicMean μ s A) hr) (Real.exp_le_exp.2 ?_)
    rw [hexp]
    exact le_of_eq (by ring)
  · by_cases hm0 : indicMean μ s A = 0
    · rw [hm0]
      simp only [mul_zero, neg_zero, zero_div, Real.exp_zero]
      exact FinProb.Pr_le_one _ _
    · have hmpos : 0 < indicMean μ s A := lt_of_le_of_ne hm (Ne.symm hm0)
      have hempty : (univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
          ((indicCount s A ω : ℝ)) ≤ (1 - t) * indicMean μ s A) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ω _
        push Not
        exact lt_of_lt_of_le (mul_neg_of_neg_of_pos (by linarith) hmpos) (Nat.cast_nonneg _)
      rw [hempty, FinProb.Pr_empty]
      exact (Real.exp_pos _).le

/-- **Two-sided multiplicative Chernoff bound.** -/
theorem chernoff_two_sided (s : Finset ι) (A : ι → Finset X) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω =>
          t * indicMean μ s A < |(indicCount s A ω : ℝ) - indicMean μ s A|)
      ≤ 2 * Real.exp (-(t ^ 2 * indicMean μ s A) / 3) := by
  have hm : 0 ≤ indicMean μ s A := indicMean_nonneg μ h0 s A
  have hsub : (univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        t * indicMean μ s A < |(indicCount s A ω : ℝ) - indicMean μ s A|)
      ⊆ (univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            (1 + t) * indicMean μ s A ≤ (indicCount s A ω : ℝ))
        ∪ (univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            ((indicCount s A ω : ℝ)) ≤ (1 - t) * indicMean μ s A) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases lt_abs.1 hω.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, by linarith⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, by linarith⟩)
  have hX : 0 ≤ t ^ 2 * indicMean μ s A := by positivity
  have e1 : -(t ^ 2 * indicMean μ s A) / (2 + t)
      ≤ -(t ^ 2 * indicMean μ s A) / 3 := by
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have e2 : -(t ^ 2 * indicMean μ s A) / 2 ≤ -(t ^ 2 * indicMean μ s A) / 3 := by
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  calc (prodSpace μ h0 h1).toFinProb.Pr
        (univ.filter fun ω =>
          t * indicMean μ s A < |(indicCount s A ω : ℝ) - indicMean μ s A|)
      ≤ (prodSpace μ h0 h1).toFinProb.Pr _ := FinProb.Pr_mono _ hsub
    _ ≤ (prodSpace μ h0 h1).toFinProb.Pr
          (univ.filter fun ω => (1 + t) * indicMean μ s A ≤ (indicCount s A ω : ℝ))
        + (prodSpace μ h0 h1).toFinProb.Pr
          (univ.filter fun ω => ((indicCount s A ω : ℝ)) ≤ (1 - t) * indicMean μ s A) :=
        FinProb.Pr_union_le _ _ _
    _ ≤ Real.exp (-(t ^ 2 * indicMean μ s A) / (2 + t))
        + Real.exp (-(t ^ 2 * indicMean μ s A) / 2) :=
        add_le_add (chernoff_upper μ h0 h1 s A ht0) (chernoff_lower μ h0 h1 s A ht0)
    _ ≤ Real.exp (-(t ^ 2 * indicMean μ s A) / 3)
        + Real.exp (-(t ^ 2 * indicMean μ s A) / 3) :=
        add_le_add (Real.exp_le_exp.2 e1) (Real.exp_le_exp.2 e2)
    _ = 2 * Real.exp (-(t ^ 2 * indicMean μ s A) / 3) := by ring

end Arlib.Probability

