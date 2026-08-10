/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Robbins–Siegmund, and the scalar stochastic-approximation theorem

The **stochastic** half of stochastic approximation (the deterministic half is
`Arlib.Probability.RobbinsMonro`).

    Let `α_t, ε_t` be scalar random variables and `B ≥ 0` a constant such that,
    with probability 1, `E[ε_t ∣ F_t] = 0`, `E[ε_t² ∣ F_t] ≤ B`, `α_t ∈ [0,1]`,
    `∑_t α_t = ∞` and `∑_t α_t² < ∞`.  If `W_{t+1} = (1−α_t)W_t + α_t ε_t`,
    then `W_t → 0` almost surely.

Everything is stated over an arbitrary probability space with an arbitrary
filtration: `α`, `err` and `W` are unconstrained processes related only by the
recursion, so the theorem applies to any scalar stochastic-approximation scheme
(Q-learning, TD, Robbins–Monro root finding).

## Route

`V_t := W_t²` satisfies, because `α_t` is `F_t`-measurable and the cross term
kills itself against `E[ε_t ∣ F_t] = 0`,

    E[V_{t+1} ∣ F_t] = (1−α_t)²·V_t + α_t²·E[ε_t² ∣ F_t]
                     ≤ V_t − α_t(2−α_t)·V_t + α_t²·B.

That is a Robbins–Siegmund recursion with `c_t = α_t² B` (summable) and
`b_t = α_t(2−α_t)V_t ≥ α_t V_t`.  Robbins–Siegmund therefore gives **both**

* `V_t → V_∞` almost surely, and
* `∑_t α_t V_t < ∞` almost surely,

and `∑_t α_t = ∞` then forces `V_∞ = 0`, i.e. `W_t → 0`.

Robbins–Siegmund itself is not in Mathlib; it is obtained here from
`MeasureTheory.Submartingale.ae_tendsto_limitProcess` applied to the
nonnegative supermartingale `U_t := V_t + B·(C − ∑_{k<t} α_k²)`, whose
`L¹` bound is `E[U_0]`, together with the second nonnegative supermartingale
`M_t := U_t + ∑_{k<t} α_k V_k`.  The difference `M_t − U_t = ∑_{k<t} α_k V_k`
of two a.e.-convergent sequences is a.e. convergent, which is exactly the
second Robbins–Siegmund conclusion.

## Main statements

* `ae_exists_tendsto_of_nonneg_supermartingale` — **a nonnegative supermartingale
  converges a.e.**  Mathlib states the a.e. martingale convergence theorem only
  for `L¹`-bounded *sub*martingales; for a nonnegative supermartingale the `L¹`
  bound is free (`‖Z n‖₁ = E[Z n] ≤ E[Z 0]`), so this is the form one actually
  reaches for.
* `tendsto_zero_of_sa` — the stochastic-approximation theorem above.
-/
import Arlib.Probability.RobbinsMonro
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Arlib.Probability.StochApprox

open scoped BigOperators Topology
open Filter Finset MeasureTheory ProbabilityTheory

/-! ## A nonnegative supermartingale converges almost everywhere

`Mathlib` states the a.e. martingale convergence theorem for `L¹`-bounded
*sub*martingales.  For a *nonnegative* supermartingale `Z` the `L¹` bound is
free: `‖Z n‖₁ = E[Z n] ≤ E[Z 0]`, so the negation `-Z` is an `L¹`-bounded
submartingale and `Mathlib`'s theorem applies. -/
theorem ae_exists_tendsto_of_nonneg_supermartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hadp : Adapted ℱ Z) (hint : ∀ n, Integrable (Z n) μ)
    (hnn : ∀ n ω, 0 ≤ Z n ω)
    (hsup : ∀ n, μ[Z (n + 1)|ℱ n] ≤ᵐ[μ] Z n) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n => Z n ω) atTop (𝓝 L) := by
  have hS : Supermartingale Z ℱ μ := supermartingale_nat hadp hint hsup
  have hI : ∀ n, ∫ ω, Z n ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
    intro n
    have := hS.setIntegral_le (i := 0) (j := n) (Nat.zero_le n) (s := Set.univ)
      (@MeasurableSet.univ _ (ℱ 0))
    simpa using this
  have hnonneg0 : 0 ≤ ∫ ω, Z 0 ω ∂μ := integral_nonneg fun ω => hnn 0 ω
  set R : NNReal := ⟨∫ ω, Z 0 ω ∂μ, hnonneg0⟩ with hR
  have hbdd : ∀ n, eLpNorm ((-Z) n) 1 μ ≤ (R : ENNReal) := by
    intro n
    have h1 : eLpNorm ((-Z) n) 1 μ = ENNReal.ofReal (∫ ω, ‖Z n ω‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_nnnorm]
      simp only [Pi.neg_apply, nnnorm_neg]
      exact (ofReal_integral_norm_eq_lintegral_nnnorm (hint n)).symm
    have h2 : ∫ ω, ‖Z n ω‖ ∂μ = ∫ ω, Z n ω ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      exact Real.norm_of_nonneg (hnn n ω)
    have h3 : (R : ENNReal) = ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := by
      rw [hR, ENNReal.ofReal_eq_coe_nnreal hnonneg0]
    rw [h1, h2, h3]
    exact ENNReal.ofReal_le_ofReal (hI n)
  filter_upwards [hS.neg.ae_tendsto_limitProcess hbdd] with ω hω
  exact ⟨-(ℱ.limitProcess (-Z) μ ω), by simpa using hω.neg⟩

/-- **`lem:tsitsiklis`.**  The scalar stochastic-approximation recursion
`W_{t+1} = (1 − α_t)W_t + α_t ε_t` drives `W_t → 0` almost surely.

The uniform bound `hsq_bdd` on the partial sums `∑_{k<n} α_k²` is the effective
form of the paper's `∑_t α_t² < ∞`: it is what makes the Robbins–Siegmund
potential integrable.  (For the Q-learning application the step sizes lie in
`[0,1]`, so any summable envelope supplies it.) -/
theorem tendsto_zero_of_sa
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {α err W : ℕ → Ω → ℝ} {B C : ℝ}
    (hB : 0 ≤ B)
    (hW_adapted : Adapted ℱ W)
    (hα_adapted : Adapted ℱ α)
    (hα01 : ∀ n ω, α n ω ∈ Set.Icc (0 : ℝ) 1)
    (herr_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (err n))
    (hW_sq_int : ∀ n, Integrable (fun ω => (W n ω) ^ 2) μ)
    (herr_sq_int : ∀ n, Integrable (fun ω => (err n ω) ^ 2) μ)
    (hmean : ∀ n, μ[err n|ℱ n] =ᵐ[μ] 0)
    (hsecond : ∀ n, μ[(fun ω => (err n ω) ^ 2)|ℱ n] ≤ᵐ[μ] fun _ => B)
    (hrec : ∀ n ω, W (n + 1) ω = (1 - α n ω) * W n ω + α n ω * err n ω)
    (hsq_bdd : ∀ n ω, ∑ k ∈ range n, (α k ω) ^ 2 ≤ C)
    (hdiv : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ range n, α k ω) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => W n ω) atTop (𝓝 0) := by
  ---------------------------------------------------------------------------
  -- 0.  Measurability and integrability book-keeping.
  ---------------------------------------------------------------------------
  have hWm : ∀ n, StronglyMeasurable[m0] (W n) := fun n => (hW_adapted n).mono (ℱ.le n)
  have hαm : ∀ n, StronglyMeasurable[m0] (α n) := fun n => (hα_adapted n).mono (ℱ.le n)
  have herrm : ∀ n, StronglyMeasurable[m0] (err n) := fun n => (herr_meas n).mono (ℱ.le (n + 1))
  have herr_int : ∀ n, Integrable (err n) μ := by
    intro n
    refine Integrable.mono' (((herr_sq_int n).add (integrable_const (1 : ℝ))).const_mul (1 / 2))
      (herrm n).aestronglyMeasurable ?_
    filter_upwards with ω
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|err n ω| - 1), abs_nonneg (err n ω), sq_abs (err n ω)]
  have hcross_int : ∀ n, Integrable (fun ω => W n ω * err n ω) μ := by
    intro n
    refine Integrable.mono' ((hW_sq_int n).add (herr_sq_int n))
      ((hWm n).mul (herrm n)).aestronglyMeasurable ?_
    filter_upwards with ω
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|W n ω| - |err n ω|), abs_nonneg (W n ω), abs_nonneg (err n ω),
      sq_abs (W n ω), sq_abs (err n ω)]
  ---------------------------------------------------------------------------
  -- A.  The one-step conditional inequality.
  ---------------------------------------------------------------------------
  have hA : ∀ n, μ[(fun ω => (W (n + 1) ω) ^ 2)|ℱ n]
      ≤ᵐ[μ] fun ω => (W n ω) ^ 2 - α n ω * (W n ω) ^ 2 + (α n ω) ^ 2 * B := by
    intro n
    set c : Ω → ℝ := fun ω => 2 * (1 - α n ω) * (α n ω) * (W n ω) with hc
    set d : Ω → ℝ := fun ω => (α n ω) ^ 2 with hd
    set f1 : Ω → ℝ := fun ω => (1 - α n ω) ^ 2 * (W n ω) ^ 2 with hf1
    set e2 : Ω → ℝ := fun ω => (err n ω) ^ 2 with he2
    have hcm : StronglyMeasurable[ℱ n] c :=
      (((stronglyMeasurable_const.sub (hα_adapted n)).const_mul 2).mul (hα_adapted n)).mul
        (hW_adapted n)
    have hdm : StronglyMeasurable[ℱ n] d := (hα_adapted n).pow 2
    have hf1m : StronglyMeasurable[ℱ n] f1 :=
      ((stronglyMeasurable_const.sub (hα_adapted n)).pow 2).mul ((hW_adapted n).pow 2)
    have hf1i : Integrable f1 μ := by
      refine Integrable.mono' (hW_sq_int n) (hf1m.mono (ℱ.le n)).aestronglyMeasurable ?_
      filter_upwards with ω
      obtain ⟨h0, h1⟩ := hα01 n ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      have hb : (1 - α n ω) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (W n ω)]
    have hf2i : Integrable (c * err n) μ := by
      refine Integrable.mono' ((hcross_int n).norm.const_mul 2)
        ((hcm.mono (ℱ.le n)).mul (herrm n)).aestronglyMeasurable ?_
      filter_upwards with ω
      obtain ⟨h0, h1⟩ := hα01 n ω
      simp only [Pi.mul_apply, hc, Real.norm_eq_abs]
      have key : 2 * (1 - α n ω) * α n ω * W n ω * err n ω
          = 2 * (1 - α n ω) * α n ω * (W n ω * err n ω) := by ring
      rw [key, abs_mul, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 2 * (1 - α n ω) * α n ω)]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    have he2i : Integrable e2 μ := herr_sq_int n
    have hf3i : Integrable (d * e2) μ := by
      refine Integrable.mono' (herr_sq_int n)
        ((hdm.mono (ℱ.le n)).mul ((herrm n).pow 2)).aestronglyMeasurable ?_
      filter_upwards with ω
      obtain ⟨h0, h1⟩ := hα01 n ω
      simp only [Pi.mul_apply, hd, he2, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (α n ω)), abs_of_nonneg (sq_nonneg (err n ω))]
      have : α n ω ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (err n ω)]
    have heq : (fun ω => (W (n + 1) ω) ^ 2) = fun ω => f1 ω + (c * err n) ω + (d * e2) ω := by
      funext ω
      simp only [hf1, hc, hd, he2, Pi.mul_apply, hrec n ω]
      ring
    have hce : μ[(fun ω => (W (n + 1) ω) ^ 2)|ℱ n]
        =ᵐ[μ] fun ω => (μ[f1|ℱ n]) ω + (μ[c * err n|ℱ n]) ω + (μ[d * e2|ℱ n]) ω := by
      rw [heq]
      have h1 : (fun ω => f1 ω + (c * err n) ω + (d * e2) ω) = (f1 + c * err n) + d * e2 := rfl
      rw [h1]
      refine (condexp_add (hf1i.add hf2i) hf3i).trans ?_
      filter_upwards [condexp_add hf1i hf2i] with ω hω
      simp only [Pi.add_apply] at hω ⊢
      rw [hω]
    have h1 : μ[f1|ℱ n] =ᵐ[μ] f1 :=
      Filter.Eventually.of_forall
        fun ω => congrFun (condexp_of_stronglyMeasurable (ℱ.le n) hf1m hf1i) ω
    have h2 : μ[c * err n|ℱ n] =ᵐ[μ] c * μ[err n|ℱ n] :=
      condexp_stronglyMeasurable_mul hcm hf2i (herr_int n)
    have h3 : μ[d * e2|ℱ n] =ᵐ[μ] d * μ[e2|ℱ n] :=
      condexp_stronglyMeasurable_mul hdm hf3i he2i
    filter_upwards [hce, h1, h2, h3, hmean n, hsecond n] with ω hω hω1 hω2 hω3 hωm hωs
    rw [hω, hω1, hω2, hω3]
    simp only [Pi.mul_apply, Pi.zero_apply] at hωm ⊢
    rw [hωm, mul_zero, add_zero]
    obtain ⟨hα0, hα1⟩ := hα01 n ω
    have hle2 : d ω * (μ[e2|ℱ n]) ω ≤ α n ω ^ 2 * B := by
      simp only [hd]
      exact mul_le_mul_of_nonneg_left hωs (sq_nonneg _)
    have hf1le : f1 ω ≤ (W n ω) ^ 2 - α n ω * (W n ω) ^ 2 := by
      simp only [hf1]
      nlinarith [mul_nonneg (mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ 1 - α n ω)) (sq_nonneg (W n ω))]
    linarith
  -- the same inequality with an `ℱ n`-measurable integrable term added on
  have hAg : ∀ (n : ℕ) (g : Ω → ℝ), StronglyMeasurable[ℱ n] g → Integrable g μ →
      μ[(fun ω => (W (n + 1) ω) ^ 2 + g ω)|ℱ n]
        ≤ᵐ[μ] fun ω => ((W n ω) ^ 2 - α n ω * (W n ω) ^ 2 + (α n ω) ^ 2 * B) + g ω := by
    intro n g hgm hgi
    have hsum : (fun ω => (W (n + 1) ω) ^ 2 + g ω) = (fun ω => (W (n + 1) ω) ^ 2) + g := rfl
    rw [hsum]
    have hadd := condexp_add (m := ℱ n) (hW_sq_int (n + 1)) hgi
    have hg : μ[g|ℱ n] =ᵐ[μ] g :=
      Filter.Eventually.of_forall
        fun ω => congrFun (condexp_of_stronglyMeasurable (ℱ.le n) hgm hgi) ω
    filter_upwards [hadd, hg, hA n] with ω hω1 hω2 hω3
    simp only [Pi.add_apply] at hω1 ⊢
    rw [hω1, hω2]
    linarith
  ---------------------------------------------------------------------------
  -- B.  The two Robbins–Siegmund potentials.
  ---------------------------------------------------------------------------
  set U : ℕ → Ω → ℝ := fun n ω => (W n ω) ^ 2 + B * (C - ∑ k ∈ range n, (α k ω) ^ 2) with hU
  set Ssum : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ range n, α k ω * (W k ω) ^ 2 with hSs
  set M : ℕ → Ω → ℝ := fun n ω => U n ω + Ssum n ω with hM
  have hTnn : ∀ n ω, (0 : ℝ) ≤ ∑ k ∈ range n, (α k ω) ^ 2 := fun n ω =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  -- measurability of the pieces
  have hTm : ∀ n j, n ≤ j + 1 → StronglyMeasurable[ℱ j] (fun ω => ∑ k ∈ range n, (α k ω) ^ 2) := by
    intro n j hnj
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hnj)
    exact ((hα_adapted k).mono (ℱ.mono hkj)).pow 2
  have hSm : ∀ n j, n ≤ j + 1 → StronglyMeasurable[ℱ j] (Ssum n) := by
    intro n j hnj
    simp only [hSs]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hnj)
    exact ((hα_adapted k).mono (ℱ.mono hkj)).mul (((hW_adapted k).mono (ℱ.mono hkj)).pow 2)
  have hgm : ∀ n j, n ≤ j + 1 →
      StronglyMeasurable[ℱ j] (fun ω => B * (C - ∑ k ∈ range n, (α k ω) ^ 2)) := fun n j hnj =>
    (stronglyMeasurable_const.sub (hTm n j hnj)).const_mul B
  -- integrability of the pieces
  have hTint : ∀ n, Integrable (fun ω => B * (C - ∑ k ∈ range n, (α k ω) ^ 2)) μ := by
    intro n
    refine Integrable.mono' (integrable_const (B * C))
      ((hgm n n (Nat.le_succ n)).mono (ℱ.le n)).aestronglyMeasurable ?_
    filter_upwards with ω
    have h0 := hTnn n ω
    have h1 := hsq_bdd n ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hSint : ∀ n, Integrable (Ssum n) μ := by
    intro n
    simp only [hSs]
    refine integrable_finset_sum _ fun k _ => ?_
    refine Integrable.mono' (hW_sq_int k)
      ((hαm k).mul ((hWm k).pow 2)).aestronglyMeasurable ?_
    filter_upwards with ω
    obtain ⟨h0, h1⟩ := hα01 k ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (W k ω)]
  have hUint : ∀ n, Integrable (U n) μ := fun n => (hW_sq_int n).add (hTint n)
  have hMint : ∀ n, Integrable (M n) μ := fun n => (hUint n).add (hSint n)
  -- nonnegativity
  have hUnn : ∀ n ω, 0 ≤ U n ω := by
    intro n ω
    have h0 := hTnn n ω
    have h1 := hsq_bdd n ω
    simp only [hU]
    nlinarith [sq_nonneg (W n ω)]
  have hSnn : ∀ n ω, 0 ≤ Ssum n ω := fun n ω =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hα01 k ω).1 (sq_nonneg _)
  have hMnn : ∀ n ω, 0 ≤ M n ω := fun n ω => add_nonneg (hUnn n ω) (hSnn n ω)
  -- adaptedness
  have hUadp : Adapted ℱ U := by
    intro n
    exact ((hW_adapted n).pow 2).add (hgm n n (Nat.le_succ n))
  have hMadp : Adapted ℱ M := by
    intro n
    exact (hUadp n).add (hSm n n (Nat.le_succ n))
  -- the supermartingale inequalities
  have hUsuper : ∀ n, μ[U (n + 1)|ℱ n] ≤ᵐ[μ] U n := by
    intro n
    have hUeq : U (n + 1)
        = fun ω => (W (n + 1) ω) ^ 2
          + (fun ω => B * (C - ∑ k ∈ range (n + 1), (α k ω) ^ 2)) ω := rfl
    rw [hUeq]
    filter_upwards [hAg n _ (hgm (n + 1) n le_rfl) (hTint (n + 1))] with ω hω
    refine hω.trans ?_
    simp only [hU, Finset.sum_range_succ]
    obtain ⟨h0, h1⟩ := hα01 n ω
    nlinarith [mul_nonneg h0 (sq_nonneg (W n ω))]
  have hMsuper : ∀ n, μ[M (n + 1)|ℱ n] ≤ᵐ[μ] M n := by
    intro n
    have hgm' : StronglyMeasurable[ℱ n]
        (fun ω => B * (C - ∑ k ∈ range (n + 1), (α k ω) ^ 2) + Ssum (n + 1) ω) :=
      (hgm (n + 1) n le_rfl).add (hSm (n + 1) n le_rfl)
    have hgi' : Integrable
        (fun ω => B * (C - ∑ k ∈ range (n + 1), (α k ω) ^ 2) + Ssum (n + 1) ω) μ :=
      (hTint (n + 1)).add (hSint (n + 1))
    have hMeq : M (n + 1)
        = fun ω => (W (n + 1) ω) ^ 2
          + (fun ω => B * (C - ∑ k ∈ range (n + 1), (α k ω) ^ 2) + Ssum (n + 1) ω) ω := by
      funext ω; simp only [hM, hU]; ring
    rw [hMeq]
    filter_upwards [hAg n _ hgm' hgi'] with ω hω
    refine hω.trans ?_
    simp only [hM, hU, hSs, Finset.sum_range_succ]
    linarith
  have hUconv := ae_exists_tendsto_of_nonneg_supermartingale hUadp hUint hUnn hUsuper
  have hMconv := ae_exists_tendsto_of_nonneg_supermartingale hMadp hMint hMnn hMsuper
  ---------------------------------------------------------------------------
  -- C/D.  Pathwise: `V n → L`, `∑ α_k V_k < ∞`, `∑ α_k = ∞`, hence `L = 0`.
  ---------------------------------------------------------------------------
  filter_upwards [hUconv, hMconv, hdiv] with ω hu hm hd
  obtain ⟨Lu, hLu⟩ := hu
  obtain ⟨Lm, hLm⟩ := hm
  -- the partial sums of `α²` converge: monotone and bounded above by `C`
  have hTmono : Monotone fun n => ∑ k ∈ range n, (α k ω) ^ 2 := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    nlinarith [sq_nonneg (α n ω)]
  have hTbdd : BddAbove (Set.range fun n => ∑ k ∈ range n, (α k ω) ^ 2) := by
    refine ⟨C, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hsq_bdd n ω
  have hT := tendsto_atTop_ciSup hTmono hTbdd
  set T : ℝ := ⨆ n, ∑ k ∈ range n, (α k ω) ^ 2 with hTdef
  -- hence `V n = W n ^ 2` converges
  have hV : Tendsto (fun n => (W n ω) ^ 2) atTop (𝓝 (Lu - B * (C - T))) := by
    refine (hLu.sub ((tendsto_const_nhds.sub hT).const_mul B)).congr fun n => ?_
    simp only [hU]; ring
  -- and the partial sums `∑_{k<n} α_k V_k = M n - U n` converge
  have hSlim : Tendsto (fun n => Ssum n ω) atTop (𝓝 (Lm - Lu)) := by
    refine (hLm.sub hLu).congr fun n => ?_
    simp only [hM]; ring
  set L : ℝ := Lu - B * (C - T) with hLdef
  have hL0 : L = 0 := by
    by_contra hne
    have hLnn : 0 ≤ L := ge_of_tendsto' hV fun n => sq_nonneg _
    have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hne)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hV.eventually (lt_mem_nhds (show L / 2 < L by linarith)))
    have hSge : ∀ n, N ≤ n →
        Ssum N ω + (L / 2) * ((∑ k ∈ range n, α k ω) - ∑ k ∈ range N, α k ω) ≤ Ssum n ω := by
      intro n hn
      have e1 : (∑ k ∈ range N, α k ω * (W k ω) ^ 2)
          + ∑ k ∈ Ico N n, α k ω * (W k ω) ^ 2 = ∑ k ∈ range n, α k ω * (W k ω) ^ 2 :=
        Finset.sum_range_add_sum_Ico _ hn
      have e2 : (∑ k ∈ range N, α k ω) + ∑ k ∈ Ico N n, α k ω = ∑ k ∈ range n, α k ω :=
        Finset.sum_range_add_sum_Ico _ hn
      have e3 : (L / 2) * (∑ k ∈ Ico N n, α k ω) ≤ ∑ k ∈ Ico N n, α k ω * (W k ω) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : N ≤ k := (Finset.mem_Ico.mp hk).1
        have hak := (hα01 k ω).1
        nlinarith [hN k hk']
      have e4 : (∑ k ∈ range n, α k ω) - ∑ k ∈ range N, α k ω = ∑ k ∈ Ico N n, α k ω := by
        linarith
      simp only [hSs]
      rw [e4]
      linarith
    have hdiv2 : Tendsto (fun n => Ssum N ω
        + (L / 2) * ((∑ k ∈ range n, α k ω) - ∑ k ∈ range N, α k ω)) atTop atTop := by
      refine Filter.tendsto_atTop_add_const_left _ _ ?_
      refine Filter.Tendsto.const_mul_atTop (by linarith) ?_
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right atTop (-(∑ k ∈ range N, α k ω)) hd
    have hStop : Tendsto (fun n => Ssum n ω) atTop atTop :=
      Filter.tendsto_atTop_mono' atTop (Filter.eventually_atTop.mpr ⟨N, hSge⟩) hdiv2
    exact not_tendsto_nhds_of_tendsto_atTop hStop _ hSlim
  have hV0 : Tendsto (fun n => (W n ω) ^ 2) atTop (𝓝 0) := hL0 ▸ hV
  have habs := (Real.continuous_sqrt.tendsto 0).comp hV0
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

end Arlib.Probability.StochApprox
