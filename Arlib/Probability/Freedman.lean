/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A finite Bernstein / Freedman inequality for martingale differences

This file proves, from first principles over `Arlib`'s finite probability model,
an exponential (Bernstein/Freedman-type) tail bound for a sum of **bounded,
conditionally mean-zero** increments over a product space — a finite martingale
difference sequence.

Two levels of generality are provided.

* **Independent (coordinatewise) increments.**  The martingale is realised
  concretely as `ξ k ω = f k (ω k)` over the independent product
  `Arlib.prodSpace`, so the mean-zero and predictable-variance hypotheses become
  the per-coordinate identities `∑_x μ_k x · f k x = 0` and
  `v_k = ∑_x μ_k x · (f k x)²`, and the exponential super-martingale step is the
  product-space factorization `Arlib.Ex_prod_apply`.
* **Previsible increments.**  The increment `Φ m p x` may depend on the whole
  length-`m` past prefix `p` and is only *conditionally* mean-zero.  This is a
  genuine martingale difference sequence and is what applications with
  history-dependent step sizes need.

The main results are `freedman_tail` (independent) and `freedman_tail_prev`
(previsible): with per-step bound `b`, total predictable variance `V` and
deviation `lam` in the sub-Gaussian regime `b · lam ≤ V`,

  `Pr[lam ≤ |∑ₖ ξ k|] ≤ 2 · exp (-3 · lam² / (8 · V))`.

Nothing comparable exists in Mathlib v4.15; the closest tool in this library,
`Arlib.Chernoff`, handles only `{0,1}`-indicators.  Everything below is
`sorry`-free.

## Main definitions

* `Arlib.prefixOf k ω` — the length-`k` prefix `(ω 0, …, ω (k-1))` of `ω`.
* `Arlib.previsibleSum Φ ω` — the previsible sum `∑ₖ Φ k (prefixOf k ω) (ω k)`.

## Main results

* `Arlib.exp_quad_bound` — the pointwise majorant `exp x ≤ 1 + x + (2/3)x²` on
  `|x| ≤ 3/4`.
* `Arlib.freedman_tail` / `Arlib.freedman_tail_upper` — the two-sided / one-sided
  tail for independent coordinatewise increments.
* `Arlib.freedman_tail_prev` / `Arlib.freedman_tail_upper_prev` — the same for
  previsible increments.
-/
import Arlib.Probability.IIDProduct
import Arlib.Probability.Chernoff
import Mathlib.Data.Complex.Exponential

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## The pointwise exponential inequality -/

/-- **The Bernstein pointwise bound.**  For `|x| ≤ 3/4`,
`exp x ≤ 1 + x + (2/3)·x²`.  This is the sharp quadratic majorant on the range
`[-3/4, 3/4]`: it comes from the degree-2 Taylor bound
`|exp x - (1 + x + x²/2)| ≤ (2/9)|x|³` (`Real.exp_bound` at `n = 3`) together
with `(2/9)|x|³ ≤ (1/6)x²` for `|x| ≤ 3/4`.  The constant `2/3` is exactly what
makes the optimized tail below come out as `exp (-3λ²/(8V))`. -/
theorem exp_quad_bound {x : ℝ} (hx : |x| ≤ 3 / 4) :
    Real.exp x ≤ 1 + x + (2 / 3) * x ^ 2 := by
  have hx1 : |x| ≤ 1 := le_trans hx (by norm_num)
  have hb := Real.exp_bound (x := x) hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  -- `hb : |Real.exp x - (1 + x + x^2/2)| ≤ |x|^3 * (2/9)` (up to normalization)
  have hupper : Real.exp x - (1 + x + x ^ 2 / 2) ≤ |x| ^ 3 * (2 / 9) := by
    have := (abs_le.1 hb).2
    nlinarith [this]
  have key : |x| ^ 3 * (2 / 9) ≤ (1 / 6) * x ^ 2 := by
    have h1 : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs]; ring
    rw [h1]
    have hprod : 0 ≤ x ^ 2 * (1 / 6 - (2 / 9) * |x|) :=
      mul_nonneg (sq_nonneg x) (by linarith [hx])
    nlinarith [hprod, abs_nonneg x, sq_nonneg x]
  linarith [hupper, key]

/-! ## Part 1 — the exponential super-martingale step

We model the martingale over the independent product space `Arlib.prodSpace μ`,
with coordinatewise increments `ξ k ω = f k (ω k)`.  The conditional-mean-zero
property `E[ξ k | past] = 0` becomes the per-coordinate identity
`∑_x μ_k x · f k x = 0`, and the predictable variance is
`v_k = ∑_x μ_k x · (f k x)²`.  The exponential super-martingale step is obtained
by the product-space factorization `Arlib.Ex_prod_apply` (which peels every
coordinate at once, the fully-independent analogue of the tower-property
induction), one honest factor per coordinate. -/

variable {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]

set_option linter.unusedSectionVars false in
/-- **Per-coordinate exponential moment bound.**  For a bounded, mean-zero
increment `f k` with `|θ · f k x| ≤ 3/4`, its exponential moment is dominated by
`exp((2/3)·θ²·v_k)`, where `v_k = ∑_x μ_k x · (f k x)²` is the predictable
variance.  This is `exp_quad_bound` averaged against `μ_k`, using mean-zero to
kill the linear term and `1 + y ≤ exp y` to close. -/
theorem coordMGF_le (μ : Fin n → X → ℝ) (h0 : ∀ k x, 0 ≤ μ k x)
    (h1 : ∀ k, ∑ x, μ k x = 1) (f : Fin n → X → ℝ) (θ : ℝ) (k : Fin n)
    (hc : ∀ x, |θ * f k x| ≤ 3 / 4) (hmz : ∑ x, μ k x * f k x = 0) :
    (∑ x, μ k x * Real.exp (θ * f k x))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2)) := by
  have step : ∀ x, μ k x * Real.exp (θ * f k x)
      ≤ μ k x * (1 + θ * f k x + (2 / 3) * (θ * f k x) ^ 2) := fun x =>
    mul_le_mul_of_nonneg_left (exp_quad_bound (hc x)) (h0 k x)
  have hmid : (∑ x, μ k x * (1 + θ * f k x + (2 / 3) * (θ * f k x) ^ 2))
      = 1 + (2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2) := by
    have expand : ∀ x, μ k x * (1 + θ * f k x + (2 / 3) * (θ * f k x) ^ 2)
        = μ k x + θ * (μ k x * f k x) + (2 / 3) * θ ^ 2 * (μ k x * (f k x) ^ 2) := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => expand x)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      h1 k, hmz]
    ring
  calc (∑ x, μ k x * Real.exp (θ * f k x))
      ≤ ∑ x, μ k x * (1 + θ * f k x + (2 / 3) * (θ * f k x) ^ 2) :=
        Finset.sum_le_sum (fun x _ => step x)
    _ = 1 + (2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2) := hmid
    _ ≤ Real.exp ((2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2)) := by
        linarith [Real.add_one_le_exp ((2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2))]

/-- **The exponential super-martingale bound for the whole sum.**  Peeling every
coordinate at once via the product-space factorization `Arlib.Ex_prod_apply`,
the exponential moment of the martingale `∑_k f k (ω k)` is dominated by
`exp((2/3)·θ²·V)`, where `V` bounds the total predictable variance
`∑_k v_k`.  This is the exponential super-martingale step of Freedman's method. -/
theorem sumMGF_le (μ : Fin n → X → ℝ) (h0 : ∀ k x, 0 ≤ μ k x)
    (h1 : ∀ k, ∑ x, μ k x = 1) (f : Fin n → X → ℝ) (θ V : ℝ)
    (hc : ∀ k x, |θ * f k x| ≤ 3 / 4) (hmz : ∀ k, ∑ x, μ k x * f k x = 0)
    (hV : (∑ k, ∑ x, μ k x * (f k x) ^ 2) ≤ V) :
    (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (θ * ∑ k, f k (ω k)))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * V) := by
  have hpt : ∀ ω : ∀ _ : Fin n, X,
      Real.exp (θ * ∑ k, f k (ω k)) = ∏ k, Real.exp (θ * f k (ω k)) := by
    intro ω; rw [Finset.mul_sum, Real.exp_sum]
  have hfact : (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (θ * ∑ k, f k (ω k)))
      = ∏ k, ∑ x, μ k x * Real.exp (θ * f k x) := by
    refine Eq.trans ?_ (Ex_prod_apply μ h0 h1 Finset.univ (fun k x => Real.exp (θ * f k x)))
    unfold FinProb.Ex
    exact Finset.sum_congr rfl (fun ω _ => by dsimp only; rw [hpt ω])
  rw [hfact]
  have hprod : (∏ k, ∑ x, μ k x * Real.exp (θ * f k x))
      ≤ ∏ k, Real.exp ((2 / 3) * θ ^ 2 * (∑ x, μ k x * (f k x) ^ 2)) := by
    apply Finset.prod_le_prod
    · intro k _
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (h0 k x) (Real.exp_pos _).le)
    · intro k _
      exact coordMGF_le μ h0 h1 f θ k (hc k) (hmz k)
  refine le_trans hprod ?_
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.2
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hV (by positivity)

/-! ## Part 2 — the exponential Markov inequality and the tail bound -/

/-- **Exponential Markov inequality.**  For `θ > 0`,
`Pr[a ≤ c] ≤ E[exp(θ·c)]/exp(θ·a)`.  (This is the `markov_exp_upper` step of
`Arlib.Chernoff`, which is `private` there, reproven for reuse.) -/
theorem pr_le_exp_mgf (P : Arlib.Probability.FinProb) (c : P.Ω → ℝ) {θ a : ℝ} (hθ : 0 < θ) :
    P.Pr (Finset.univ.filter fun ω => a ≤ c ω)
      ≤ P.Ex (fun ω => Real.exp (θ * c ω)) / Real.exp (θ * a) := by
  have hsub : (Finset.univ.filter fun ω => a ≤ c ω)
      ⊆ (Finset.univ.filter fun ω => Real.exp (θ * a) ≤ Real.exp (θ * c ω)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω.2 hθ.le)⟩
  refine le_trans (P.Pr_mono hsub) ?_
  exact P.markov (fun ω => Real.exp (θ * c ω)) (fun ω => (Real.exp_pos _).le) (Real.exp_pos _)

/-- **The raw one-sided tail at an arbitrary `θ > 0`.**  Combining the
exponential Markov inequality with the super-martingale bound `sumMGF_le`. -/
theorem tail_raw (μ : Fin n → X → ℝ) (h0 : ∀ k x, 0 ≤ μ k x)
    (h1 : ∀ k, ∑ x, μ k x = 1) (f : Fin n → X → ℝ) (θ V lam : ℝ) (hθ : 0 < θ)
    (hc : ∀ k x, |θ * f k x| ≤ 3 / 4) (hmz : ∀ k, ∑ x, μ k x * f k x = 0)
    (hV : (∑ k, ∑ x, μ k x * (f k x) ^ 2) ≤ V) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => lam ≤ ∑ k, f k (ω k))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := by
  have hmk := pr_le_exp_mgf (prodSpace μ h0 h1).toFinProb
    (fun ω => ∑ k, f k (ω k)) (a := lam) hθ
  have hmgf := sumMGF_le μ h0 h1 f θ V hc hmz hV
  calc (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω => lam ≤ ∑ k, f k (ω k))
      ≤ (prodSpace μ h0 h1).toFinProb.Ex (fun ω => Real.exp (θ * ∑ k, f k (ω k)))
          / Real.exp (θ * lam) := hmk
    _ ≤ Real.exp ((2 / 3) * θ ^ 2 * V) / Real.exp (θ * lam) :=
        (div_le_div_iff_of_pos_right (Real.exp_pos _)).2 hmgf
    _ = Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := (Real.exp_sub _ _).symm

/-- **One-sided Freedman/Bernstein tail (optimized).**  For bounded
(`|f k x| ≤ b`), conditionally mean-zero coordinatewise increments with total
predictable variance `≤ V`, in the sub-Gaussian regime `b·λ ≤ V`,
`Pr[λ ≤ ∑_k f k (ω k)] ≤ exp(-3λ²/(8V))`.  Obtained from `tail_raw` at the
optimal `θ = 3λ/(4V)` (which satisfies `θ·b ≤ 3/4` exactly when `b·λ ≤ V`). -/
theorem freedman_tail_upper (μ : Fin n → X → ℝ) (h0 : ∀ k x, 0 ≤ μ k x)
    (h1 : ∀ k, ∑ x, μ k x = 1) (f : Fin n → X → ℝ) (b V lam : ℝ)
    (hb : ∀ k x, |f k x| ≤ b) (hmz : ∀ k, ∑ x, μ k x * f k x = 0)
    (hVvar : (∑ k, ∑ x, μ k x * (f k x) ^ 2) ≤ V)
    (hV : 0 < V) (hbl : b * lam ≤ V) (hlam : 0 ≤ lam) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => lam ≤ ∑ k, f k (ω k))
      ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · rw [← hlam0, show (-3 * (0 : ℝ) ^ 2 / (8 * V)) = 0 by ring, Real.exp_zero]
    exact FinProb.Pr_le_one _ _
  · set θ := 3 * lam / (4 * V) with hθdef
    have hθ : 0 < θ := by rw [hθdef]; positivity
    have hθb : θ * b ≤ 3 / 4 := by
      rw [hθdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hbl]
    have hc : ∀ k x, |θ * f k x| ≤ 3 / 4 := by
      intro k x
      rw [abs_mul, abs_of_pos hθ]
      calc θ * |f k x| ≤ θ * b := mul_le_mul_of_nonneg_left (hb k x) hθ.le
        _ ≤ 3 / 4 := hθb
    have hraw := tail_raw μ h0 h1 f θ V lam hθ hc hmz hVvar
    have hexp : (2 / 3) * θ ^ 2 * V - θ * lam = -3 * lam ^ 2 / (8 * V) := by
      rw [hθdef]; field_simp; ring
    rwa [hexp] at hraw

/-- **Two-sided Freedman/Bernstein tail.**  Applying `freedman_tail_upper` to the
increments `f` and to their negation `-f` (which share the same bound, mean-zero
property and predictable variance), and combining with a union bound:
`Pr[λ ≤ |∑_k f k (ω k)|] ≤ 2·exp(-3λ²/(8V))`. -/
theorem freedman_tail (μ : Fin n → X → ℝ) (h0 : ∀ k x, 0 ≤ μ k x)
    (h1 : ∀ k, ∑ x, μ k x = 1) (f : Fin n → X → ℝ) (b V lam : ℝ)
    (hb : ∀ k x, |f k x| ≤ b) (hmz : ∀ k, ∑ x, μ k x * f k x = 0)
    (hVvar : (∑ k, ∑ x, μ k x * (f k x) ^ 2) ≤ V)
    (hV : 0 < V) (hbl : b * lam ≤ V) (hlam : 0 ≤ lam) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => lam ≤ |∑ k, f k (ω k)|)
      ≤ 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  have hup := freedman_tail_upper μ h0 h1 f b V lam hb hmz hVvar hV hbl hlam
  -- the negated increments satisfy the same hypotheses
  have hb' : ∀ k x, |(-(f k x))| ≤ b := fun k x => by rw [abs_neg]; exact hb k x
  have hmz' : ∀ k, ∑ x, μ k x * (-(f k x)) = 0 := fun k => by
    simp only [mul_neg, Finset.sum_neg_distrib, hmz k, neg_zero]
  have hVvar' : (∑ k, ∑ x, μ k x * (-(f k x)) ^ 2) ≤ V := by
    simp only [neg_sq]; exact hVvar
  have hlo0 := freedman_tail_upper μ h0 h1 (fun k x => -(f k x)) b V lam hb' hmz' hVvar' hV hbl hlam
  -- the lower-tail event, rewritten from the negated sum
  have hgsum : ∀ ω : Fin n → X,
      (∑ k, (fun k x => -(f k x)) k (ω k)) = -(∑ k, f k (ω k)) := fun ω => by
    simp only [Finset.sum_neg_distrib]
  have hsub : (Finset.univ.filter fun ω : Fin n → X => lam ≤ |∑ k, f k (ω k)|)
      ⊆ (Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, f k (ω k))
        ∪ (Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, (fun k x => -(f k x)) k (ω k)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases le_abs.1 hω.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, ?_⟩)
      rw [hgsum ω]; exact h
  calc (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : Fin n → X => lam ≤ |∑ k, f k (ω k)|)
      ≤ (prodSpace μ h0 h1).toFinProb.Pr
          ((Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, f k (ω k))
          ∪ (Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, (fun k x => -(f k x)) k (ω k))) :=
        (prodSpace μ h0 h1).toFinProb.Pr_mono hsub
    _ ≤ (prodSpace μ h0 h1).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, f k (ω k))
          + (prodSpace μ h0 h1).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X => lam ≤ ∑ k, (fun k x => -(f k x)) k (ω k)) :=
        (prodSpace μ h0 h1).toFinProb.Pr_union_le _ _
    _ ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) + Real.exp (-3 * lam ^ 2 / (8 * V)) :=
        add_le_add hup hlo0
    _ = 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by ring

/-! ## Part 3 — the PREVISIBLE (genuine martingale) generalization

The independent versions above require *unconditional* per-coordinate mean-zero.
In a typical streaming application the increment
`ξ_k = (1/ρ_k)·𝟙[κ_{s_k} ≤ ρ_k] − 1` has a sampling rate `ρ_k` that depends on
the earlier draws `κ_{<k}`, so `ξ_k = φ_k(ω_{<k}, ω_k)` is **previsible** and
mean-zero only *conditionally on the past*.  We now cover this.

We use two *global* families, so that nothing needs "restriction" as the number
of coordinates changes under the induction:
* `ν : ℕ → X → ℝ` — the coin law at each step;
* `Φ : ∀ m, (Fin m → X) → X → ℝ` — the increment given the length-`m` prefix and
  the current coordinate.

For `ω : Fin n → X`, the `k`-th increment is `Φ k.val (prefixOf k ω) (ω k)`, where
`prefixOf k ω` is the prefix `(ω 0, …, ω (k-1))`.  The hypotheses are the honest
*conditional* martingale-difference conditions: for every prefix `p`,
`∑_x ν m x · Φ m p x = 0` (conditional mean-zero), `|Φ m p x| ≤ b`, and
`∑_x ν m x · (Φ m p x)² ≤ vf m`. -/

/-- **Single-distribution exponential moment bound** — the `k = 0`, `n = 1`
instance of `coordMGF_le`, extracted so the previsible induction can apply it at
each fixed prefix. -/
theorem mgf_single (ρ ψ : X → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) (θ : ℝ)
    (hc : ∀ x, |θ * ψ x| ≤ 3 / 4) (hmz : ∑ x, ρ x * ψ x = 0) :
    (∑ x, ρ x * Real.exp (θ * ψ x))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * (∑ x, ρ x * (ψ x) ^ 2)) := by
  have h := coordMGF_le (n := 1) (fun _ => ρ) (fun _ x => hρ0 x) (fun _ => hρ1)
    (fun _ => ψ) θ 0 (fun x => hc x) hmz
  simpa using h

/-- The length-`k` prefix `(ω 0, …, ω (k-1))` of an outcome `ω : Fin n → X`. -/
def prefixOf {n : ℕ} (k : Fin n) (ω : Fin n → X) : Fin k.val → X :=
  fun i => ω (Fin.castLE k.isLt.le i)

/-- The previsible martingale sum `∑_{k} Φ k.val (prefix) (ω k)`. -/
def previsibleSum {n : ℕ} (Φ : ∀ m, (Fin m → X) → X → ℝ) (ω : Fin n → X) : ℝ :=
  ∑ k : Fin n, Φ k.val (prefixOf k ω) (ω k)

set_option linter.unusedSectionVars false in
/-- Appending a coordinate does not change the prefix at an interior index. -/
theorem prefixOf_castSucc_snoc {n : ℕ} (k : Fin n) (ω' : Fin n → X) (y : X) :
    prefixOf (k.castSucc) (Fin.snoc ω' y) = prefixOf k ω' := by
  funext i
  simp only [prefixOf]
  rw [show (Fin.castLE (k.castSucc).isLt.le i : Fin (n + 1))
        = Fin.castSucc (Fin.castLE k.isLt.le i) from Fin.ext rfl, Fin.snoc_castSucc]

set_option linter.unusedSectionVars false in
/-- The full prefix at the last index recovers the appended tuple. -/
theorem prefixOf_last_snoc {n : ℕ} (ω' : Fin n → X) (y : X) :
    prefixOf (Fin.last n) (Fin.snoc ω' y) = ω' := by
  funext i
  simp only [prefixOf]
  rw [show (Fin.castLE (Fin.last n).isLt.le i : Fin (n + 1)) = Fin.castSucc i from Fin.ext rfl,
    Fin.snoc_castSucc]

set_option linter.unusedSectionVars false in
/-- **Peeling the last coordinate of the previsible sum.**
`previsibleSum Φ (snoc ω' y) = previsibleSum Φ ω' + Φ n ω' y`. -/
theorem previsibleSum_snoc {n : ℕ} (Φ : ∀ m, (Fin m → X) → X → ℝ) (ω' : Fin n → X) (y : X) :
    previsibleSum Φ (Fin.snoc ω' y) = previsibleSum Φ ω' + Φ n ω' y := by
  unfold previsibleSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [prefixOf_castSucc_snoc, Fin.snoc_castSucc]
    rfl
  · rw [prefixOf_last_snoc, Fin.snoc_last]
    rfl

/-- **Peeling the last coordinate of a `prodSpace` expectation.**
`E_{Fin (n+1)}[F] = E_{Fin n}[ω' ↦ ∑_y ν n y · F (snoc ω' y)]`.  The product mass
`∏_{k} ν k.val (ω k)` splits as `(∏_{k<n} ν k.val (ω' k))·ν n y` under
`ω = snoc ω' y`, and summing over the `Fin.snocEquiv` decomposition
`(Fin (n+1) → X) ≃ X × (Fin n → X)` factors the last coordinate out. -/
theorem Ex_snoc (n : ℕ) (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x) (hν1 : ∀ m, ∑ x, ν m x = 1)
    (F : (Fin (n + 1) → X) → ℝ) :
    (prodSpace (fun k : Fin (n + 1) => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Ex F
      = (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Ex
          (fun ω' => ∑ y, ν n y * F (Fin.snoc ω' y)) := by
  have hprod : ∀ (ω' : Fin n → X) (y : X),
      (∏ k : Fin (n + 1), ν (k : ℕ) ((Fin.snoc ω' y : Fin (n + 1) → X) k))
        = (∏ k : Fin n, ν (k : ℕ) (ω' k)) * ν n y := by
    intro ω' y
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  have key : (∑ ω : Fin (n + 1) → X, (∏ k : Fin (n + 1), ν (k : ℕ) (ω k)) * F ω)
      = ∑ ω' : Fin n → X,
          (∏ k : Fin n, ν (k : ℕ) (ω' k)) * (∑ y, ν n y * F (Fin.snoc ω' y)) := by
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => X))
          (fun ω : Fin (n + 1) → X => (∏ k : Fin (n + 1), ν (k : ℕ) (ω k)) * F ω),
      Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have he : (Fin.snocEquiv (fun _ : Fin (n + 1) => X)) (y, ω') = Fin.snoc ω' y := rfl
    rw [he]
    rw [hprod ω' y]
    ring
  simp only [FinProb.Ex, prodSpace_mass]
  exact key

/-- **The previsible exponential super-martingale step (exact form).**  By
induction on `n`, peeling the last coordinate with `Ex_snoc`: the inner factor
`∑_y ν n y · exp(θ·Φ n prefix y) ≤ exp((2/3)θ²·(cond. variance))` is bounded at
each fixed prefix by `mgf_single` (conditional mean-zero + bound), and the
remaining `∑_{k<n}` part is handled by the induction hypothesis. -/
theorem sumMGF_prev_exact (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (θ : ℝ) (vf : ℕ → ℝ)
    (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0) (hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Ex (fun ω : Fin n → X => Real.exp (θ * previsibleSum Φ ω))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * (∑ k : Fin n, vf k.val)) := by
  induction n with
  | zero =>
    have h1 : (prodSpace (fun k : Fin 0 => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Ex (fun ω : Fin 0 → X => Real.exp (θ * previsibleSum Φ ω)) = 1 := by
      rw [show (fun ω : Fin 0 → X => Real.exp (θ * previsibleSum Φ ω)) = (fun _ => (1 : ℝ)) by
            funext ω; simp [previsibleSum]]
      exact FinProb.Ex_const _ 1
    rw [h1]
    simp
  | succ n ih =>
    rw [Ex_snoc n ν hν0 hν1 (fun ω : Fin (n + 1) → X => Real.exp (θ * previsibleSum Φ ω))]
    set Pn := (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
      (fun k => hν1 k.val)).toFinProb with hPn
    have hsum : (∑ k : Fin (n + 1), vf k.val) = (∑ k : Fin n, vf k.val) + vf n := by
      rw [Fin.sum_univ_castSucc]; simp only [Fin.coe_castSucc, Fin.val_last]
    rw [hsum]
    have inner : ∀ ω' : Fin n → X,
        (∑ y, ν n y * Real.exp (θ * previsibleSum Φ (Fin.snoc ω' y)))
          ≤ Real.exp ((2 / 3) * θ ^ 2 * vf n) * Real.exp (θ * previsibleSum Φ ω') := by
      intro ω'
      have step1 : (∑ y, ν n y * Real.exp (θ * previsibleSum Φ (Fin.snoc ω' y)))
          = Real.exp (θ * previsibleSum Φ ω') * ∑ y, ν n y * Real.exp (θ * Φ n ω' y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [previsibleSum_snoc, mul_add, Real.exp_add]
        ring
      rw [step1]
      have hmg := mgf_single (ν n) (Φ n ω') (hν0 n) (hν1 n) θ (fun x => hc n ω' x) (hΦmz n ω')
      have hvar : Real.exp ((2 / 3) * θ ^ 2 * (∑ x, ν n x * (Φ n ω' x) ^ 2))
          ≤ Real.exp ((2 / 3) * θ ^ 2 * vf n) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hΦvar n ω') (by positivity))
      calc Real.exp (θ * previsibleSum Φ ω') * ∑ y, ν n y * Real.exp (θ * Φ n ω' y)
          ≤ Real.exp (θ * previsibleSum Φ ω') * Real.exp ((2 / 3) * θ ^ 2 * (∑ x, ν n x * (Φ n ω' x) ^ 2)) :=
            mul_le_mul_of_nonneg_left hmg (Real.exp_pos _).le
        _ ≤ Real.exp (θ * previsibleSum Φ ω') * Real.exp ((2 / 3) * θ ^ 2 * vf n) :=
            mul_le_mul_of_nonneg_left hvar (Real.exp_pos _).le
        _ = Real.exp ((2 / 3) * θ ^ 2 * vf n) * Real.exp (θ * previsibleSum Φ ω') := by ring
    refine le_trans (Pn.Ex_mono inner) ?_
    rw [Pn.Ex_smul]
    refine le_trans (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le) ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (le_of_eq (by ring))

/-- **The previsible super-martingale bound (with variance budget `V`).** -/
theorem sumMGF_prev (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x) (hν1 : ∀ m, ∑ x, ν m x = 1)
    (Φ : ∀ m, (Fin m → X) → X → ℝ) (θ V : ℝ) (vf : ℕ → ℝ)
    (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0) (hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ)
    (hV : (∑ k : Fin n, vf k.val) ≤ V) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Ex (fun ω : Fin n → X => Real.exp (θ * previsibleSum Φ ω))
      ≤ Real.exp ((2 / 3) * θ ^ 2 * V) := by
  refine le_trans (sumMGF_prev_exact ν hν0 hν1 Φ θ vf hΦmz hc hΦvar n) ?_
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hV (by positivity))

/-- **Previsible raw one-sided tail** at an arbitrary `θ > 0` (previsible analogue
of `tail_raw`). -/
theorem tail_raw_prev (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x) (hν1 : ∀ m, ∑ x, ν m x = 1)
    (Φ : ∀ m, (Fin m → X) → X → ℝ) (θ V : ℝ) (vf : ℕ → ℝ) (hθ : 0 < θ)
    (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0) (hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ)
    (hV : (∑ k : Fin n, vf k.val) ≤ V) (lam : ℝ) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
      ≤ Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := by
  have hmk := pr_le_exp_mgf (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
    (fun k => hν1 k.val)).toFinProb (previsibleSum Φ) (a := lam) hθ
  have hmgf := sumMGF_prev ν hν0 hν1 Φ θ V vf hΦmz hc hΦvar n hV
  calc (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Pr
          (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
      ≤ (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Ex (fun ω => Real.exp (θ * previsibleSum Φ ω))
          / Real.exp (θ * lam) := hmk
    _ ≤ Real.exp ((2 / 3) * θ ^ 2 * V) / Real.exp (θ * lam) :=
        (div_le_div_iff_of_pos_right (Real.exp_pos _)).2 hmgf
    _ = Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := (Real.exp_sub _ _).symm

/-- **Previsible one-sided Freedman/Bernstein tail (optimized).**  Same statement
as `freedman_tail_upper` but for the previsible martingale sum `previsibleSum Φ`. -/
theorem freedman_tail_upper_prev (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (b V : ℝ) (vf : ℕ → ℝ)
    (hΦb : ∀ m p x, |Φ m p x| ≤ b) (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ)
    (hV : (∑ k : Fin n, vf k.val) ≤ V) (hVpos : 0 < V) (lam : ℝ) (hbl : b * lam ≤ V)
    (hlam : 0 ≤ lam) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
      ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · rw [← hlam0, show (-3 * (0 : ℝ) ^ 2 / (8 * V)) = 0 by ring, Real.exp_zero]
    exact FinProb.Pr_le_one _ _
  · set θ := 3 * lam / (4 * V) with hθdef
    have hθ : 0 < θ := by rw [hθdef]; positivity
    have hθb : θ * b ≤ 3 / 4 := by
      rw [hθdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hbl]
    have hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4 := by
      intro m p x
      rw [abs_mul, abs_of_pos hθ]
      calc θ * |Φ m p x| ≤ θ * b := mul_le_mul_of_nonneg_left (hΦb m p x) hθ.le
        _ ≤ 3 / 4 := hθb
    have hraw := tail_raw_prev ν hν0 hν1 Φ θ V vf hθ hΦmz hc hΦvar n hV lam
    have hexp : (2 / 3) * θ ^ 2 * V - θ * lam = -3 * lam ^ 2 / (8 * V) := by
      rw [hθdef]; field_simp; ring
    rwa [hexp] at hraw

set_option linter.unusedSectionVars false in
/-- `previsibleSum` of the negated increments is the negation of `previsibleSum`. -/
theorem previsibleSum_neg {n : ℕ} (Φ : ∀ m, (Fin m → X) → X → ℝ) (ω : Fin n → X) :
    previsibleSum (fun m p x => -(Φ m p x)) ω = -(previsibleSum Φ ω) := by
  simp only [previsibleSum, Finset.sum_neg_distrib]

/-- **Previsible two-sided Freedman/Bernstein tail.** -/
theorem freedman_tail_prev (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (b V : ℝ) (vf : ℕ → ℝ)
    (hΦb : ∀ m p x, |Φ m p x| ≤ b) (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ)
    (hV : (∑ k : Fin n, vf k.val) ≤ V) (hVpos : 0 < V) (lam : ℝ) (hbl : b * lam ≤ V)
    (hlam : 0 ≤ lam) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X => lam ≤ |previsibleSum Φ ω|)
      ≤ 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  have hup := freedman_tail_upper_prev ν hν0 hν1 Φ b V vf hΦb hΦmz hΦvar n hV hVpos lam hbl hlam
  have hΦb' : ∀ m p x, |(-(Φ m p x))| ≤ b := fun m p x => by rw [abs_neg]; exact hΦb m p x
  have hΦmz' : ∀ m p, ∑ x, ν m x * (-(Φ m p x)) = 0 := fun m p => by
    simp only [mul_neg, Finset.sum_neg_distrib, hΦmz m p, neg_zero]
  have hΦvar' : ∀ m p, ∑ x, ν m x * (-(Φ m p x)) ^ 2 ≤ vf m := by
    intro m p; simp only [neg_sq]; exact hΦvar m p
  have hlo0 := freedman_tail_upper_prev ν hν0 hν1 (fun m p x => -(Φ m p x)) b V vf
    hΦb' hΦmz' hΦvar' n hV hVpos lam hbl hlam
  have hsub : (Finset.univ.filter fun ω : Fin n → X => lam ≤ |previsibleSum Φ ω|)
      ⊆ (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
        ∪ (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases le_abs.1 hω.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, ?_⟩)
      exact le_of_le_of_eq h (previsibleSum_neg Φ ω).symm
  calc (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Pr
          (Finset.univ.filter fun ω : Fin n → X => lam ≤ |previsibleSum Φ ω|)
      ≤ (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Pr
          ((Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
          ∪ (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω)) :=
        FinProb.Pr_mono _ hsub
    _ ≤ (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
            (fun k => hν1 k.val)).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum Φ ω)
          + (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
            (fun k => hν1 k.val)).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X => lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω) :=
        FinProb.Pr_union_le _ _ _
    _ ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) + Real.exp (-3 * lam ^ 2 / (8 * V)) :=
        add_le_add hup hlo0
    _ = 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by ring

/-! ## Part 4 — the PATHWISE predictable-variance bound

`freedman_tail_prev` asks for a **deterministic** per-step variance budget: the
conditional variance `∑_x ν m x · (Φ m p x)²` must be at most a number `vf m`
that does not depend on the prefix `p`.  Many martingales have a genuinely
*random* conditional variance (say `4^j · 𝟙[ℓ(s) ≥ j]`, where `ℓ(s)` is read off
the past), and replacing it by its worst case over prefixes throws away exactly
the factor the argument was after.

The remedy is standard: carry the variance **inside** the exponent.  Writing
`pathVar vfun ω = ∑_k vfun k (prefixOf k ω)` for the accumulated pathwise
predictable variance, the induction of `sumMGF_prev_exact` proves the *exact*
super-martingale statement

  `E[exp(θ·previsibleSum Φ − (2/3)·θ²·pathVar vfun)] ≤ 1`

(`sumMGF_prev_pathwise`), with no variance budget anywhere.  On the event
`{pathVar vfun ≤ V}` the integrand is at least `exp(θ·λ − (2/3)·θ²·V)`, so
Markov gives the tail bound for the *joint* event
`{λ ≤ previsibleSum Φ} ∩ {pathVar vfun ≤ V}`, and the same optimization in `θ`
as before produces the same exponent `-3λ²/(8V)`.

The deterministic version is recovered by taking `vfun m _ = vf m`
(`freedman_tail_prev_of_pathwise`). -/

/-- The **accumulated pathwise predictable variance** along the trajectory `ω`:
`pathVar vfun ω = ∑_k vfun k (prefixOf k ω)`, where `vfun m p` bounds the
conditional variance of the `m`-th increment given the prefix `p`.  Unlike the
deterministic budget `∑_k vf k` of `freedman_tail_prev`, this is a random
variable. -/
def pathVar {n : ℕ} (vfun : ∀ m, (Fin m → X) → ℝ) (ω : Fin n → X) : ℝ :=
  ∑ k : Fin n, vfun k.val (prefixOf k ω)

set_option linter.unusedSectionVars false in
/-- **Peeling the last coordinate of the pathwise variance.**  The last summand
`vfun n (prefixOf (last n) (snoc ω' y)) = vfun n ω'` does not depend on the
appended coordinate `y` — that is precisely previsibility. -/
theorem pathVar_snoc {n : ℕ} (vfun : ∀ m, (Fin m → X) → ℝ) (ω' : Fin n → X) (y : X) :
    pathVar vfun (Fin.snoc ω' y) = pathVar vfun ω' + vfun n ω' := by
  unfold pathVar
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [prefixOf_castSucc_snoc]
    rfl
  · rw [prefixOf_last_snoc]
    rfl

/-- **The pathwise exponential super-martingale identity.**  With the predictable
variance carried inside the exponent there is no budget to spend and no
inequality to accumulate:

  `E[exp(θ·previsibleSum Φ − (2/3)·θ²·pathVar vfun)] ≤ 1`.

The proof is the induction of `sumMGF_prev_exact`, peeling the last coordinate
with `Ex_snoc`: at a fixed prefix `ω'` the factor `exp(−(2/3)θ²·vfun n ω')` is
*constant*, and it cancels the bound `exp((2/3)θ²·vfun n ω')` supplied by
`mgf_single`, leaving exactly the integrand one level down. -/
theorem sumMGF_prev_pathwise (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (θ : ℝ)
    (vfun : ∀ m, (Fin m → X) → ℝ)
    (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0) (hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vfun m p) (n : ℕ) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Ex
        (fun ω : Fin n → X =>
          Real.exp (θ * previsibleSum Φ ω - (2 / 3) * θ ^ 2 * pathVar vfun ω))
      ≤ 1 := by
  induction n with
  | zero =>
    have h1 : (fun ω : Fin 0 → X =>
        Real.exp (θ * previsibleSum Φ ω - (2 / 3) * θ ^ 2 * pathVar vfun ω))
        = (fun _ => (1 : ℝ)) := by
      funext ω; simp [previsibleSum, pathVar]
    rw [h1]
    exact le_of_eq (FinProb.Ex_const _ 1)
  | succ n ih =>
    rw [Ex_snoc n ν hν0 hν1 (fun ω : Fin (n + 1) → X =>
      Real.exp (θ * previsibleSum Φ ω - (2 / 3) * θ ^ 2 * pathVar vfun ω))]
    set Pn := (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
      (fun k => hν1 k.val)).toFinProb with hPn
    have inner : ∀ ω' : Fin n → X,
        (∑ y, ν n y * Real.exp (θ * previsibleSum Φ (Fin.snoc ω' y)
            - (2 / 3) * θ ^ 2 * pathVar vfun (Fin.snoc ω' y)))
          ≤ Real.exp (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω') := by
      intro ω'
      have step1 : (∑ y, ν n y * Real.exp (θ * previsibleSum Φ (Fin.snoc ω' y)
            - (2 / 3) * θ ^ 2 * pathVar vfun (Fin.snoc ω' y)))
          = (Real.exp (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω')
              * Real.exp (-((2 / 3) * θ ^ 2 * vfun n ω')))
            * ∑ y, ν n y * Real.exp (θ * Φ n ω' y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [previsibleSum_snoc, pathVar_snoc,
          show θ * (previsibleSum Φ ω' + Φ n ω' y)
              - (2 / 3) * θ ^ 2 * (pathVar vfun ω' + vfun n ω')
            = (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω')
              + (-((2 / 3) * θ ^ 2 * vfun n ω')) + θ * Φ n ω' y from by ring,
          Real.exp_add, Real.exp_add]
        ring
      rw [step1]
      have hmg := mgf_single (ν n) (Φ n ω') (hν0 n) (hν1 n) θ (fun x => hc n ω' x) (hΦmz n ω')
      have hvar : Real.exp ((2 / 3) * θ ^ 2 * (∑ x, ν n x * (Φ n ω' x) ^ 2))
          ≤ Real.exp ((2 / 3) * θ ^ 2 * vfun n ω') :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hΦvar n ω') (by positivity))
      calc (Real.exp (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω')
              * Real.exp (-((2 / 3) * θ ^ 2 * vfun n ω')))
            * ∑ y, ν n y * Real.exp (θ * Φ n ω' y)
          ≤ (Real.exp (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω')
              * Real.exp (-((2 / 3) * θ ^ 2 * vfun n ω')))
            * Real.exp ((2 / 3) * θ ^ 2 * vfun n ω') :=
            mul_le_mul_of_nonneg_left (le_trans hmg hvar) (by positivity)
        _ = Real.exp (θ * previsibleSum Φ ω' - (2 / 3) * θ ^ 2 * pathVar vfun ω') := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact le_trans (Pn.Ex_mono inner) ih

/-- **The pathwise raw one-sided tail** at an arbitrary `θ > 0`.  On the event
`{pathVar vfun ≤ V}` the pathwise super-martingale of `sumMGF_prev_pathwise` is
at least `exp(θ·λ − (2/3)θ²·V)` wherever `λ ≤ previsibleSum Φ`, so Markov's
inequality applied to it bounds the *joint* event. -/
theorem tail_raw_prev_pathwise (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (θ V : ℝ)
    (vfun : ∀ m, (Fin m → X) → ℝ) (hθ : 0 < θ)
    (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0) (hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vfun m p) (n : ℕ) (lam : ℝ) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
      ≤ Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := by
  set P := (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
    (fun k => hν1 k.val)).toFinProb with hP
  set G : (Fin n → X) → ℝ := fun ω =>
    Real.exp (θ * previsibleSum Φ ω - (2 / 3) * θ ^ 2 * pathVar vfun ω) with hG
  have hEx : P.Ex G ≤ 1 := sumMGF_prev_pathwise ν hν0 hν1 Φ θ vfun hΦmz hc hΦvar n
  set t := Real.exp (θ * lam - (2 / 3) * θ ^ 2 * V) with ht
  have htpos : 0 < t := Real.exp_pos _
  have hsub : (Finset.univ.filter fun ω : Fin n → X =>
        lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
      ⊆ Finset.univ.filter (fun ω : Fin n → X => t ≤ G ω) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨hω.1, ?_⟩
    rw [hG, ht]
    refine Real.exp_le_exp.2 ?_
    have h1 : θ * lam ≤ θ * previsibleSum Φ ω :=
      mul_le_mul_of_nonneg_left hω.2.1 hθ.le
    have h2 : (2 / 3) * θ ^ 2 * pathVar vfun ω ≤ (2 / 3) * θ ^ 2 * V :=
      mul_le_mul_of_nonneg_left hω.2.2 (by positivity)
    linarith
  calc P.Pr (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
      ≤ P.Pr (Finset.univ.filter fun ω : Fin n → X => t ≤ G ω) := P.Pr_mono hsub
    _ ≤ P.Ex G / t := P.markov G (fun ω => (Real.exp_pos _).le) htpos
    _ ≤ 1 / t := (div_le_div_iff_of_pos_right htpos).2 hEx
    _ = Real.exp ((2 / 3) * θ ^ 2 * V - θ * lam) := by
        rw [ht, one_div, ← Real.exp_neg]
        congr 1
        ring

/-- **Pathwise one-sided Freedman/Bernstein tail (optimized).**  Same conclusion
as `freedman_tail_upper_prev`, but the variance hypothesis is the *pathwise*
`∑_x ν m x · (Φ m p x)² ≤ vfun m p` (a bound that may depend on the past), and
the event is intersected with the budget event `{pathVar vfun ω ≤ V}`:

  `Pr[λ ≤ previsibleSum Φ  ∧  pathVar vfun ≤ V] ≤ exp(-3λ²/(8V))`.

Obtained from `tail_raw_prev_pathwise` at the same optimal `θ = 3λ/(4V)`. -/
theorem freedman_tail_upper_prev_pathwise (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (b V : ℝ)
    (vfun : ∀ m, (Fin m → X) → ℝ)
    (hΦb : ∀ m p x, |Φ m p x| ≤ b) (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vfun m p)
    (hvfun0 : ∀ m p, 0 ≤ vfun m p) (n : ℕ) (hVpos : 0 < V) (lam : ℝ)
    (hbl : b * lam ≤ V) (hlam : 0 ≤ lam) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
      ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · rw [← hlam0, show (-3 * (0 : ℝ) ^ 2 / (8 * V)) = 0 by ring, Real.exp_zero]
    exact FinProb.Pr_le_one _ _
  · set θ := 3 * lam / (4 * V) with hθdef
    have hθ : 0 < θ := by rw [hθdef]; positivity
    have hθb : θ * b ≤ 3 / 4 := by
      rw [hθdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hbl]
    have hc : ∀ m p x, |θ * Φ m p x| ≤ 3 / 4 := by
      intro m p x
      rw [abs_mul, abs_of_pos hθ]
      calc θ * |Φ m p x| ≤ θ * b := mul_le_mul_of_nonneg_left (hΦb m p x) hθ.le
        _ ≤ 3 / 4 := hθb
    have hraw := tail_raw_prev_pathwise ν hν0 hν1 Φ θ V vfun hθ hΦmz hc hΦvar n lam
    have hexp : (2 / 3) * θ ^ 2 * V - θ * lam = -3 * lam ^ 2 / (8 * V) := by
      rw [hθdef]; field_simp; ring
    rwa [hexp] at hraw

/-- **Pathwise two-sided Freedman/Bernstein tail.**  The pathwise analogue of
`freedman_tail_prev`:

  `Pr[λ ≤ |previsibleSum Φ|  ∧  pathVar vfun ≤ V] ≤ 2·exp(-3λ²/(8V))`.

Obtained by applying `freedman_tail_upper_prev_pathwise` to `Φ` and to `-Φ`
(which have the *same* pathwise variance bound `vfun`, since `(-Φ)² = Φ²`, hence
the same budget event) and a union bound. -/
theorem freedman_tail_prev_pathwise (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (b V : ℝ)
    (vfun : ∀ m, (Fin m → X) → ℝ)
    (hΦb : ∀ m p x, |Φ m p x| ≤ b) (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vfun m p)
    (hvfun0 : ∀ m p, 0 ≤ vfun m p) (n : ℕ) (hVpos : 0 < V) (lam : ℝ)
    (hbl : b * lam ≤ V) (hlam : 0 ≤ lam) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ |previsibleSum Φ ω| ∧ pathVar vfun ω ≤ V)
      ≤ 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  have hup := freedman_tail_upper_prev_pathwise ν hν0 hν1 Φ b V vfun hΦb hΦmz hΦvar
    hvfun0 n hVpos lam hbl hlam
  have hΦb' : ∀ m p x, |(-(Φ m p x))| ≤ b := fun m p x => by rw [abs_neg]; exact hΦb m p x
  have hΦmz' : ∀ m p, ∑ x, ν m x * (-(Φ m p x)) = 0 := fun m p => by
    simp only [mul_neg, Finset.sum_neg_distrib, hΦmz m p, neg_zero]
  have hΦvar' : ∀ m p, ∑ x, ν m x * (-(Φ m p x)) ^ 2 ≤ vfun m p := by
    intro m p; simp only [neg_sq]; exact hΦvar m p
  have hlo0 := freedman_tail_upper_prev_pathwise ν hν0 hν1 (fun m p x => -(Φ m p x)) b V vfun
    hΦb' hΦmz' hΦvar' hvfun0 n hVpos lam hbl hlam
  have hsub : (Finset.univ.filter fun ω : Fin n → X =>
        lam ≤ |previsibleSum Φ ω| ∧ pathVar vfun ω ≤ V)
      ⊆ (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
        ∪ (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω ∧ pathVar vfun ω ≤ V) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases le_abs.1 hω.2.1 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨mem_univ _, h, hω.2.2⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨mem_univ _, ?_, hω.2.2⟩)
      exact le_of_le_of_eq h (previsibleSum_neg Φ ω).symm
  calc (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Pr
          (Finset.univ.filter fun ω : Fin n → X =>
            lam ≤ |previsibleSum Φ ω| ∧ pathVar vfun ω ≤ V)
      ≤ (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
          (fun k => hν1 k.val)).toFinProb.Pr
          ((Finset.univ.filter fun ω : Fin n → X =>
            lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
          ∪ (Finset.univ.filter fun ω : Fin n → X =>
            lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω ∧ pathVar vfun ω ≤ V)) :=
        FinProb.Pr_mono _ hsub
    _ ≤ (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
            (fun k => hν1 k.val)).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X =>
              lam ≤ previsibleSum Φ ω ∧ pathVar vfun ω ≤ V)
          + (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
            (fun k => hν1 k.val)).toFinProb.Pr
            (Finset.univ.filter fun ω : Fin n → X =>
              lam ≤ previsibleSum (fun m p x => -(Φ m p x)) ω ∧ pathVar vfun ω ≤ V) :=
        FinProb.Pr_union_le _ _ _
    _ ≤ Real.exp (-3 * lam ^ 2 / (8 * V)) + Real.exp (-3 * lam ^ 2 / (8 * V)) :=
        add_le_add hup hlo0
    _ = 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by ring

/-- **Consistency check: the pathwise bound implies the deterministic one.**
Taking `vfun m _ = vf m` makes `pathVar vfun` the constant `∑_k vf k`, so the
budget event is all of `Ω` under `hV` and `freedman_tail_prev_pathwise`
specializes to `freedman_tail_prev` verbatim.  (This is a *re-derivation* of
`freedman_tail_prev`, not a new statement; it certifies that the pathwise event
is not vacuous.) -/
theorem freedman_tail_prev_of_pathwise (ν : ℕ → X → ℝ) (hν0 : ∀ m x, 0 ≤ ν m x)
    (hν1 : ∀ m, ∑ x, ν m x = 1) (Φ : ∀ m, (Fin m → X) → X → ℝ) (b V : ℝ) (vf : ℕ → ℝ)
    (hΦb : ∀ m p x, |Φ m p x| ≤ b) (hΦmz : ∀ m p, ∑ x, ν m x * Φ m p x = 0)
    (hΦvar : ∀ m p, ∑ x, ν m x * (Φ m p x) ^ 2 ≤ vf m) (n : ℕ)
    (hV : (∑ k : Fin n, vf k.val) ≤ V) (hVpos : 0 < V) (lam : ℝ) (hbl : b * lam ≤ V)
    (hlam : 0 ≤ lam) :
    (prodSpace (fun k : Fin n => ν k.val) (fun k => hν0 k.val)
        (fun k => hν1 k.val)).toFinProb.Pr
        (Finset.univ.filter fun ω : Fin n → X => lam ≤ |previsibleSum Φ ω|)
      ≤ 2 * Real.exp (-3 * lam ^ 2 / (8 * V)) := by
  -- the outcome type is nonempty (its masses sum to `1`), so every prefix type is
  have hXne : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hν1 0
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hvf0 : ∀ m, (0 : ℝ) ≤ vf m := by
    intro m
    have hp : Fin m → X := fun _ => Classical.arbitrary X
    refine le_trans ?_ (hΦvar m hp)
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν0 m x) (sq_nonneg _))
  have hpw := freedman_tail_prev_pathwise ν hν0 hν1 Φ b V (fun m _ => vf m) hΦb hΦmz
    (fun m p => hΦvar m p) (fun m _ => hvf0 m) n hVpos lam hbl hlam
  have hconst : ∀ ω : Fin n → X, pathVar (fun m _ => vf m) ω = ∑ k : Fin n, vf k.val :=
    fun ω => rfl
  have hev : (Finset.univ.filter fun ω : Fin n → X => lam ≤ |previsibleSum Φ ω|)
      = (Finset.univ.filter fun ω : Fin n → X =>
          lam ≤ |previsibleSum Φ ω| ∧ pathVar (fun m _ => vf m) ω ≤ V) := by
    apply Finset.filter_congr
    intro ω _
    rw [hconst ω]
    exact ⟨fun h => ⟨h, hV⟩, fun h => h.1⟩
  rw [hev]
  exact hpw

end Arlib.Probability
