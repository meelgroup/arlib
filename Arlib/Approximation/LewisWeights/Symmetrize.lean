/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Symmetrization: the probabilistic core of Cohen–Peng's `momentreduct` (L5)

The `momentreduct` reduction of Cohen–Peng passes from the *sampling error* of the
ℓ₁ Lewis importance sampler to a **Rademacher sign process**, at the cost of a
factor `2^{2k}` in the `2k`-th moment.  This is the standard symmetrization
argument, formalized here for the sampler of `Sampler.lean`.

Writing `Ê(y) = (sampledWPS … ω).E y = ∑ᵣ sval(ωᵣ)` for the reduced functional (a
sum of `m` iid draws `sval(i) = (1/(m pᵢ))·|⟨y, aᵢ⟩|`) and
`‖Ay‖₁ = (WPS.exact ι a).E y` for its mean, we prove

    `𝔼_ω[(Ê(y) − ‖Ay‖₁)^{2k}] ≤ 2^{2k} · 𝔼_{σ,ω}[(∑ᵣ σᵣ sval(ωᵣ))^{2k}]`
    (`sampled_central_moment_le_symm`),

where `σ` is an independent uniform sign vector.  The three moves are classical and
use **no matrix Chernoff**:

1. *Independent copy + Jensen.*  `‖Ay‖₁ = 𝔼_{ω'}[Ê'(y)]`, so
   `Ê(y) − ‖Ay‖₁ = 𝔼_{ω'}[∑ᵣ(sval(ωᵣ) − sval(ω'ᵣ))]`; convexity of `t ↦ t^{2k}`
   moves the power inside the `ω'`-expectation.
2. *Sign insertion.*  The pair `(ω, ω')` is coordinate-wise exchangeable, so the
   per-coordinate swap `swapPair σ` (measure-preserving, `Ex_prodFinProb_swapPair`)
   turns `∑ᵣ(sval(ωᵣ) − sval(ω'ᵣ))` into `∑ᵣ σᵣ(sval(ωᵣ) − sval(ω'ᵣ))` for every `σ`.
3. *Convex split.*  `(A − B)^{2k} ≤ 2^{2k−1}(A^{2k} + B^{2k})`, and the two halves
   have equal expectation, collapsing the coupled sum to a single sign process at
   cost `2^{2k}`.

`MomentReduct.lean` composes this with Khintchine to reach the empirical-energy
moment bound — Cohen–Peng's `lem:momentreduct`.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.SymmSwap
import Arlib.Approximation.LewisWeights.Sampler
import Arlib.Approximation.LewisWeights.Probability
import Arlib.Probability.FinProbProd
import Mathlib.Analysis.MeanInequalitiesPow

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset Arlib Arlib.Approximation Arlib.Probability

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The value contributed by a single Lewis importance draw of row `i`, for query
`y`: `(1 / (m·pᵢ))·|⟨y, aᵢ⟩|` with `pᵢ = wᵢ/∑w`.  The reduced functional
`(sampledWPS … ω).E y` is `∑ᵣ sval (ωᵣ)`. -/
noncomputable def sval (w : ι → ℝ) (a : ι → d → ℝ) (m : ℕ) (y : d → ℝ) (i : ι) : ℝ :=
  (1 / ((m : ℝ) * (w i / (∑ j, w j)))) * |dot y (a i)|

variable {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## Small reusable facts about `FinProb.Ex` and even powers -/

/-- Monotonicity of `FinProb.Ex`. -/
private theorem finEx_mono (P : FinProb) {f g : P.Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    P.Ex f ≤ P.Ex g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.mass_nonneg ω)

/-- Congruence of `FinProb.Ex` under a pointwise-equal integrand. -/
private theorem finEx_congr (P : FinProb) {f g : P.Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    P.Ex f = P.Ex g :=
  congrArg P.Ex (funext h)

/-- `FinProb.Ex` is linear over subtraction. -/
private theorem finEx_sub (P : FinProb) (X Y : P.Ω → ℝ) :
    P.Ex (fun ω => X ω - Y ω) = P.Ex X - P.Ex Y := by
  show (∑ ω, P.mass ω * (X ω - Y ω)) = (∑ ω, P.mass ω * X ω) - ∑ ω, P.mass ω * Y ω
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- `FinProb.Ex` is additive. -/
private theorem finEx_add (P : FinProb) (X Y : P.Ω → ℝ) :
    P.Ex (fun ω => X ω + Y ω) = P.Ex X + P.Ex Y := by
  show (∑ ω, P.mass ω * (X ω + Y ω)) = (∑ ω, P.mass ω * X ω) + ∑ ω, P.mass ω * Y ω
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- `FinProb.Ex` pulls out a constant scalar. -/
private theorem finEx_const_mul (P : FinProb) (c : ℝ) (X : P.Ω → ℝ) :
    P.Ex (fun ω => c * X ω) = c * P.Ex X := by
  show (∑ ω, P.mass ω * (c * X ω)) = c * ∑ ω, P.mass ω * X ω
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Jensen for even powers over a probability measure:
`(𝔼 f)^{2k} ≤ 𝔼 (f^{2k})`. -/
private theorem jensen_even_pow (P : FinProb) (f : P.Ω → ℝ) (k : ℕ) :
    (P.Ex f) ^ (2 * k) ≤ P.Ex (fun ω => f ω ^ (2 * k)) := by
  have hev : Even (2 * k) := ⟨k, two_mul k⟩
  have h := Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ
    (fun ω => P.mass ω) f (fun ω _ => P.mass_nonneg ω) (by simpa using P.mass_sum) hev
  simpa [FinProb.Ex] using h

/-- Even-power convex split: `(A − B)^{2k} ≤ 2^{2k−1}(A^{2k} + B^{2k})`. -/
private theorem sub_pow_even_le (A B : ℝ) (k : ℕ) :
    (A - B) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (A ^ (2 * k) + B ^ (2 * k)) := by
  have hev : Even (2 * k) := ⟨k, two_mul k⟩
  have h1 : (A - B) ^ (2 * k) = |A - B| ^ (2 * k) := (hev.pow_abs _).symm
  have h3 : |A - B| ^ (2 * k) ≤ (|A| + |B|) ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) (2 * k)
  have h4 : (|A| + |B|) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (|A| ^ (2 * k) + |B| ^ (2 * k)) :=
    add_pow_le (abs_nonneg A) (abs_nonneg B) (2 * k)
  rw [h1]; exact h3.trans (h4.trans (by rw [hev.pow_abs, hev.pow_abs]))

/-- Per-coordinate action of `swapPair` on the difference of draw values. -/
private theorem sval_swapPair_diff (m : ℕ) (y : d → ℝ) (σ : Fin m → Bool)
    (p : (Fin m → ι) × (Fin m → ι)) (r : Fin m) :
    sval w a m y ((swapPair σ p).1 r) - sval w a m y ((swapPair σ p).2 r)
      = Sgn (σ r) * (sval w a m y (p.1 r) - sval w a m y (p.2 r)) := by
  simp only [swapPair]
  by_cases hσ : σ r
  · simp only [hσ, if_true, Sgn]; ring
  · simp only [hσ, if_false, Bool.false_eq_true, Sgn]; ring

/-! ## The reduced functional as a sum of per-draw values -/

/-- `(sampledWPS … ω).E y = ∑ᵣ sval (ωᵣ)`. -/
theorem sampledWPS_E_sval [Nonempty ι] (hw : ∀ i, 0 < w i)
    (m : ℕ) (y : d → ℝ) (ω : Fin m → ι) :
    (sampledWPS w hw a m ω).E y = ∑ r, sval w a m y (ω r) :=
  sampledWPS_E w hw a m ω y

/-! ## The symmetrization inequality (L5) -/

/-- **Symmetrization to the sign process** (the probabilistic core of Cohen–Peng's
`lem:momentreduct`).  The `2k`-th central moment of the Lewis importance-sampling
estimator is bounded by `2^{2k}` times the `2k`-th moment of the corresponding
Rademacher sign process:

`𝔼_ω[(Ê(y) − ‖Ay‖₁)^{2k}] ≤ 2^{2k} · 𝔼_{σ,ω}[(∑ᵣ σᵣ·sval(ωᵣ))^{2k}]`.

No matrix Chernoff, no net: an independent copy, the measure-preserving swap
`Ex_prodFinProb_swapPair`, Jensen, and a convex split. -/
theorem sampled_central_moment_le_symm [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (m : ℕ) (hm : 0 < m) (y : d → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (sampleSpace w hw m).Ex
        (fun ω => ((sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y) ^ (2 * k))
      ≤ 2 ^ (2 * k) *
        (prodFinProb (radProb (Fin m)) (sampleSpace w hw m)).Ex
          (fun q => (∑ r, Sgn (q.1 r) * sval w a m y (q.2 r)) ^ (2 * k)) := by
  set E : ℝ := (WPS.exact ι a).E y with hE
  -- unbiasedness: E = 𝔼_ω (Ê(y))
  have hunb : (sampleSpace w hw m).Ex (fun ω => (sampledWPS w hw a m ω).E y) = E :=
    estimator_unbiased w hw a m hm y
  -- STEP 1: independent copy + Jensen.
  have hcenter : ∀ ω : Fin m → ι,
      (sampleSpace w hw m).Ex
          (fun ω' => (sampledWPS w hw a m ω).E y - (sampledWPS w hw a m ω').E y)
        = (sampledWPS w hw a m ω).E y - E := by
    intro ω
    rw [finEx_sub (sampleSpace w hw m) (fun _ => (sampledWPS w hw a m ω).E y)
      (fun ω' => (sampledWPS w hw a m ω').E y), FinProb.Ex_const, hunb]
  have step1 :
      (sampleSpace w hw m).Ex
          (fun ω => ((sampledWPS w hw a m ω).E y - E) ^ (2 * k))
        ≤ (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
            (fun p => ((sampledWPS w hw a m p.1).E y - (sampledWPS w hw a m p.2).E y) ^ (2 * k)) := by
    rw [Ex_prodFinProb]
    refine finEx_mono (sampleSpace w hw m) (fun ω => ?_)
    rw [← hcenter ω]
    exact jensen_even_pow (sampleSpace w hw m)
      (fun ω' => (sampledWPS w hw a m ω).E y - (sampledWPS w hw a m ω').E y) k
  -- STEP 2: coordinates + sign insertion.
  -- the coupled difference is a coordinate sum
  have hD : ∀ p : (Fin m → ι) × (Fin m → ι),
      (sampledWPS w hw a m p.1).E y - (sampledWPS w hw a m p.2).E y
        = ∑ r, (sval w a m y (p.1 r) - sval w a m y (p.2 r)) := by
    intro p
    rw [sampledWPS_E_sval hw m y, sampledWPS_E_sval hw m y, ← Finset.sum_sub_distrib]
  -- rewrite RHS of step1 in coordinate form
  have hRHS1 :
      (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => ((sampledWPS w hw a m p.1).E y - (sampledWPS w hw a m p.2).E y) ^ (2 * k))
        = (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k)) :=
    finEx_congr _ (fun p => congrArg (· ^ (2 * k)) (hD p))
  -- sign insertion via the measure-preserving swap
  have hswap : ∀ σ : Fin m → Bool,
      (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, Sgn (σ r)
              * (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k))
        = (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k)) := by
    intro σ
    have hmid := Ex_prodFinProb_swapPair w hw m σ
      (fun p => (∑ r, (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k))
    refine Eq.trans (finEx_congr _ (fun p => ?_)) hmid
    refine congrArg (· ^ (2 * k)) ?_
    exact Finset.sum_congr rfl fun r _ => (sval_swapPair_diff m y σ p r).symm
  -- distribute the sign over the difference
  have hdist : ∀ (σ : Fin m → Bool) (p : (Fin m → ι) × (Fin m → ι)),
      (∑ r, Sgn (σ r) * (sval w a m y (p.1 r) - sval w a m y (p.2 r)))
        = (∑ r, Sgn (σ r) * sval w a m y (p.1 r))
            - (∑ r, Sgn (σ r) * sval w a m y (p.2 r)) := by
    intro σ p
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [mul_sub]
  -- STEP 3: convex split + fold to a single sign process
  -- H σ, and the fst/snd expectations both equal it
  have hfst : ∀ σ : Fin m → Bool,
      (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, Sgn (σ r) * sval w a m y (p.1 r)) ^ (2 * k))
        = (sampleSpace w hw m).Ex
          (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k)) :=
    fun σ => Ex_prodFinProb_fst (sampleSpace w hw m) (sampleSpace w hw m)
      (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))
  have hsnd : ∀ σ : Fin m → Bool,
      (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, Sgn (σ r) * sval w a m y (p.2 r)) ^ (2 * k))
        = (sampleSpace w hw m).Ex
          (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k)) :=
    fun σ => Ex_prodFinProb_snd (sampleSpace w hw m) (sampleSpace w hw m)
      (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))
  have h2k1 : 2 * k - 1 + 1 = 2 * k := by omega
  have hHbound : ∀ σ : Fin m → Bool,
      (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, Sgn (σ r)
              * (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k))
        ≤ 2 ^ (2 * k) * (sampleSpace w hw m).Ex
          (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k)) := by
    intro σ
    have hle :
        (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
            (fun p => (∑ r, Sgn (σ r)
                * (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k))
          ≤ (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
            (fun p => 2 ^ (2 * k - 1)
              * ((∑ r, Sgn (σ r) * sval w a m y (p.1 r)) ^ (2 * k)
                + (∑ r, Sgn (σ r) * sval w a m y (p.2 r)) ^ (2 * k))) := by
      refine finEx_mono _ (fun p => ?_)
      rw [hdist σ p]
      exact sub_pow_even_le _ _ k
    refine hle.trans (le_of_eq ?_)
    rw [finEx_const_mul, finEx_add, hfst, hsnd, ← two_mul, ← mul_assoc, ← pow_succ, h2k1]
  -- assemble
  calc (sampleSpace w hw m).Ex
          (fun ω => ((sampledWPS w hw a m ω).E y - E) ^ (2 * k))
      ≤ (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => ((sampledWPS w hw a m p.1).E y - (sampledWPS w hw a m p.2).E y) ^ (2 * k)) :=
        step1
    _ = (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
          (fun p => (∑ r, (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k)) := hRHS1
    _ = (radProb (Fin m)).Ex (fun σ =>
          (prodFinProb (sampleSpace w hw m) (sampleSpace w hw m)).Ex
            (fun p => (∑ r, Sgn (σ r)
                * (sval w a m y (p.1 r) - sval w a m y (p.2 r))) ^ (2 * k))) :=
        (FinProb.Ex_const (radProb (Fin m)) _).symm.trans
          (finEx_congr _ (fun σ => (hswap σ).symm))
    _ ≤ (radProb (Fin m)).Ex (fun σ => 2 ^ (2 * k) * (sampleSpace w hw m).Ex
          (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))) :=
        finEx_mono _ hHbound
    _ = 2 ^ (2 * k) * (radProb (Fin m)).Ex (fun σ => (sampleSpace w hw m).Ex
          (fun ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))) := by
        rw [finEx_const_mul]
    _ = 2 ^ (2 * k) * (prodFinProb (radProb (Fin m)) (sampleSpace w hw m)).Ex
          (fun q => (∑ r, Sgn (q.1 r) * sval w a m y (q.2 r)) ^ (2 * k)) := by
        rw [Ex_prodFinProb]

end Arlib.Approximation.LewisWeights
