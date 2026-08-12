/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Dirichlet form, the Poincaré inequality, and positive semidefiniteness

Where `Var_μ(f)` measures the *global* variation of `f`, the Dirichlet form
`ℰ_P(f)` measures its *local* variation along the edges of the transition graph
`(Ω, P)`.  The entire mixing-time theory is the comparison of the two: a chain
mixes quickly exactly when local variation controls global variation, which is
the Poincaré inequality `γ · Var_μ(f) ≤ ℰ_P(f)`.

* `dirichlet μ P f g` — the bilinear form `⟪f, (I - P) g⟫_μ`; the Dirichlet form
  proper is the quadratic case `dirichlet μ P f f`.
* `sum_pair_sq` — the workhorse: for a *stationary* `μ` and any `s : ℝ`,
  `∑ x, ∑ y, μ x * P x y * (f x + s * f y) ^ 2 = (1 + s²)⟪f,f⟫ + 2s⟪f, Pf⟫`.
  Specialising to `s = -1` gives the pair form of the Dirichlet form, and to
  `s = 1` the lower bound `-⟪f,f⟫ ≤ ⟪f, Pf⟫`.  Both signs matter: one says the
  chain is a contraction, the other that it cannot overshoot.
* `dirichlet_self_eq_pair` — `ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`, the
  paper's definition, here a theorem.
* `SpectralGapAtLeast μ P γ` — the Poincaré inequality.  Following the source
  monograph we take this *as* the definition of the spectral gap: for reversible
  chains it agrees with `1 - λ₂`, and for non-reversible ones it is the right
  notion anyway (the "Poincaré constant"), so no eigenvalue is ever needed.
* `NonnegDefinite μ P` — `0 ≤ ⟪f, P f⟫_μ` for all `f`, the PSD condition.  This
  is what upgrades the spectral gap to the *absolute* spectral gap, and hence
  what makes the gap control the decay of variance; see
  `Arlib.MarkovChains.Techniques.SpectralGap`.

The pay-off proved here is `ip_act_le_of_gap`: on a mean-zero function a chain
with gap `γ` which is PSD satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`, the
two-sided bound that drives everything downstream.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.Probability.FinDistFunctional

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The Dirichlet form -/

/-- The **Dirichlet form** as a bilinear form: `ℰ_P(f, g) = ⟪f, (I - P) g⟫_μ`.

The Dirichlet form of the monograph is the quadratic case `dirichlet μ P f f`,
for which `dirichlet_self_eq_pair` gives the familiar edge-sum expression. -/
def dirichlet (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) : ℝ :=
  ip μ f g - ip μ f (P.act g)

theorem dirichlet_apply (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    dirichlet μ P f g = ip μ f g - ip μ f (P.act g) := rfl

/-! ## The pair expansion

Everything about the Dirichlet form flows from a single computation: expanding
`∑_{x,y} μ(x) P(x,y) (f x + s · f y)²` for a stationary `μ`.  The `f x²` term is
resummed with `∑_y P x y = 1`, the `f y²` term with stationarity, and the cross
term is `⟪f, P f⟫_μ` on the nose. -/

/-- The **pair expansion**.  For `μ` stationary and any real `s`,
`∑_{x,y} μ(x) P(x,y) (f x + s · f y)² = (1 + s²)⟪f,f⟫_μ + 2s⟪f, Pf⟫_μ`.

The left-hand side is manifestly nonnegative, so each choice of `s` yields an
inequality between `⟪f,f⟫_μ` and `⟪f, Pf⟫_μ`; `s = -1` and `s = 1` give the two
that matter. -/
theorem sum_pair_sq {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) (s : ℝ) :
    ∑ x, ∑ y, μ x * P x y * (f x + s * f y) ^ 2
      = (1 + s ^ 2) * ip μ f f + 2 * s * ip μ f (P.act f) := by
  have inner : ∀ x : Ω, ∑ y, μ x * P x y * (f x + s * f y) ^ 2
      = μ x * f x * f x + 2 * s * (μ x * f x * P.act f x)
        + s ^ 2 * ∑ y, μ x * P x y * (f y * f y) := by
    intro x
    have step : ∀ y : Ω, μ x * P x y * (f x + s * f y) ^ 2
        = μ x * f x * f x * P x y + 2 * s * (μ x * f x) * (P x y * f y)
          + s ^ 2 * (μ x * P x y * (f y * f y)) := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      P.sum_coe x, mul_one]
    simp only [FinKernel.act]
    ring
  have h2 : ∑ x, 2 * s * (μ x * f x * P.act f x) = 2 * s * ip μ f (P.act f) := by
    rw [← Finset.mul_sum]; rfl
  have h3 : ∑ x, s ^ 2 * ∑ y, μ x * P x y * (f y * f y) = s ^ 2 * ip μ f f := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, h y]
    ring
  rw [Finset.sum_congr rfl fun x _ => inner x, Finset.sum_add_distrib,
    Finset.sum_add_distrib, h2, h3]
  have h1 : ∑ x, μ x * f x * f x = ip μ f f := rfl
  rw [h1]
  ring

/-- **Pair form of the Dirichlet form.**
`ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`.

This is the monograph's *definition* of the Dirichlet form; for us it is a
theorem, and it is the form in which the Dirichlet form is compared to the pair
form of the variance (`Var_eq_pair`). -/
theorem dirichlet_self_eq_pair {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) :
    dirichlet μ P f f = (1 / 2) * ∑ x, ∑ y, μ x * P x y * (f x - f y) ^ 2 := by
  have key := sum_pair_sq h f (-1)
  have rw_sub : ∀ x y : Ω, μ x * P x y * (f x + (-1) * f y) ^ 2
      = μ x * P x y * (f x - f y) ^ 2 := fun x y => by ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => rw_sub x y] at key
  rw [dirichlet_apply, key]
  ring

/-- The Dirichlet form is nonnegative: local variation is a sum of squares. -/
theorem dirichlet_self_nonneg {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : 0 ≤ dirichlet μ P f f := by
  rw [dirichlet_self_eq_pair h f]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  exact mul_nonneg (mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y)) (sq_nonneg _)

/-! ## Two-sided control of `⟪f, P f⟫_μ`

A stochastic kernel is a contraction on `L²(μ)`: taking `s = -1` above bounds
`⟪f, P f⟫_μ` from above by `⟪f, f⟫_μ`, and taking `s = 1` bounds it from below
by `-⟪f, f⟫_μ`.  These are the elementary substitutes for "all eigenvalues lie
in `[-1, 1]`". -/

/-- `⟪f, P f⟫_μ ≤ ⟪f, f⟫_μ`: the chain does not increase the `L²(μ)` norm. -/
theorem ip_act_self_le {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) (f : Ω → ℝ) :
    ip μ f (P.act f) ≤ ip μ f f := by
  have := dirichlet_self_nonneg h f
  rw [dirichlet_apply] at this
  linarith

/-- `-⟪f, f⟫_μ ≤ ⟪f, P f⟫_μ`: the elementary form of "no eigenvalue below `-1`". -/
theorem neg_ip_le_ip_act_self {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : -ip μ f f ≤ ip μ f (P.act f) := by
  have key := sum_pair_sq h f 1
  have hnn : 0 ≤ ∑ x, ∑ y, μ x * P x y * (f x + 1 * f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y)) (sq_nonneg _)
  rw [key] at hnn
  norm_num at hnn
  linarith

/-- The `L²(μ)` operator bound `|⟪f, P f⟫_μ| ≤ ⟪f, f⟫_μ`. -/
theorem abs_ip_act_self_le {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : |ip μ f (P.act f)| ≤ ip μ f f :=
  abs_le.mpr ⟨neg_ip_le_ip_act_self h f, ip_act_self_le h f⟩

/-! ## Symmetry and bilinearity -/

/-- `⟪f, P g⟫_μ = ∑_x ∑_y μ(x)·P(x,y)·f(x)·g(y)`: the inner product against the
action of a kernel, written so that the detailed-balance cell `μ(x)·P(x,y)`
occurs as a subterm. -/
theorem ip_act_eq_sum_sum (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ∑ x, ∑ y, μ x * P x y * (f x * g y) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [FinKernel.act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Reversibility is exactly self-adjointness**: `⟪f, P g⟫_μ = ⟪g, P f⟫_μ`. -/
theorem ip_act_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ip μ g (P.act f) := by
  rw [ip_act_eq_sum_sum μ P f g, ip_act_eq_sum_sum μ P g f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [h x y]; ring

/-- For a reversible chain the Dirichlet form is symmetric. -/
theorem dirichlet_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (f g : Ω → ℝ) :
    dirichlet μ P f g = dirichlet μ P g f := by
  rw [dirichlet_apply, dirichlet_apply, ip_comm μ f g, ip_act_comm h f g]

/-- The Dirichlet form is bilinear, hence (being symmetric and positive
semidefinite for a reversible chain) subject to `psd_cauchy_schwarz`. -/
theorem isBilin_dirichlet (μ : FinDist Ω) (P : FinChain Ω) : IsBilin (dirichlet μ P) := by
  have hb := isBilin_ip μ
  have hip : ∀ f g : Ω → ℝ, ip μ f g = ∑ x, μ x * f x * g x := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [dirichlet_apply]
    rw [hb.add_left u v w, hb.add_left u v (P.act w)]; ring
  · intro c u v
    simp only [dirichlet_apply]
    rw [hb.smul_left c u v, hb.smul_left c u (P.act v)]; ring
  · intro u v w
    simp only [dirichlet_apply]
    have hact : P.act (v + w) = P.act v + P.act w := P.act_add v w
    rw [hb.add_right u v w, hact, hb.add_right u (P.act v) (P.act w)]; ring
  · intro c u v
    simp only [dirichlet_apply]
    have hact : P.act (c • v) = c • P.act v := by
      funext x
      have := congrFun (P.act_smul c v) x
      simpa [Pi.smul_apply, smul_eq_mul, FinKernel.act] using this
    rw [hb.smul_right c u v, hact, hb.smul_right c u (P.act v)]; ring

/-- The Dirichlet form only sees differences: adding a constant to `f` changes
nothing.  (Immediate from the pair form.) -/
theorem dirichlet_self_sub_const {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) (c : ℝ) :
    dirichlet μ P (fun x => f x - c) (fun x => f x - c) = dirichlet μ P f f := by
  rw [dirichlet_self_eq_pair h, dirichlet_self_eq_pair h]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring_nf

/-! ## The spectral gap -/

/-- **The Poincaré inequality**: the chain `P` has spectral gap at least `γ` with
respect to `μ` when `γ · Var_μ(f) ≤ ℰ_P(f)` for every `f`.

Following the source monograph, this *is* our definition of the spectral gap.
For a reversible chain it coincides with `1 - λ₂`, and for a non-reversible one
it is the Poincaré constant, which is the notion the mixing arguments actually
use.  Defining it variationally keeps the whole development free of eigenvalues. -/
def SpectralGapAtLeast (μ : FinDist Ω) (P : FinChain Ω) (γ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, γ * Var μ f ≤ dirichlet μ P f f

/-- Every stationary chain has spectral gap at least `0`. -/
theorem spectralGapAtLeast_zero {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    SpectralGapAtLeast μ P 0 := fun f => by
  simpa using dirichlet_self_nonneg h f

/-- A gap bound weakens. -/
theorem SpectralGapAtLeast.mono {μ : FinDist Ω} {P : FinChain Ω} {γ γ' : ℝ}
    (h : SpectralGapAtLeast μ P γ) (hle : γ' ≤ γ) :
    SpectralGapAtLeast μ P γ' := fun f =>
  le_trans (mul_le_mul_of_nonneg_right hle (Var_nonneg μ f)) (h f)

/-- On a mean-zero function the Poincaré inequality reads
`⟪f, P f⟫_μ ≤ (1 - γ) ⟪f, f⟫_μ`. -/
theorem ip_act_self_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hgap : SpectralGapAtLeast μ P γ) {f : Ω → ℝ} (hf : Ex μ f = 0) :
    ip μ f (P.act f) ≤ (1 - γ) * ip μ f f := by
  have h := hgap f
  rw [Var_eq_ip_self_of_mean_zero hf, dirichlet_apply] at h
  linarith

/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/

/-- `P` is **positive semidefinite** with respect to `μ`. -/
def NonnegDefinite (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ f : Ω → ℝ, 0 ≤ ip μ f (P.act f)

/-- **Two-sided spectral bound.**  For a PSD chain with spectral gap at least
`γ`, every mean-zero `f` satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`.

This is the hypothesis under which variance decays geometrically; see
`Arlib.MarkovChains.Techniques.SpectralGap`. -/
theorem ip_act_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hpsd : NonnegDefinite μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1)
    {f : Ω → ℝ} (hf : Ex μ f = 0) :
    |ip μ f (P.act f)| ≤ (1 - γ) * ip μ f f := by
  refine abs_le.mpr ⟨?_, ip_act_self_le_of_gap hgap hf⟩
  have h0 := hpsd f
  have hnn : 0 ≤ (1 - γ) * ip μ f f :=
    mul_nonneg (by linarith) (ip_self_nonneg μ f)
  linarith

end Arlib.MarkovChains
