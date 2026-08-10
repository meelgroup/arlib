/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `L²(μ)` functional calculus: expectation, inner product, variance

The functional-analytic side of the spectral-independence machinery is carried
out entirely in `L²(μ)` for a distribution `μ` on a finite type.  This module
sets up the three functionals used everywhere downstream and the identities
relating them.

* `Ex μ f` — expectation `∑ x, μ x * f x`.
* `ip μ f g` — inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`.
* `Var μ f` — variance `μ((f - μ(f))²)`.

The key identities, all elementary algebra over a finite sum:

* `Var_eq_ip_sub_sq` — `Var μ f = ⟪f, f⟫_μ - (μ f)²`;
* `Var_eq_pair` — the *pair form* `Var μ f = ½ ∑ x, ∑ y, μ x * μ y * (f x - f y)²`,
  which is what makes variance directly comparable to a Dirichlet form;
* `Var_eq_ip_self_of_mean_zero` — on mean-zero functions variance *is* the
  squared norm, which is why almost every proof below starts by centering `f`.

We also record that `ip μ` is a positive semidefinite symmetric bilinear form
(`isBilin_ip`, `ip_comm`, `ip_self_nonneg`), so that `psd_cauchy_schwarz` from
`Arlib.Probability.Bilinear` applies to it directly, together with the
lambda-form bilinearity lemmas (`ip_add_left`, `ip_smul_right`, …) that the
computations downstream actually rewrite with.

Two families of "support only" lemmas are here because *every* guarded-total
construction in the development produces a junk value off the support of the
averaging distribution: `Ex_congr_ae`, `Var_congr_ae` and `Ex_mono_of_ne_zero`
say that expectations, variances and their monotonicity see only the support.

Finally, `Ex_push_eq` and `ip_push_eq` transport `Ex` and `ip` along a
*rectangular* kernel; they involve no stationarity and are the bookkeeping that
makes the law of total variance (`Arlib.MarkovChains.Techniques.LevelVariance`)
a three-line
computation.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDist
import Arlib.Probability.Bilinear

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-! ## Expectation -/

/-- The expectation `μ(f) = ∑ x, μ x * f x`. -/
def Ex (μ : FinDist Ω) (f : Ω → ℝ) : ℝ := ∑ x, μ x * f x

theorem Ex_apply (μ : FinDist Ω) (f : Ω → ℝ) : Ex μ f = ∑ x, μ x * f x := rfl

@[simp] theorem Ex_const (μ : FinDist Ω) (c : ℝ) : Ex μ (fun _ => c) = c :=
  μ.sum_coe_mul_const c

theorem Ex_add (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x + g x) = Ex μ f + Ex μ g := by
  simp only [Ex, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Ex_sub (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x - g x) = Ex μ f - Ex μ g := by
  simp only [Ex, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation commutes with a finite sum. -/
theorem Ex_sum {ι : Type*} [Fintype ι] (μ : FinDist Ω) (g : ι → Ω → ℝ) :
    Ex μ (fun x => ∑ i, g i x) = ∑ i, Ex μ (g i) := by
  simp only [Ex_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem Ex_smul (μ : FinDist Ω) (c : ℝ) (f : Ω → ℝ) :
    Ex μ (fun x => c * f x) = c * Ex μ f := by
  simp only [Ex, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Ex_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Ex μ (fun x => f x - c) = Ex μ f - c := by
  rw [Ex_sub, Ex_const]

theorem Ex_nonneg {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ Ex μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.coe_nonneg x) (hf x)

theorem Ex_mono {μ : FinDist Ω} {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : Ex μ f ≤ Ex μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.coe_nonneg x)

/-- **Monotonicity of an expectation, on the support only.**  If `F₁ x ≤ F₂ x`
at every `x` carrying `μ`-mass, then `μ(F₁) ≤ μ(F₂)`.  Off the support both
summands are `0`, whatever the two functions do there.

This is the form every average over a *guarded-total* construction needs, where
the junk value off the support makes the pointwise hypothesis of `Ex_mono`
false. -/
theorem Ex_mono_of_ne_zero (μ : FinDist Ω) {F₁ F₂ : Ω → ℝ}
    (h : ∀ x, μ x ≠ 0 → F₁ x ≤ F₂ x) : Ex μ F₁ ≤ Ex μ F₂ := by
  simp only [Ex_apply]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.coe_nonneg x)

/-- A pointwise positive function has positive `μ`-mean.  Needed to license the
mean-normalisation in the attainment half of the Gibbs variational principle; it
is not automatic from `f ≥ 0`. -/
theorem Ex_pos_of_pos {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 < f x) : 0 < Ex μ f := by
  rcases (Ex_nonneg fun x => (hf x).le).eq_or_lt with h0 | hpos
  · exfalso
    have hsum : ∑ x : Ω, μ x * f x = 0 := by rw [← Ex_apply]; exact h0.symm
    have hz : ∀ x : Ω, μ x * f x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
        mul_nonneg (μ.coe_nonneg y) (hf y).le).mp hsum x (Finset.mem_univ x)
    have hzero : ∀ x : Ω, μ x = 0 := by
      intro x
      rcases mul_eq_zero.mp (hz x) with h | h
      · exact h
      · exact absurd h (hf x).ne'
    have h1 : (1 : ℝ) = 0 := by
      rw [← μ.sum_coe]
      exact Finset.sum_eq_zero fun x _ => hzero x
    exact one_ne_zero h1
  · exact hpos

/-- Expectation only sees the support of the distribution: two functions agreeing
wherever `μ` is nonzero have the same `μ`-average. -/
theorem Ex_congr_ae {μ : FinDist Ω} {f g : Ω → ℝ} (h : ∀ x, μ x ≠ 0 → f x = g x) :
    Ex μ f = Ex μ g := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

/-- **Expectation is invariant under a measure-preserving relabelling**:
`μ(g ∘ e) = μ(g)` for `e` an equivalence preserving `μ`. -/
theorem Ex_comp_equiv {μ : FinDist Ω} (e : Ω ≃ Ω) (he : ∀ x, μ (e x) = μ x) (g : Ω → ℝ) :
    Ex μ (fun x => g (e x)) = Ex μ g := by
  simp only [Ex_apply]
  calc ∑ x, μ x * g (e x) = ∑ x, μ (e x) * g (e x) :=
        Finset.sum_congr rfl fun x _ => by rw [he x]
    _ = ∑ y, μ y * g y := Equiv.sum_comp e (fun y => μ y * g y)

/-- Stationarity says exactly that the chain preserves expectations. -/
theorem Ex_act_of_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : Ex μ (P.act f) = Ex μ f := by
  simp only [Ex, FinKernel.act]
  calc ∑ x, μ x * ∑ y, P x y * f y
      = ∑ x, ∑ y, μ x * P x y * f y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, μ x * P x y * f y := Finset.sum_comm
    _ = ∑ y, μ y * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, h y]

/-! ## Inner product -/

/-- The `L²(μ)` inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`. -/
def ip (μ : FinDist Ω) (f g : Ω → ℝ) : ℝ := ∑ x, μ x * f x * g x

theorem ip_apply (μ : FinDist Ω) (f g : Ω → ℝ) : ip μ f g = ∑ x, μ x * f x * g x := rfl

theorem ip_comm (μ : FinDist Ω) (f g : Ω → ℝ) : ip μ f g = ip μ g f :=
  Finset.sum_congr rfl fun x _ => by ring

theorem ip_self_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ ip μ f f :=
  Finset.sum_nonneg fun x _ => by
    have : μ x * f x * f x = μ x * (f x) ^ 2 := by ring
    rw [this]; exact mul_nonneg (μ.coe_nonneg x) (sq_nonneg _)

theorem ip_eq_Ex_mul (μ : FinDist Ω) (f g : Ω → ℝ) :
    ip μ f g = Ex μ (fun x => f x * g x) :=
  Finset.sum_congr rfl fun x _ => by ring

@[simp] theorem ip_one_right (μ : FinDist Ω) (f : Ω → ℝ) :
    ip μ f (fun _ => 1) = Ex μ f :=
  Finset.sum_congr rfl fun x _ => by ring

/-- The squared `L²(μ)` norm as an expectation of squares. -/
theorem ip_self_eq_Ex_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    ip μ f f = Ex μ (fun x => (f x) ^ 2) :=
  Finset.sum_congr rfl fun x _ => by ring

/-- The squared `L²(μ)` norm of a constant. -/
theorem ip_const (μ : FinDist Ω) (c : ℝ) :
    ip μ (fun _ => c) (fun _ => c) = c ^ 2 := by
  rw [ip_apply]
  have h : ∀ x : Ω, μ x * c * c = μ x * c ^ 2 := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => h x, μ.sum_coe_mul_const]

/-- `ip μ` is a bilinear form, so `psd_cauchy_schwarz` applies to it. -/
theorem isBilin_ip (μ : FinDist Ω) : IsBilin (ip μ) := isBilin_weighted _

/-! ### Explicit bilinearity

`isBilin_ip` states bilinearity in terms of `Pi` addition and scalar
multiplication.  Most computations downstream are much smoother with the
arguments written as explicit lambdas, so we record that form too. -/

theorem ip_add_left (μ : FinDist Ω) (f g h : Ω → ℝ) :
    ip μ (fun x => f x + g x) h = ip μ f h + ip μ g h := by
  simp only [ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_add_right (μ : FinDist Ω) (f g h : Ω → ℝ) :
    ip μ f (fun x => g x + h x) = ip μ f g + ip μ f h := by
  simp only [ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_smul_left (μ : FinDist Ω) (c : ℝ) (f g : Ω → ℝ) :
    ip μ (fun x => c * f x) g = c * ip μ f g := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_smul_right (μ : FinDist Ω) (c : ℝ) (f g : Ω → ℝ) :
    ip μ f (fun x => c * g x) = c * ip μ f g := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Cauchy–Schwarz in `L²(μ)`.** -/
theorem ip_sq_le (μ : FinDist Ω) (f g : Ω → ℝ) :
    ip μ f g ^ 2 ≤ ip μ f f * ip μ g g :=
  psd_cauchy_schwarz (isBilin_ip μ) (ip_comm μ) (ip_self_nonneg μ) f g

/-! ## Variance -/

/-- The variance `Var_μ(f) = μ((f - μ(f))²)`. -/
def Var (μ : FinDist Ω) (f : Ω → ℝ) : ℝ := Ex μ (fun x => (f x - Ex μ f) ^ 2)

theorem Var_apply (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ∑ x, μ x * (f x - Ex μ f) ^ 2 := rfl

theorem Var_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ Var μ f :=
  Ex_nonneg fun _ => sq_nonneg _

/-- `Var_μ(f) = ⟪f, f⟫_μ - (μ f)²`. -/
theorem Var_eq_ip_sub_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ f f - (Ex μ f) ^ 2 := by
  have key : ∀ x, μ x * (f x - Ex μ f) ^ 2
      = μ x * f x * f x - 2 * Ex μ f * (μ x * f x) + (Ex μ f) ^ 2 * μ x := by
    intro x; ring
  rw [Var_apply, Finset.sum_congr rfl fun x _ => key x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [μ.sum_coe]
  simp only [ip, Ex, mul_one]
  ring

@[simp] theorem Var_const (μ : FinDist Ω) (c : ℝ) : Var μ (fun _ => c) = 0 := by
  simp [Var]

/-- Variance is unchanged by subtracting a constant. -/
theorem Var_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Var μ (fun x => f x - c) = Var μ f := by
  simp only [Var, Ex_sub_const]
  exact Finset.sum_congr rfl fun x _ => by ring_nf

/-- Variance only sees the support of the distribution. -/
theorem Var_congr_ae {μ : FinDist Ω} {f g : Ω → ℝ} (h : ∀ x, μ x ≠ 0 → f x = g x) :
    Var μ f = Var μ g := by
  have hE : Ex μ f = Ex μ g := Ex_congr_ae h
  rw [Var, Var, hE]
  exact Ex_congr_ae fun x hx => by rw [h x hx]

/-- The variance of an affine function: `Var(c + d f) = d² Var(f)`. -/
theorem Var_affine (μ : FinDist Ω) (c d : ℝ) (f : Ω → ℝ) :
    Var μ (fun x => c + d * f x) = d ^ 2 * Var μ f := by
  have hE : Ex μ (fun x => c + d * f x) = c + d * Ex μ f := by
    rw [Ex_add μ (fun _ => c) (fun x => d * f x), Ex_const, Ex_smul]
  rw [Var_apply, Var_apply, hE, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- On a mean-zero function, variance is the squared `L²(μ)` norm. -/
theorem Var_eq_ip_self_of_mean_zero {μ : FinDist Ω} {f : Ω → ℝ} (h : Ex μ f = 0) :
    Var μ f = ip μ f f := by
  rw [Var_eq_ip_sub_sq, h]; ring

/-- The *centering* of `f`: `f - μ(f)`.  Has mean zero and the same variance. -/
theorem Ex_center (μ : FinDist Ω) (f : Ω → ℝ) : Ex μ (fun x => f x - Ex μ f) = 0 := by
  rw [Ex_sub_const]; ring

theorem Var_eq_ip_center (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ (fun x => f x - Ex μ f) (fun x => f x - Ex μ f) := by
  rw [← Var_eq_ip_self_of_mean_zero (Ex_center μ f), Var_sub_const]

/-- **Pair form of the variance.**
`Var_μ(f) = ½ ∑_{x, y} μ(x) μ(y) (f x - f y)²`.  This is the identity that makes
variance directly comparable with a Dirichlet form. -/
theorem Var_eq_pair (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
  have expand : ∀ x y : Ω, μ x * μ y * (f x - f y) ^ 2
      = μ y * (μ x * f x * f x) - 2 * (μ x * f x) * (μ y * f y)
        + μ x * (μ y * f y * f y) := by
    intro x y; ring
  have inner : ∀ x : Ω, ∑ y, μ x * μ y * (f x - f y) ^ 2
      = (μ x * f x * f x) - 2 * (μ x * f x) * Ex μ f + μ x * ip μ f f := by
    intro x
    rw [Finset.sum_congr rfl fun y _ => expand x y]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, μ.sum_coe]
    simp only [Ex, ip]
    ring
  have hA : ∑ x, μ x * f x * f x = ip μ f f := rfl
  have hB : ∑ x, 2 * (μ x * f x) * Ex μ f = 2 * Ex μ f * Ex μ f := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rfl
  have hC : ∑ x, μ x * ip μ f f = ip μ f f := by
    rw [← Finset.sum_mul, μ.sum_coe, one_mul]
  calc Var μ f = ip μ f f - (Ex μ f) ^ 2 := Var_eq_ip_sub_sq μ f
    _ = (1 / 2) * (ip μ f f - 2 * Ex μ f * Ex μ f + ip μ f f) := by ring
    _ = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
        congr 1
        rw [Finset.sum_congr rfl fun x _ => inner x, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, hA, hB, hC]

/-- Variance is monotone under a pointwise bound on the pair form; specialised
form used when comparing two distributions on the same space. -/
theorem Var_le_ip_self (μ : FinDist Ω) (f : Ω → ℝ) : Var μ f ≤ ip μ f f := by
  rw [Var_eq_ip_sub_sq]
  nlinarith [sq_nonneg (Ex μ f)]

/-! ## Pushforwards

Two bookkeeping identities for a *rectangular* kernel `K : α → β`, both plain
`Finset.sum_comm`.  They are what makes the law of total variance a three-line
computation. -/

section Push

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Expectation under a pushforward**: `(Kμ)(g) = μ(K g)`.  The kernel may be
rectangular, so this is not `Ex_act_of_stationary`; no stationarity is involved. -/
theorem Ex_push_eq (K : FinKernel α β) (μ : FinDist α) (g : β → ℝ) :
    Ex (K.push μ) g = Ex μ (K.act g) := by
  simp only [Ex_apply, FinKernel.push_apply, FinKernel.act_apply]
  calc ∑ y, (∑ x, μ x * K x y) * g y
      = ∑ y, ∑ x, μ x * K x y * g y :=
        Finset.sum_congr rfl fun y _ => Finset.sum_mul _ _ _
    _ = ∑ x, ∑ y, μ x * K x y * g y := Finset.sum_comm
    _ = ∑ x, μ x * ∑ y, K x y * g y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- The `L²` inner product under a pushforward. -/
theorem ip_push_eq (K : FinKernel α β) (μ : FinDist α) (g h : β → ℝ) :
    ip (K.push μ) g h = Ex μ (K.act (fun y => g y * h y)) := by
  rw [ip_eq_Ex_mul, Ex_push_eq]

end Push

/-! ## χ²-divergence -/

/-- The relative density `ν / μ` of `ν` with respect to `μ`, defined to be `0`
where `μ` vanishes. -/
noncomputable def relDensity (ν μ : FinDist Ω) : Ω → ℝ :=
  fun x => if μ x = 0 then 0 else ν x / μ x

/-- The relative density is nonnegative. -/
theorem relDensity_nonneg (ν μ : FinDist Ω) (x : Ω) : 0 ≤ relDensity ν μ x := by
  by_cases hx : μ x = 0
  · simp [relDensity, hx]
  · simp only [relDensity, if_neg hx]
    exact div_nonneg (ν.coe_nonneg x) (μ.coe_nonneg x)

/-- The χ²-divergence `D_{χ²}(ν ‖ μ) = Var_μ(ν/μ)`. -/
noncomputable def chiSq (ν μ : FinDist Ω) : ℝ := Var μ (relDensity ν μ)

theorem chiSq_nonneg (ν μ : FinDist Ω) : 0 ≤ chiSq ν μ := Var_nonneg _ _

/-- If `ν` is absolutely continuous with respect to `μ` then the relative
density has `μ`-mean `1`. -/
theorem Ex_relDensity {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    Ex μ (relDensity ν μ) = 1 := by
  rw [Ex_apply]
  have : ∀ x : Ω, μ x * relDensity ν μ x = ν x := by
    intro x
    by_cases hx : μ x = 0
    · simp [relDensity, hx, hac x hx]
    · field_simp [relDensity, hx]
  rw [Finset.sum_congr rfl fun x _ => this x, ν.sum_coe]

/-- With absolute continuity, `D_{χ²}(ν ‖ μ) = ∑ x, (ν x - μ x)² / μ x`
in the form `⟪g, g⟫_μ - 1` for `g = ν/μ`. -/
theorem chiSq_eq_ip_sub_one {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    chiSq ν μ = ip μ (relDensity ν μ) (relDensity ν μ) - 1 := by
  rw [chiSq, Var_eq_ip_sub_sq, Ex_relDensity hac]; norm_num

end FinDist

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability.FinDist (Ex Ex_apply Ex_const Ex_add Ex_sub Ex_sum Ex_smul Ex_sub_const
  Ex_nonneg Ex_mono Ex_mono_of_ne_zero Ex_pos_of_pos Ex_congr_ae Ex_comp_equiv Ex_act_of_stationary
  ip ip_apply ip_comm ip_self_nonneg ip_eq_Ex_mul ip_one_right ip_self_eq_Ex_sq ip_const isBilin_ip
  ip_add_left ip_add_right ip_smul_left ip_smul_right ip_sq_le Var Var_apply Var_nonneg
  Var_eq_ip_sub_sq Var_const Var_sub_const Var_congr_ae Var_affine Var_eq_ip_self_of_mean_zero
  Ex_center Var_eq_ip_center Var_eq_pair Var_le_ip_self Ex_push_eq ip_push_eq relDensity
  relDensity_nonneg chiSq chiSq_nonneg Ex_relDensity chiSq_eq_ip_sub_one)

end Arlib.MarkovChains
