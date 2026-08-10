/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spectral independence, without the spectrum

The source monograph defines spectral independence as a bound `λ_max(Ψ) ≤ 1 + η`
on the largest eigenvalue of an influence matrix `Ψ`.  That formulation cannot
be used here (see `docs/dev/MarkovChains-ROADMAP.md` §1.2), and it does not need to be: the monograph
itself proves that the eigenvalue bound is *equivalent* to a semidefinite
ordering between the covariance form of `μ` and the diagonal form of its
marginals, because `Cov = D · Ψ` with `D` diagonal.  We take that ordering as
the definition, which removes `Ψ`, the spectrum, and the diagonal square roots
`D^{±1/2}` from the development in one step.

The state space is the configuration space `V → S` of a spin system with finite
site set `V` and spin set `S`, and the index type of every form below is the set
`V × S` of (site, spin) pairs — the same indexing the monograph uses for the
local walk and for the multi-spin influence matrix.  The measure `μ` is an
arbitrary `FinDist (V → S)`; nothing here needs it to be a Gibbs measure, and
marginals are built directly from `Pr` rather than from the pinning machinery.

The organising identity is `quadForm_Cov`: the covariance form evaluated at `a`
is the *variance* of the linear statistic `σ ↦ ∑_v a (v, σ v)`.  Every other
result is a corollary — positive semidefiniteness of `Cov` becomes
`Var_nonneg`, with no matrix theory anywhere.

* `marg μ` — the pair marginal `μ(σ v = s)`, indexed by `V × S`.
* `joint μ` — the pair joint probability `μ(σ v = s ∧ σ u = t)`; `Psd (joint μ)`
  is immediate from `psd_weighted_rankOne`.
* `Cov μ` — the covariance form `joint − marg ⊗ marg`, with `Cov_symm` and
  `Cov_sum_right` (each row of a block sums to zero, so the form is genuinely
  degenerate — this is why no normalisation by `D^{-1}` is possible or wanted).
* **`quadForm_Cov`** — `quadForm (Cov μ) a = Var μ (σ ↦ ∑_v a (v, σ v))`,
  and hence **`psd_Cov`**.
* **`SpectralIndependence μ η`** — the ordering `Cov μ ⪯ η · diag (marg μ)`.
  *The constant differs from the monograph's by one*: this `η` is the
  monograph's `1 + η`.  See the note below `SpectralIndependence`.
* `SpectralIndependence.mono`, `one_sub_marg_le_of_spectralIndependence` (the
  order forces `η ≥ 1 − μ(σ v = s)`), and the crude universal bound
  **`spectralIndependence_card`** with `η = |V|`.
* **`spectralIndependence_of_pairwiseIndep`** — the calibration point: a measure
  whose coordinates are pairwise independent satisfies the condition with
  `η = 1`, i.e. with the monograph's `η = 0`, and by
  `one_sub_marg_le_of_spectralIndependence` that is optimal as soon as some
  marginal is small.  The proof exhibits `diag (marg μ) − Cov μ` as a sum of
  rank-one forms, one per site.

Everything here is proved from first principles with no `sorry`, and no
eigenvalue appears anywhere.
-/
import Arlib.MarkovChains.Techniques.PsdOrder
import Arlib.MarkovChains.Techniques.TotalVariation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Indicators and linear statistics

A vector `a : V × S → ℝ` acts on a configuration through the indicators of the
events `σ v = s`; the resulting random variable is the general "linear
statistic" of the configuration, and its variance is what the covariance form
below computes. -/

section Indicator

variable {V S : Type*} [DecidableEq S]

/-- The indicator of the event `σ v = s`, as a real-valued function of the
configuration. -/
def spinInd (p : V × S) (σ : V → S) : ℝ := if σ p.1 = p.2 then 1 else 0

end Indicator

section Comb

variable {V S : Type*} [Fintype V] [Fintype S] [DecidableEq S]

/-- The linear statistic attached to `a : V × S → ℝ`. -/
def spinComb (a : V × S → ℝ) (σ : V → S) : ℝ := ∑ p : V × S, a p * spinInd p σ

/-- Only the spin actually taken at each site contributes: the linear statistic
is `σ ↦ ∑_v a (v, σ v)`. -/
theorem spinComb_eq (a : V × S → ℝ) (σ : V → S) : spinComb a σ = ∑ v, a (v, σ v) := by
  rw [spinComb, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [spinInd]
  rw [Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset S)) =>
    (by by_cases h : σ v = s <;> simp [h] :
      a (v, s) * (if σ v = s then (1 : ℝ) else 0) = if σ v = s then a (v, s) else 0)]
  rw [Finset.sum_ite_eq univ (σ v) fun s => a (v, s)]
  simp

end Comb

section SpinMarginals

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Events and marginals -/

/-- The event that the configuration takes the spin `s` at the site `v`. -/
def spinEvent (v : V) (s : S) : Finset (V → S) := univ.filter fun σ => σ v = s

/-- The event that the configuration takes the spin `s` at `v` *and* the spin
`t` at `u`. -/
def spinEvent₂ (v : V) (s : S) (u : V) (t : S) : Finset (V → S) :=
  univ.filter fun σ => σ v = s ∧ σ u = t

/-- The **pair marginal** `marg μ (v, s) = Pr_μ(σ v = s)`, indexed by `V × S`.
This is the diagonal of the spectral-independence comparison, and the stationary
distribution of the monograph's local walk up to normalisation. -/
def marg (μ : FinDist (V → S)) : V × S → ℝ := fun p => Pr μ (spinEvent p.1 p.2)

/-- The **pair joint probability** `joint μ (v,s) (u,t) = Pr_μ(σ v = s ∧ σ u = t)`. -/
def joint (μ : FinDist (V → S)) : (V × S) → (V × S) → ℝ :=
  fun p q => Pr μ (spinEvent₂ p.1 p.2 q.1 q.2)

variable {μ : FinDist (V → S)}

/-- The marginal as an expectation of an indicator. -/
theorem marg_eq_sum (p : V × S) : marg μ p = ∑ σ, μ σ * spinInd p σ := by
  rw [marg, Pr_apply, spinEvent, Finset.sum_filter]
  exact Finset.sum_congr rfl fun σ _ => by
    by_cases h : σ p.1 = p.2 <;> simp [spinInd, h]

/-- The joint probability as an expectation of a product of indicators. -/
theorem joint_eq_sum (p q : V × S) :
    joint μ p q = ∑ σ, μ σ * (spinInd p σ * spinInd q σ) := by
  rw [joint, Pr_apply, spinEvent₂, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : σ p.1 = p.2 <;> by_cases h2 : σ q.1 = q.2 <;> simp [spinInd, h1, h2]

theorem marg_nonneg (p : V × S) : 0 ≤ marg μ p := Pr_nonneg _ _

theorem marg_le_one (p : V × S) : marg μ p ≤ 1 := Pr_le_one _ _

/-- The marginals at a fixed site form a probability distribution on spins. -/
theorem sum_marg (v : V) : ∑ s, marg μ (v, s) = 1 := by
  have h : ∀ s : S, marg μ (v, s) = ∑ σ, μ σ * spinInd (v, s) σ := fun s => marg_eq_sum _
  rw [Finset.sum_congr rfl fun s _ => h s, Finset.sum_comm]
  rw [← μ.sum_coe]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ s : S, spinInd (v, s) σ = 1 := by
    simp only [spinInd]
    rw [Finset.sum_ite_eq univ (σ v) (fun _ => (1 : ℝ))]
    simp
  rw [this, mul_one]

/-- The joint probability of an event with itself is its marginal. -/
theorem joint_self (p : V × S) : joint μ p p = marg μ p := by
  rw [joint_eq_sum, marg_eq_sum]
  exact Finset.sum_congr rfl fun σ _ => by
    by_cases h : σ p.1 = p.2 <;> simp [spinInd, h]

/-- The joint probability is symmetric. -/
theorem joint_symm (p q : V × S) : joint μ p q = joint μ q p := by
  rw [joint_eq_sum, joint_eq_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- The joint probability is a probability. -/
theorem joint_nonneg (p q : V × S) : 0 ≤ joint μ p q := Pr_nonneg _ _

/-- A joint probability is dominated by the marginal of its first coordinate. -/
theorem joint_le_marg (p q : V × S) : joint μ p q ≤ marg μ p := by
  rw [joint_eq_sum, marg_eq_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hind : spinInd q σ ≤ 1 := by
    simp only [spinInd]
    split <;> norm_num
  have hnn : 0 ≤ μ σ * spinInd p σ := by
    refine mul_nonneg (μ.coe_nonneg σ) ?_
    simp only [spinInd]
    split <;> norm_num
  nlinarith

/-- Two different spins at the *same* site are incompatible. -/
theorem joint_eq_zero_of_spin_ne {p q : V × S} (hv : p.1 = q.1) (hs : p.2 ≠ q.2) :
    joint μ p q = 0 := by
  rw [joint_eq_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h1 : σ p.1 = p.2
  · have h2 : ¬ (σ q.1 = q.2) := by rw [← hv, h1]; exact hs
    simp [spinInd, h2]
  · simp [spinInd, h1]

/-! ## Means of linear statistics -/

/-- The mean of a linear statistic is read off the marginals. -/
theorem Ex_spinComb (a : V × S → ℝ) :
    Ex μ (spinComb a) = ∑ p : V × S, a p * marg μ p := by
  calc Ex μ (spinComb a) = ∑ σ, ∑ p : V × S, a p * (μ σ * spinInd p σ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [spinComb, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ p : V × S, ∑ σ, a p * (μ σ * spinInd p σ) := Finset.sum_comm
    _ = ∑ p : V × S, a p * marg μ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.mul_sum, ← marg_eq_sum]

/-- Averaging a function of the spin at one site against `μ` is averaging it
against the marginal at that site. -/
theorem sum_mu_coord (μ : FinDist (V → S)) (v : V) (g : S → ℝ) :
    ∑ σ, μ σ * g (σ v) = ∑ s, marg μ (v, s) * g s := by
  have hterm : ∀ σ : V → S, μ σ * g (σ v) = ∑ s, μ σ * spinInd (v, s) σ * g s := by
    intro σ
    rw [Finset.sum_eq_single (σ v)]
    · simp [spinInd]
    · intro s _ hs
      have hne : ¬ (σ v = s) := fun h => hs h.symm
      simp [spinInd, hne]
    · intro hcon; exact absurd (mem_univ (σ v)) hcon
  calc ∑ σ, μ σ * g (σ v) = ∑ σ, ∑ s, μ σ * spinInd (v, s) σ * g s :=
        Finset.sum_congr rfl fun σ _ => hterm σ
    _ = ∑ s, ∑ σ, μ σ * spinInd (v, s) σ * g s := Finset.sum_comm
    _ = ∑ s, marg μ (v, s) * g s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_mul, ← marg_eq_sum]

/-! ## The covariance form -/

/-- The **covariance form** of `μ` on (site, spin) pairs:
`Cov μ (v,s) (u,t) = Pr(σ v = s ∧ σ u = t) − Pr(σ v = s)·Pr(σ u = t)`.

This is the covariance matrix of the indicator vector of the configuration.  In
the monograph's notation it is `D · Ψ` for the (modified) influence matrix `Ψ`
and the diagonal `D` of marginals; here `Ψ` is never formed. -/
def Cov (μ : FinDist (V → S)) : (V × S) → (V × S) → ℝ :=
  fun p q => joint μ p q - marg μ p * marg μ q

theorem Cov_apply (p q : V × S) : Cov μ p q = joint μ p q - marg μ p * marg μ q := rfl

theorem Cov_symm (p q : V × S) : Cov μ p q = Cov μ q p := by
  simp only [Cov, joint_symm p q]; ring

theorem Cov_self (p : V × S) : Cov μ p p = marg μ p - marg μ p * marg μ p := by
  rw [Cov_apply, joint_self]

/-- **Each block row of the covariance form sums to zero.**  Consequently the
form annihilates every vector that is constant on the spins at each site: the
covariance form is always degenerate, which is exactly why the comparison with
`diag (marg μ)` — rather than any normalisation by `D^{-1}` — is the right
statement. -/
theorem Cov_sum_right (p : V × S) (u : V) : ∑ t, Cov μ p (u, t) = 0 := by
  have h1 : ∑ t : S, joint μ p (u, t) = marg μ p := by
    have : ∀ t : S, joint μ p (u, t) = ∑ σ, μ σ * (spinInd p σ * spinInd (u, t) σ) :=
      fun t => joint_eq_sum _ _
    rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_comm, marg_eq_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hone : ∑ t : S, spinInd (u, t) σ = 1 := by
      simp only [spinInd]
      rw [Finset.sum_ite_eq univ (σ u) (fun _ => (1 : ℝ))]
      simp
    calc ∑ t : S, μ σ * (spinInd p σ * spinInd (u, t) σ)
        = (μ σ * spinInd p σ) * ∑ t : S, spinInd (u, t) σ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = μ σ * spinInd p σ := by rw [hone, mul_one]
  have h2 : ∑ t : S, marg μ p * marg μ (u, t) = marg μ p := by
    rw [← Finset.mul_sum, sum_marg, mul_one]
  simp only [Cov]
  rw [Finset.sum_sub_distrib, h1, h2, sub_self]

/-- The joint form is positive semidefinite: it is the `μ`-average of the
rank-one forms of the indicator vectors. -/
theorem psd_joint (μ : FinDist (V → S)) : Psd (joint μ) := by
  have h : joint μ = fun p q : V × S =>
      ∑ σ ∈ (univ : Finset (V → S)), μ σ * (spinInd p σ * spinInd q σ) := by
    funext p q; exact joint_eq_sum p q
  rw [h]
  exact psd_weighted_rankOne _ (fun σ _ => μ.coe_nonneg σ) (fun σ p => spinInd p σ)

/-- The quadratic form of `joint μ` is the second moment of the linear
statistic. -/
theorem quadForm_joint (a : V × S → ℝ) :
    quadForm (joint μ) a = ∑ σ, μ σ * (spinComb a σ) ^ 2 := by
  have h : joint μ = fun p q : V × S =>
      ∑ σ ∈ (univ : Finset (V → S)), μ σ * (spinInd p σ * spinInd q σ) := by
    funext p q; exact joint_eq_sum p q
  rw [h, quadForm_weighted_rankOne]
  rfl

/-- **The covariance form is the variance of a linear statistic.**

`quadForm (Cov μ) a = Var_μ (σ ↦ ∑_v a (v, σ v))`.  This single identity is the
whole content of the module: it replaces every appeal to the spectral theory of
the covariance matrix by an appeal to the elementary properties of variance. -/
theorem quadForm_Cov (a : V × S → ℝ) : quadForm (Cov μ) a = Var μ (spinComb a) := by
  have hip : ip μ (spinComb a) (spinComb a) = ∑ σ, μ σ * (spinComb a σ) ^ 2 :=
    Finset.sum_congr rfl fun σ _ => by ring
  rw [Var_eq_ip_sub_sq, hip, Ex_spinComb]
  have hcov : Cov μ = fun p q : V × S => joint μ p q - marg μ p * marg μ q := rfl
  rw [hcov, quadForm_sub, quadForm_rankOne, quadForm_joint]

/-- **The covariance form is positive semidefinite** — because variances are
nonnegative.  No matrix theory, no spectral theorem. -/
theorem psd_Cov (μ : FinDist (V → S)) : Psd (Cov μ) :=
  psd_of_nonneg fun a => by rw [quadForm_Cov]; exact Var_nonneg _ _

/-- Cauchy–Schwarz for the covariance form, from `quadForm_bilin_sq_le`. -/
theorem bilinOf_Cov_sq_le (u v : V × S → ℝ) :
    bilinOf (Cov μ) u v ^ 2 ≤ quadForm (Cov μ) u * quadForm (Cov μ) v :=
  quadForm_bilin_sq_le Cov_symm (psd_Cov μ) u v

end SpinMarginals

/-! ## Spectral independence -/

section SI

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {μ : FinDist (V → S)}

/-- **Spectral independence, as a semidefinite ordering.**

`μ` is `η`-spectrally independent when the covariance form is dominated by `η`
times the diagonal form of the marginals.

*Why this is the eigenvalue-free form.*  On the index set `V × S` the influence
matrix is `Ψ((v,s),(u,t)) = μ(σ u = t | σ v = s) − μ(σ u = t)`, and multiplying
by the marginal at `(v,s)` gives exactly `Cov = D · Ψ` for `D = diag (marg μ)`.
Hence `D^{1/2} Ψ D^{-1/2} ⪯ η I`, i.e. `λ_max(Ψ) ≤ η`, is literally
`Cov ⪯ η · D`.  Nothing is lost and `Ψ`, the spectrum and the square roots
`D^{±1/2}` all disappear.

*Constant convention.*  The monograph's condition is `λ_max ≤ 1 + η`, so the `η`
here is the monograph's `1 + η`; a product measure satisfies
`SpectralIndependence μ 1`, the monograph's `0`-spectral independence.  The
shift is unavoidable once the eigenvalue is dropped, because `Ψ` has unit
diagonal while `Cov` does not, and carrying the monograph's normalisation would
mean writing `1 + η` at every use site with no gain.

*Relation to the monograph's `n × n` matrix (two spins).*  For `S` a two-element
type the condition above is *equivalent*, with the same constant, to the
monograph's `Cov_μ ⪯ (1+η) diag(Var_μ)` on the `|V| × |V|` covariance matrix of
the indicators `X_v = 1[σ v = 1]`: the quadratic form on `V × S` depends on `a`
only through the differences `b v = a (v,1) − a (v,0)`, and minimising
`p·a(v,1)² + (1−p)·a(v,0)²` at fixed `b v` returns exactly `Var(X_v)·(b v)²`.
So this is the monograph's *spectral* independence, not the weaker notion
attached to `diag` of the means in the `n × n` indexing. -/
def SpectralIndependence (μ : FinDist (V → S)) (η : ℝ) : Prop :=
  PsdLe (Cov μ) (η • diag (marg μ))

theorem spectralIndependence_iff (η : ℝ) :
    SpectralIndependence μ η ↔ ∀ a, quadForm (Cov μ) a ≤ η * ∑ p : V × S, marg μ p * a p ^ 2 := by
  constructor
  · intro h a; have := h a; rwa [quadForm_smul, quadForm_diag] at this
  · intro h a; rw [quadForm_smul, quadForm_diag]; exact h a

/-- Spectral independence is monotone in the constant. -/
theorem SpectralIndependence.mono {η η' : ℝ} (h : SpectralIndependence μ η) (hle : η ≤ η') :
    SpectralIndependence μ η' := by
  refine (spectralIndependence_iff η').mpr fun a => ?_
  have h₁ := (spectralIndependence_iff η).mp h a
  have h₂ : 0 ≤ ∑ p : V × S, marg μ p * a p ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (marg_nonneg p) (sq_nonneg _)
  nlinarith

/-- **The ordering forces `η ≥ 1 − μ(σ v = s)` at every charged pair.**

Evaluating the definition at a single basis vector already pins the constant
down: a distribution with a small marginal cannot be spectrally independent with
a small constant.  In particular no measure charging two spins at a site
satisfies `SpectralIndependence μ η` for `η < 1/2`, so the value `η = 1` reached
by product measures is close to optimal. -/
theorem one_sub_marg_le_of_spectralIndependence {η : ℝ} (h : SpectralIndependence μ η)
    {p : V × S} (hp : 0 < marg μ p) : 1 - marg μ p ≤ η := by
  have hle := h (fun q => if q = p then (1 : ℝ) else 0)
  rw [quadForm_single, quadForm_smul, quadForm_single, diag_self, Cov_self] at hle
  nlinarith [hle, hp]

/-- **Spectral independence forces a nonnegative constant.**

Evaluating `Cov μ ⪯ η · diag (marg μ)` at the all-ones vector gives
`0 ≤ η · |V|`, because the linear statistic of the all-ones vector is the
constant `|V|` and constants have variance zero, while `∑_p marg μ p = |V|`.

This is worth having because it removes a hypothesis downstream: the side
condition `γ_j ≤ 2` of the Improved Random Walk Theorem
(`Chains.SpectralIndependenceMixing`) needs `0 ≤ η`, and it is free.  Compare
`one_sub_marg_le_of_spectralIndependence`, which is the same evaluation at a
basis vector. -/
theorem nonneg_of_spectralIndependence [Nonempty V] {μ : FinDist (V → S)} {η : ℝ}
    (h : SpectralIndependence μ η) : 0 ≤ η := by
  have h1 := (spectralIndependence_iff η).mp h (fun _ => 1)
  have h2 : quadForm (Cov μ) (fun _ => (1 : ℝ)) = 0 := by
    rw [quadForm_Cov]
    have hcomb : spinComb (fun _ : V × S => (1 : ℝ)) = fun _ => ((Fintype.card V : ℝ)) := by
      funext σ
      rw [spinComb_eq]
      simp
    rw [hcomb, Var_const]
  have h3 : (∑ p : V × S, marg μ p * (1 : ℝ) ^ 2) = (Fintype.card V : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp [sum_marg]
  rw [h2, h3] at h1
  have hc : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

/-! ### The universal bound

Some constant always works.  Cauchy–Schwarz on the `|V|`-term sum defining the
linear statistic gives `η = |V|`, and that bound is **attained**: for `μ`
uniform on the two constant configurations the ratio is `|V|`, as the test
vector `a (v, true) = 1/2`, `a (v, false) = -1/2` shows — variance `|V|²/4`
against diagonal form `|V|/4`.

(An earlier version of this comment said `|V|/2`.  That is wrong, and
disprovably so: `Chains/TwoSiteSpectralIndependence.lean` proves
`twoSiteConst_eta_eq_card` — the constant is exactly `2` at `|V| = 2` — together
with `twoSiteConst_not_spectralIndependence_one`, which refutes the `η = 1` that
`|V|/2` would predict there.) -/

/-- **Every distribution is `|V|`-spectrally independent.** -/
theorem spectralIndependence_card (μ : FinDist (V → S)) :
    SpectralIndependence μ (Fintype.card V) := by
  refine (spectralIndependence_iff _).mpr fun a => ?_
  set C : ℝ := (Fintype.card V : ℝ) with hC
  have hip : ip μ (spinComb a) (spinComb a) = ∑ σ, μ σ * (spinComb a σ) ^ 2 :=
    Finset.sum_congr rfl fun σ _ => by ring
  have hb : ∀ σ : V → S, (spinComb a σ) ^ 2 ≤ C * ∑ v, a (v, σ v) ^ 2 := by
    intro σ; rw [spinComb_eq]; exact sq_sum_le_card_mul_sum_sq _
  have hstep : ∑ σ, μ σ * (spinComb a σ) ^ 2
      ≤ ∑ σ, μ σ * (C * ∑ v, a (v, σ v) ^ 2) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hb σ) (μ.coe_nonneg σ)
  have e1 : ∑ σ, μ σ * (C * ∑ v, a (v, σ v) ^ 2) = C * ∑ σ, ∑ v, μ σ * a (v, σ v) ^ 2 := by
    have inner : ∀ σ : V → S, μ σ * (C * ∑ v, a (v, σ v) ^ 2)
        = C * ∑ v, μ σ * a (v, σ v) ^ 2 := by
      intro σ
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_congr rfl fun σ _ => inner σ, ← Finset.mul_sum]
  have e3 : ∀ v : V, ∑ σ, μ σ * a (v, σ v) ^ 2 = ∑ s, marg μ (v, s) * a (v, s) ^ 2 :=
    fun v => sum_mu_coord μ v fun s => a (v, s) ^ 2
  have e2 : ∑ σ, ∑ v, μ σ * a (v, σ v) ^ 2 = ∑ p : V × S, marg μ p * a p ^ 2 := by
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun v _ => e3 v
  rw [quadForm_Cov]
  calc Var μ (spinComb a) ≤ ip μ (spinComb a) (spinComb a) := Var_le_ip_self _ _
    _ = ∑ σ, μ σ * (spinComb a σ) ^ 2 := hip
    _ ≤ ∑ σ, μ σ * (C * ∑ v, a (v, σ v) ^ 2) := hstep
    _ = C * ∑ p : V × S, marg μ p * a p ^ 2 := by rw [e1, e2]

/-! ### Calibration: pairwise independent coordinates

The definition is only worth anything if the extreme case comes out with the
extreme constant.  It does, and with the weakest possible hypothesis: only
*pairwise* independence of the coordinates is used, since the covariance form
sees nothing else.  The proof exhibits `diag (marg μ) − Cov μ` as a sum of one
rank-one form per site, so the ordering is not merely true but manifestly so. -/

/-- The coordinates of `μ` are pairwise independent. -/
def PairwiseIndep (μ : FinDist (V → S)) : Prop :=
  ∀ p q : V × S, p.1 ≠ q.1 → joint μ p q = marg μ p * marg μ q

/-- Under pairwise independence the covariance form is block diagonal, and its
defect from the diagonal of marginals is a sum of rank-one forms, one per
site. -/
theorem diag_sub_Cov_eq_blocks (h : PairwiseIndep μ) :
    (fun p q : V × S => diag (marg μ) p q - Cov μ p q)
      = fun p q : V × S => ∑ k : V, (1 : ℝ) *
          ((if p.1 = k then marg μ p else 0) * (if q.1 = k then marg μ q else 0)) := by
  funext p q
  have hrhs : (∑ k : V, (1 : ℝ) *
      ((if p.1 = k then marg μ p else 0) * (if q.1 = k then marg μ q else 0)))
      = marg μ p * (if q.1 = p.1 then marg μ q else 0) := by
    rw [Finset.sum_eq_single p.1]
    · rw [if_pos rfl]; ring
    · intro k _ hk; rw [if_neg (Ne.symm hk)]; ring
    · intro hcon; exact absurd (mem_univ p.1) hcon
  rw [hrhs, Cov_apply]
  by_cases hv : p.1 = q.1
  · rw [if_pos hv.symm]
    have hdj : diag (marg μ) p q = joint μ p q := by
      by_cases hpq : p = q
      · subst hpq; rw [diag_self, joint_self]
      · have hs : p.2 ≠ q.2 := by
          intro hs2
          exact hpq (Prod.ext hv hs2)
        rw [diag_apply, if_neg hpq, joint_eq_zero_of_spin_ne hv hs]
    rw [hdj]; ring
  · rw [if_neg fun hc => hv hc.symm]
    have hpq : p ≠ q := fun hc => hv (congrArg Prod.fst hc)
    rw [diag_apply, if_neg hpq, h p q hv]
    ring

/-- **A pairwise independent measure is `1`-spectrally independent** — that is,
`0`-spectrally independent in the monograph's normalisation.  This is the
calibration point for the definition: `η = 1` is the smallest constant the
convention allows for a genuinely random measure, by
`one_sub_marg_le_of_spectralIndependence`. -/
theorem spectralIndependence_of_pairwiseIndep (h : PairwiseIndep μ) :
    SpectralIndependence μ 1 := by
  intro a
  have h0 : 0 ≤ quadForm (fun p q : V × S => diag (marg μ) p q - Cov μ p q) a := by
    rw [diag_sub_Cov_eq_blocks h, quadForm_weighted_rankOne]
    exact Finset.sum_nonneg fun k _ => by positivity
  rw [quadForm_sub] at h0
  rw [quadForm_smul, one_mul]
  linarith

end SI

end Arlib.MarkovChains

