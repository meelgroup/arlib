/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two-site spin system: the spectral independence constant, computed exactly

The whole spectral-independence development — `Techniques.SpectralIndependence`,
`Techniques.LocalSpectralIndependence`, `Techniques.SpectralIndependenceConverse`
— was instantiated only at *product* measures
(`Chains.ProductSpectralIndependence`), where the covariance form is block
diagonal, the constant is the degenerate `η = 1`, and the local walk's gap is
`1`.  Nothing exhibited a genuinely correlated measure with a computed constant,
so nothing tested whether those definitions have the sharp value on a system
where the sharp value is known.  Per `docs/dev/MarkovChains-ROADMAP.md` §1.1 that is the job of a
`Chains/` module, and this is it.

The system is the smallest one that can be correlated at all: two sites
(`V = Bool`), two spins (`S = Bool`), and an arbitrary distribution on the four
configurations.  Everything is computed in closed form, and the exact spectral
independence constant turns out to be

    **η = 1 + |ρ|,   ρ = (μ₀₀μ₁₁ − μ₀₁μ₁₀) / √((μ₀₀+μ₀₁)(μ₁₀+μ₁₁)(μ₀₀+μ₁₀)(μ₀₁+μ₁₁))**

— one plus the modulus of the Pearson correlation of the two spin indicators,
whose numerator is the determinant of the `2 × 2` table and whose denominator is
the geometric mean of the four line sums.  Since `|ρ| ≤ 1` (Cauchy–Schwarz for
`Cov`, itself the discriminant argument of `Techniques.Bilinear`, with no
eigenvalue), the constant lies in `[1, 2] = [1, |V|]` and **both endpoints are
attained**: `η = 1` exactly in the product case, and `η = 2` at perfect
correlation.  So the two general bounds bracketing it,
`spectralIndependence_of_pairwiseIndep` (`η = 1`) and
`spectralIndependence_card` (`η = |V|`), are each sharp, and neither is sharp
anywhere else.

## What the calibration found

*One claim in `Techniques.SpectralIndependence` is wrong.*  The docstring of
`spectralIndependence_card` says that "for `μ` uniform on the two constant
configurations the ratio is `|V|/2`".  It is `|V|`.  At `|V| = 2` the claim
predicts `η = 1`, and `twoSiteConst_not_spectralIndependence_one` proves that
`SpectralIndependence μ 1` is *false* for that measure, while
`twoSiteConst_eta_eq_card` proves the exact constant is `2 = |V|`.  The bound
`spectralIndependence_card` is therefore attained, not merely valid; the
surrounding text ("that is the right order of magnitude") stands.

*The local walk exists at two sites, and is not degenerate.*  `pinLocalWalk`
requires `|Λ| + 1 < |V|`, so at `|V| = 2` only the empty pinning qualifies — but
it does qualify (`twoSite_card_succ_lt`), and the resulting Poincaré constant
`1 − |ρ|` runs over the whole of `[0, 1]` as the correlation varies.  At perfect
correlation it is `0`, which is right: there `Q_∅` is reducible.

## Main declarations

* `twoSiteCfg`, `twoSiteEquiv`, `twoSite_sum_config` — the four configurations
  and how to sum over them.
* `twoSite_marg_left`, `twoSite_marg_right`, `twoSite_joint` — `marg` and
  `joint` as the line sums and the entries of the `2 × 2` table.
* `twoSiteVar`, `twoSiteCov`, with `twoSite_var_left`, `twoSite_var_right` and
  **`twoSite_cov_eq_det`** — the covariance is the determinant `μ₀₀μ₁₁ − μ₀₁μ₁₀`.
* **`twoSite_quadForm_Cov`** — the `4 × 4` covariance form in closed form,
  `V₀b₀² + 2Cb₀b₁ + V₁b₁²`, obtained from `quadForm_Cov` (the form *is* the
  variance of the linear statistic) rather than by expanding the array.
* `twoSite_sum_marg_sq` and `twoSiteTest` — the diagonal form split into the
  part the covariance form sees and the part it cannot, and the extremal vectors
  where the second part vanishes.
* **`twoSite_cov_sq_le`** — Cauchy–Schwarz for the two entries, from
  `PsdOrder.bilinOf_single` and `SpectralIndependence.bilinOf_Cov_sq_le`.
* **`twoSiteCorr`**, **`twoSiteEta`** — `ρ` and `η = 1 + |ρ|`, with
  `twoSite_corr_eq` in the four probabilities, **`twoSite_corr_gibbs`** in the
  four *unnormalised* weights (the partition function cancels), and
  `twoSite_abs_corr_le_one`.
* **`twoSite_spectralIndependence`** (`η` works),
  **`twoSite_eta_le_of_spectralIndependence`** (`η` is least, away from a
  deterministic site) and **`twoSite_spectralIndependence_iff`** — the constant
  is computed, not merely bounded.  `twoSiteConst_zero_degenerate` shows the
  non-degeneracy hypothesis of the lower bound cannot be dropped.
* **`twoSite_eta_eq_one_iff_pairwiseIndep`** and `twoSite_eta_eq_one_iff_det` —
  the first sanity check: `η = 1` **iff** the measure is a product, calibrating
  `Chains.ProductSpectralIndependence`.
* `twoSiteConst`, **`twoSiteConst_eta`**, `twoSiteConst_eta_eq_card`,
  `twoSiteConst_not_spectralIndependence_one` — the second sanity check: the
  measure on the two constant configurations has `ρ = 1`, `η = 2 = |V|`, and
  refutes `Cov ⪯ 1·diag (marg)`.
* `twoSite_eta_mem_Icc`, `twoSite_spectralIndependence_card_check` — the
  constant lies in `[1, |V|]`, as it must.
* **`twoSite_dirichlet_pinLocalWalk`** — `ℰ_{Q_∅}(f) = ½∑_{s,t} μ(s,t)(f(0,s) −
  f(1,t))²`, computed from the definition of `pinLocalWalk` and
  `dirichlet_self_eq_pair` alone, together with `twoSite_Var_pinDist`.
* **`twoSite_pinLocalWalk_audit`** — the same Poincaré constant `1 − |ρ|` proved
  twice: once through
  `spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty`, once from the
  closed forms with no `Cov` and no `quadForm` anywhere in the proof.
  `twoSite_spectralGapAtLeast_pinLocalWalk_iff` shows `1 − |ρ|` is exact.

*Not done here.*  This module is not imported by `Arlib/MarkovChains.lean`,
because it was written under a rule forbidding edits to existing files; adding
the import is a one-line change that should be made.

Everything here is proved from first principles with no `sorry`, and no
eigenvalue, spectrum or Hermitian matrix appears anywhere.
-/
import Arlib.MarkovChains.Techniques.SpectralIndependenceConverse

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The four configurations -/

/-- The configuration of the two-site system carrying the spin `s` at the site
`false` and the spin `t` at the site `true`. -/
def twoSiteCfg (s t : Bool) : Bool → Bool := fun v => cond v t s

@[simp] theorem twoSiteCfg_false (s t : Bool) : twoSiteCfg s t false = s := rfl

@[simp] theorem twoSiteCfg_true (s t : Bool) : twoSiteCfg s t true = t := rfl

/-- Every configuration is one of the four. -/
theorem twoSiteCfg_eta (σ : Bool → Bool) : twoSiteCfg (σ false) (σ true) = σ := by
  funext v; cases v <;> rfl

/-- The configuration space of the two-site, two-spin system is `Bool × Bool`. -/
def twoSiteEquiv : Bool × Bool ≃ (Bool → Bool) where
  toFun p := twoSiteCfg p.1 p.2
  invFun σ := (σ false, σ true)
  left_inv _ := rfl
  right_inv σ := twoSiteCfg_eta σ

/-- **A sum over configurations, written out.** -/
theorem twoSite_sum_config (f : (Bool → Bool) → ℝ) :
    ∑ σ, f σ = f (twoSiteCfg false false) + f (twoSiteCfg false true)
      + f (twoSiteCfg true false) + f (twoSiteCfg true true) := by
  rw [← Equiv.sum_comp twoSiteEquiv f]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, twoSiteEquiv]
  ring

/-! ## The four probabilities -/

section Table

variable (μ : FinDist (Bool → Bool))

/-- The four configuration probabilities sum to one. -/
theorem twoSite_sum_mu :
    μ (twoSiteCfg false false) + μ (twoSiteCfg false true)
      + μ (twoSiteCfg true false) + μ (twoSiteCfg true true) = 1 := by
  rw [← twoSite_sum_config (fun σ => μ σ)]
  exact μ.sum_coe

/-- **The marginal at the site `false`**: a row sum of the `2 × 2` table. -/
theorem twoSite_marg_left (s : Bool) :
    marg μ (false, s) = μ (twoSiteCfg s false) + μ (twoSiteCfg s true) := by
  rw [marg_eq_sum, twoSite_sum_config]
  cases s <;> simp [spinInd]

/-- **The marginal at the site `true`**: a column sum of the `2 × 2` table. -/
theorem twoSite_marg_right (t : Bool) :
    marg μ (true, t) = μ (twoSiteCfg false t) + μ (twoSiteCfg true t) := by
  rw [marg_eq_sum, twoSite_sum_config]
  cases t <;> simp [spinInd]

/-- **The joint law at the two distinct sites is the table itself.** -/
theorem twoSite_joint (s t : Bool) :
    joint μ (false, s) (true, t) = μ (twoSiteCfg s t) := by
  rw [joint_eq_sum, twoSite_sum_config]
  cases s <;> cases t <;> simp [spinInd]

end Table

/-! ## The three numbers that decide everything -/

section Moments

variable (μ : FinDist (Bool → Bool))

/-- The **variance of the spin indicator at a site**, read off the covariance
form as the diagonal entry `Cov μ (v,true) (v,true)`. -/
def twoSiteVar (v : Bool) : ℝ := Cov μ (v, true) (v, true)

/-- The **covariance of the two spin indicators**, read off the covariance form
as the cross entry `Cov μ (false,true) (true,true)`. -/
def twoSiteCov : ℝ := Cov μ (false, true) (true, true)

/-- The variance at the site `false`, in the four probabilities. -/
theorem twoSite_var_left :
    twoSiteVar μ false
      = (μ (twoSiteCfg true false) + μ (twoSiteCfg true true))
        * (μ (twoSiteCfg false false) + μ (twoSiteCfg false true)) := by
  have hsum := twoSite_sum_mu μ
  rw [twoSiteVar, Cov_self, twoSite_marg_left]
  linear_combination (-(μ (twoSiteCfg true false) + μ (twoSiteCfg true true))) * hsum

/-- The variance at the site `true`, in the four probabilities. -/
theorem twoSite_var_right :
    twoSiteVar μ true
      = (μ (twoSiteCfg false true) + μ (twoSiteCfg true true))
        * (μ (twoSiteCfg false false) + μ (twoSiteCfg true false)) := by
  have hsum := twoSite_sum_mu μ
  rw [twoSiteVar, Cov_self, twoSite_marg_right]
  linear_combination (-(μ (twoSiteCfg false true) + μ (twoSiteCfg true true))) * hsum

/-- **The covariance is the determinant of the `2 × 2` table.**

`Cov μ (false,true) (true,true) = μ₀₀·μ₁₁ − μ₀₁·μ₁₀`.

Every normalisation cancels: the four cross-terms of
`joint − marg·marg` collapse to the determinant using only that the four
probabilities sum to one.  This is the number that makes the two-site system
correlated, and it is the only place the product structure can fail. -/
theorem twoSite_cov_eq_det :
    twoSiteCov μ
      = μ (twoSiteCfg false false) * μ (twoSiteCfg true true)
        - μ (twoSiteCfg false true) * μ (twoSiteCfg true false) := by
  have hsum := twoSite_sum_mu μ
  rw [twoSiteCov, Cov_apply, twoSite_joint, twoSite_marg_left, twoSite_marg_right]
  linear_combination (-(μ (twoSiteCfg true true))) * hsum

/-- Both site variances are nonnegative. -/
theorem twoSite_var_nonneg (v : Bool) : 0 ≤ twoSiteVar μ v := by
  rw [twoSiteVar, Cov_self]
  nlinarith [marg_nonneg (μ := μ) (v, true), marg_le_one (μ := μ) (v, true)]

end Moments

/-! ## The covariance form of the two-site system, exactly -/

section QuadForm

/-- The **spin gap** of a test vector `x : (site, spin) → ℝ` at a site: the only
feature of `x` that the covariance form can see. -/
def twoSiteDiff (x : Bool × Bool → ℝ) (v : Bool) : ℝ := x (v, true) - x (v, false)

variable (μ : FinDist (Bool → Bool)) (x : Bool × Bool → ℝ)

/-- The linear statistic of the two-site system, evaluated on a configuration. -/
theorem twoSite_spinComb (s t : Bool) :
    spinComb x (twoSiteCfg s t) = x (false, s) + x (true, t) := by
  rw [spinComb_eq, Fintype.sum_bool]
  simp only [twoSiteCfg_false, twoSiteCfg_true]
  ring

/-- **The covariance form of the two-site system, in closed form.**

`quadForm (Cov μ) x = V₀·b₀² + 2·C·b₀b₁ + V₁·b₁²`, with `b_v = twoSiteDiff x v`,
`V_v = twoSiteVar μ v` and `C = twoSiteCov μ`.  The form is a `4 × 4` array on
`(site, spin)` pairs, but it depends on `x` only through the two spin gaps —
which is `Cov_sum_right`, the degeneracy of the covariance form, made explicit.
The proof is `quadForm_Cov`: the form *is* the variance of the linear statistic
`σ ↦ x(false, σ false) + x(true, σ true)`, and that variance is expanded over the
four configurations. -/
theorem twoSite_quadForm_Cov :
    quadForm (Cov μ) x
      = twoSiteVar μ false * twoSiteDiff x false ^ 2
        + 2 * twoSiteCov μ * (twoSiteDiff x false * twoSiteDiff x true)
        + twoSiteVar μ true * twoSiteDiff x true ^ 2 := by
  have hip : ip μ (spinComb x) (spinComb x)
      = μ (twoSiteCfg false false) * (x (false, false) + x (true, false)) ^ 2
        + μ (twoSiteCfg false true) * (x (false, false) + x (true, true)) ^ 2
        + μ (twoSiteCfg true false) * (x (false, true) + x (true, false)) ^ 2
        + μ (twoSiteCfg true true) * (x (false, true) + x (true, true)) ^ 2 := by
    rw [show ip μ (spinComb x) (spinComb x) = ∑ σ, μ σ * spinComb x σ * spinComb x σ from rfl,
      twoSite_sum_config]
    simp only [twoSite_spinComb]
    ring
  have hex : Ex μ (spinComb x)
      = μ (twoSiteCfg false false) * (x (false, false) + x (true, false))
        + μ (twoSiteCfg false true) * (x (false, false) + x (true, true))
        + μ (twoSiteCfg true false) * (x (false, true) + x (true, false))
        + μ (twoSiteCfg true true) * (x (false, true) + x (true, true)) := by
    rw [show Ex μ (spinComb x) = ∑ σ, μ σ * spinComb x σ from rfl, twoSite_sum_config]
    simp only [twoSite_spinComb]
  have h00 : μ (twoSiteCfg false false)
      = 1 - μ (twoSiteCfg false true) - μ (twoSiteCfg true false)
        - μ (twoSiteCfg true true) := by
    have := twoSite_sum_mu μ; linarith
  rw [quadForm_Cov, Var_eq_ip_sub_sq, hip, hex, twoSite_var_left, twoSite_var_right,
    twoSite_cov_eq_det, twoSiteDiff, twoSiteDiff, h00]
  ring

end QuadForm

/-! ## The diagonal form of the marginals -/

section Diagonal

variable (μ : FinDist (Bool → Bool)) (x : Bool × Bool → ℝ)

/-- The **mean of a test vector at a site**, against the marginal there. -/
def twoSiteMean (v : Bool) : ℝ :=
  marg μ (v, false) * x (v, false) + marg μ (v, true) * x (v, true)

/-- The site variance is the product of the two marginals at that site. -/
theorem twoSite_var_eq_marg_mul (v : Bool) :
    twoSiteVar μ v = marg μ (v, false) * marg μ (v, true) := by
  have h := sum_marg (μ := μ) v
  simp only [Fintype.sum_bool] at h
  rw [twoSiteVar, Cov_self]
  linear_combination (-(marg μ (v, true))) * h

/-- **The diagonal form, in closed form.**

`∑_p marg p · x p² = ∑_v (V_v·b_v² + m_v²)`, an exact decomposition of the
second moment into the part the covariance form sees (the spin gap `b_v`) and
the part it cannot (the site mean `m_v`).  Since the covariance form depends on
`x` only through the gaps, the whole optimisation defining the spectral
independence constant is the choice of the `b_v` with the means set to zero. -/
theorem twoSite_sum_marg_sq :
    ∑ p : Bool × Bool, marg μ p * x p ^ 2
      = (twoSiteVar μ false * twoSiteDiff x false ^ 2 + twoSiteMean μ x false ^ 2)
        + (twoSiteVar μ true * twoSiteDiff x true ^ 2 + twoSiteMean μ x true ^ 2) := by
  have hL := sum_marg (μ := μ) false
  have hR := sum_marg (μ := μ) true
  simp only [Fintype.sum_bool] at hL hR
  rw [Fintype.sum_prod_type, twoSite_var_eq_marg_mul, twoSite_var_eq_marg_mul]
  simp only [Fintype.sum_bool, twoSiteDiff, twoSiteMean]
  linear_combination
    (-(marg μ (false, true) * x (false, true) ^ 2
      + marg μ (false, false) * x (false, false) ^ 2)) * hL
    + (-(marg μ (true, true) * x (true, true) ^ 2
      + marg μ (true, false) * x (true, false) ^ 2)) * hR

/-- Dropping the site means: the diagonal form dominates the gap part. -/
theorem twoSite_sum_marg_sq_ge :
    twoSiteVar μ false * twoSiteDiff x false ^ 2
        + twoSiteVar μ true * twoSiteDiff x true ^ 2
      ≤ ∑ p : Bool × Bool, marg μ p * x p ^ 2 := by
  rw [twoSite_sum_marg_sq]
  linarith [sq_nonneg (twoSiteMean μ x false), sq_nonneg (twoSiteMean μ x true)]

end Diagonal

/-! ## The extremal test vectors

The bound above is attained exactly when both site means vanish, and the vectors
with prescribed spin gaps and vanishing means form a two-parameter family: at
each site, put `−marg(v,true)·c v` on the spin `false` and `marg(v,false)·c v` on
the spin `true`.  These are the vectors that make the spectral independence
constant *sharp*, and they are the only computation that the lower bound needs. -/

section Test

variable (μ : FinDist (Bool → Bool)) (c : Bool → ℝ)

/-- The **centred test vector** with prescribed spin gaps `c`. -/
def twoSiteTest : Bool × Bool → ℝ :=
  fun p => cond p.2 (marg μ (p.1, false) * c p.1) (-(marg μ (p.1, true) * c p.1))

@[simp] theorem twoSiteTest_true (v : Bool) :
    twoSiteTest μ c (v, true) = marg μ (v, false) * c v := rfl

@[simp] theorem twoSiteTest_false (v : Bool) :
    twoSiteTest μ c (v, false) = -(marg μ (v, true) * c v) := rfl

/-- The test vector has the prescribed spin gaps. -/
theorem twoSiteDiff_test (v : Bool) : twoSiteDiff (twoSiteTest μ c) v = c v := by
  have h := sum_marg (μ := μ) v
  simp only [Fintype.sum_bool] at h
  rw [twoSiteDiff, twoSiteTest_true, twoSiteTest_false]
  linear_combination c v * h

/-- The test vector is centred at every site. -/
theorem twoSiteMean_test (v : Bool) : twoSiteMean μ (twoSiteTest μ c) v = 0 := by
  rw [twoSiteMean, twoSiteTest_true, twoSiteTest_false]
  ring

/-- **On the test vectors the diagonal form is exactly the gap part** — there is
no slack left to throw away. -/
theorem twoSite_sum_marg_sq_test :
    ∑ p : Bool × Bool, marg μ p * twoSiteTest μ c p ^ 2
      = twoSiteVar μ false * c false ^ 2 + twoSiteVar μ true * c true ^ 2 := by
  rw [twoSite_sum_marg_sq, twoSiteDiff_test, twoSiteDiff_test, twoSiteMean_test,
    twoSiteMean_test]
  ring

end Test

/-! ## Cauchy–Schwarz for the two entries

`|C| ≤ √(V₀V₁)` is the statement that the correlation coefficient below has
modulus at most one, and it is the reason the exact constant lands in `[1,2]`.
It is `Techniques.SpectralIndependence.bilinOf_Cov_sq_le` — itself the
discriminant argument of `Techniques.Bilinear`, with no eigenvalue — evaluated
at two standard basis vectors, by the evaluation lemma
`Techniques.PsdOrder.bilinOf_single`. -/

section CauchySchwarz

variable (μ : FinDist (Bool → Bool))

/-- **Cauchy–Schwarz for the two-site covariance**: `C² ≤ V₀·V₁`. -/
theorem twoSite_cov_sq_le : twoSiteCov μ ^ 2 ≤ twoSiteVar μ false * twoSiteVar μ true := by
  have h := bilinOf_Cov_sq_le (μ := μ)
    (fun k => if k = ((false, true) : Bool × Bool) then (1 : ℝ) else 0)
    (fun k => if k = ((true, true) : Bool × Bool) then (1 : ℝ) else 0)
  rwa [bilinOf_single, quadForm_single, quadForm_single] at h

/-- The product of the two site variances is nonnegative. -/
theorem twoSite_var_mul_nonneg : 0 ≤ twoSiteVar μ false * twoSiteVar μ true :=
  mul_nonneg (twoSite_var_nonneg μ false) (twoSite_var_nonneg μ true)

/-- `|C| ≤ √(V₀V₁)`, the square-root form of Cauchy–Schwarz. -/
theorem twoSite_abs_cov_le_sqrt :
    |twoSiteCov μ| ≤ Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (twoSite_cov_sq_le μ)

/-- If the two site variances multiply to zero the covariance vanishes. -/
theorem twoSite_cov_eq_zero_of_var_mul_eq_zero
    (h : twoSiteVar μ false * twoSiteVar μ true = 0) : twoSiteCov μ = 0 := by
  have h2 := twoSite_cov_sq_le μ
  rw [h] at h2
  have := sq_nonneg (twoSiteCov μ)
  nlinarith

end CauchySchwarz

/-! ## The exact constant -/

section Constant

variable (μ : FinDist (Bool → Bool))

/-- The **correlation coefficient** of the two spin indicators,
`ρ = C / √(V₀V₁)`.  When a site is deterministic both `C` and the denominator
vanish and the junk value `0` of real division is the mathematically right one:
a deterministic site contributes nothing to the covariance form
(`Cov_eq_zero_of_marg_eq_one`), so the system is uncorrelated. -/
noncomputable def twoSiteCorr : ℝ :=
  twoSiteCov μ / Real.sqrt (twoSiteVar μ false * twoSiteVar μ true)

/-- **The exact spectral independence constant of a two-site, two-spin system**:
`η = 1 + |ρ|`.  In the monograph's normalisation (our `η` is its `1 + η`) this is
`|ρ|`-spectral independence.  See `twoSite_spectralIndependence` and
`twoSite_eta_le_of_spectralIndependence` for the two halves of the claim that
this is the *least* admissible constant. -/
noncomputable def twoSiteEta : ℝ := 1 + |twoSiteCorr μ|

/-- The correlation coefficient in the four probabilities: the determinant of
the `2 × 2` table over the geometric mean of the four line sums. -/
theorem twoSite_corr_eq :
    twoSiteCorr μ
      = (μ (twoSiteCfg false false) * μ (twoSiteCfg true true)
          - μ (twoSiteCfg false true) * μ (twoSiteCfg true false))
        / Real.sqrt
            ((μ (twoSiteCfg true false) + μ (twoSiteCfg true true))
              * (μ (twoSiteCfg false false) + μ (twoSiteCfg false true))
              * ((μ (twoSiteCfg false true) + μ (twoSiteCfg true true))
                * (μ (twoSiteCfg false false) + μ (twoSiteCfg true false)))) := by
  rw [twoSiteCorr, twoSite_cov_eq_det, twoSite_var_left, twoSite_var_right]

/-- **The correlation coefficient has modulus at most one.** -/
theorem twoSite_abs_corr_le_one : |twoSiteCorr μ| ≤ 1 := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (twoSiteVar μ false * twoSiteVar μ true)) with hr | hr
  · rw [twoSiteCorr, ← hr, div_zero, abs_zero]; norm_num
  · rw [twoSiteCorr, abs_div, abs_of_pos hr, div_le_one hr]
    exact twoSite_abs_cov_le_sqrt μ

/-- **The constant is at least `1`** — the value already reached by product
measures (`Techniques.SpectralIndependence.spectralIndependence_of_pairwiseIndep`). -/
theorem twoSite_one_le_eta : 1 ≤ twoSiteEta μ := by
  rw [twoSiteEta]; linarith [abs_nonneg (twoSiteCorr μ)]

/-- **The constant is at most `2 = |V|`** — the value of the crude universal
bound `Techniques.SpectralIndependence.spectralIndependence_card`. -/
theorem twoSite_eta_le_two : twoSiteEta μ ≤ 2 := by
  rw [twoSiteEta]; linarith [twoSite_abs_corr_le_one μ]

end Constant

/-! ## The constant in the unnormalised weights

Everything above is stated for a distribution, i.e. for a table summing to one.
An arbitrary nonnegative weight `w` on the four configurations gives the same
number: `ρ` is a ratio of a degree-two form to the square root of a degree-four
form, so the partition function cancels and `Z` never appears. -/

section Weights

variable (w : (Bool → Bool) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)

/-- **The exact constant in the four weights.**

`ρ = (w₀₀w₁₁ − w₀₁w₁₀) / √((w₀₀+w₀₁)(w₁₀+w₁₁)(w₀₀+w₁₀)(w₀₁+w₁₁))`,

with no `Z`: the determinant is quadratic in `w` and the four line sums are
quartic, so the two powers of the partition function cancel.  The exact spectral
independence constant of the Gibbs measure of `w` is `1 + |ρ|`. -/
theorem twoSite_corr_gibbs :
    twoSiteCorr (gibbs w hw hZ)
      = (w (twoSiteCfg false false) * w (twoSiteCfg true true)
          - w (twoSiteCfg false true) * w (twoSiteCfg true false))
        / Real.sqrt
            ((w (twoSiteCfg true false) + w (twoSiteCfg true true))
              * (w (twoSiteCfg false false) + w (twoSiteCfg false true))
              * ((w (twoSiteCfg false true) + w (twoSiteCfg true true))
                * (w (twoSiteCfg false false) + w (twoSiteCfg true false)))) := by
  have hZ' : Z w ≠ 0 := hZ.ne'
  have hZ2 : (Z w) ^ 2 ≠ 0 := pow_ne_zero 2 hZ'
  have hcancel : ∀ x y z : ℝ, z ≠ 0 → x / z / (y / z) = x / y := by
    intro x y z hz
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · field_simp
  set A := w (twoSiteCfg false false) with hA
  set B := w (twoSiteCfg false true) with hB
  set C := w (twoSiteCfg true false) with hC
  set D := w (twoSiteCfg true true) with hD
  rw [twoSiteCorr, twoSite_cov_eq_det, twoSite_var_left, twoSite_var_right]
  simp only [gibbs_apply]
  have hnum : A / Z w * (D / Z w) - B / Z w * (C / Z w)
      = (A * D - B * C) / (Z w) ^ 2 := by
    field_simp
    left; ring
  have hden : (C / Z w + D / Z w) * (A / Z w + B / Z w)
        * ((B / Z w + D / Z w) * (A / Z w + C / Z w))
      = ((C + D) * (A + B) * ((B + D) * (A + C))) / ((Z w) ^ 2) ^ 2 := by
    field_simp
    left; ring
  rw [hnum, hden, Real.sqrt_div' _ (sq_nonneg ((Z w) ^ 2)), Real.sqrt_sq (sq_nonneg (Z w))]
  exact hcancel _ _ _ hZ2

end Weights

/-! ## `η = 1 + |ρ|` works -/

section Upper

variable (μ : FinDist (Bool → Bool))

/-- The weighted arithmetic–geometric mean inequality in the two site
variances: `2√(V₀V₁)·|b₀b₁| ≤ V₀b₀² + V₁b₁²`.  This is the only inequality in
the sharp direction, and equality in it is what the extremal test vector
realises. -/
theorem twoSite_amgm (b₀ b₁ : ℝ) :
    2 * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) * |b₀ * b₁|
      ≤ twoSiteVar μ false * b₀ ^ 2 + twoSiteVar μ true * b₁ ^ 2 := by
  set r₀ := Real.sqrt (twoSiteVar μ false) with hr₀
  set r₁ := Real.sqrt (twoSiteVar μ true) with hr₁
  have h0 : r₀ ^ 2 = twoSiteVar μ false := by
    rw [hr₀]; exact Real.sq_sqrt (twoSite_var_nonneg μ false)
  have h1 : r₁ ^ 2 = twoSiteVar μ true := by
    rw [hr₁]; exact Real.sq_sqrt (twoSite_var_nonneg μ true)
  have hr : Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) = r₀ * r₁ := by
    rw [hr₀, hr₁]; exact Real.sqrt_mul (twoSite_var_nonneg μ false) _
  rw [hr, abs_mul, ← sq_abs b₀, ← sq_abs b₁, ← h0, ← h1]
  nlinarith [sq_nonneg (r₀ * |b₀| - r₁ * |b₁|)]

/-- The cross term of the covariance form is dominated by `|ρ|` times the gap
part of the diagonal form.  This is the whole content of the upper bound; the
degenerate case `V₀V₁ = 0` is where Cauchy–Schwarz forces `C = 0`, so both sides
vanish and the junk value of `ρ` does no harm. -/
theorem twoSite_cross_le (b₀ b₁ : ℝ) :
    2 * twoSiteCov μ * (b₀ * b₁)
      ≤ |twoSiteCorr μ| * (twoSiteVar μ false * b₀ ^ 2 + twoSiteVar μ true * b₁ ^ 2) := by
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (twoSiteVar μ false * twoSiteVar μ true)) with hr | hr
  · have hz : twoSiteVar μ false * twoSiteVar μ true = 0 := by
      have h := Real.sq_sqrt (twoSite_var_mul_nonneg μ)
      rw [← hr] at h
      simpa using h.symm
    have hC : twoSiteCov μ = 0 := twoSite_cov_eq_zero_of_var_mul_eq_zero μ hz
    have hcorr : twoSiteCorr μ = 0 := by rw [twoSiteCorr, ← hr, div_zero]
    rw [hC, hcorr]
    simp
  · have hcorr : |twoSiteCorr μ|
        = |twoSiteCov μ| / Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) := by
      rw [twoSiteCorr, abs_div, abs_of_pos hr]
    have h1 : twoSiteCov μ * (b₀ * b₁) ≤ |twoSiteCov μ| * |b₀ * b₁| := by
      rw [← abs_mul]; exact le_abs_self _
    have hmul := mul_le_mul_of_nonneg_left (twoSite_amgm μ b₀ b₁)
      (div_nonneg (abs_nonneg (twoSiteCov μ)) hr.le)
    have hsimp : |twoSiteCov μ| / Real.sqrt (twoSiteVar μ false * twoSiteVar μ true)
        * (2 * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) * |b₀ * b₁|)
        = 2 * |twoSiteCov μ| * |b₀ * b₁| := by
      field_simp
      ring
    rw [hsimp] at hmul
    rw [hcorr]
    linarith

/-- **The two-site system is `(1 + |ρ|)`-spectrally independent.**

The covariance form is bounded by `η` times the *gap part* of the diagonal form,
which is the strongest form of the statement: the site means thrown away by
`twoSite_sum_marg_sq_ge` are exactly the slack, and the extremal vectors of
`twoSiteTest` have none. -/
theorem twoSite_quadForm_Cov_le (a : Bool × Bool → ℝ) :
    quadForm (Cov μ) a
      ≤ twoSiteEta μ * (twoSiteVar μ false * twoSiteDiff a false ^ 2
          + twoSiteVar μ true * twoSiteDiff a true ^ 2) := by
  have hu : 0 ≤ twoSiteVar μ false * twoSiteDiff a false ^ 2
      + twoSiteVar μ true * twoSiteDiff a true ^ 2 :=
    add_nonneg (mul_nonneg (twoSite_var_nonneg μ false) (sq_nonneg _))
      (mul_nonneg (twoSite_var_nonneg μ true) (sq_nonneg _))
  have hkey := twoSite_cross_le μ (twoSiteDiff a false) (twoSiteDiff a true)
  rw [twoSite_quadForm_Cov, twoSiteEta]
  nlinarith [hkey, hu]

/-- **The two-site system is `(1 + |ρ|)`-spectrally independent**, in the shape
of `Techniques.SpectralIndependence.SpectralIndependence`. -/
theorem twoSite_spectralIndependence : SpectralIndependence μ (twoSiteEta μ) := by
  refine (spectralIndependence_iff _).mpr fun a => ?_
  refine (twoSite_quadForm_Cov_le μ a).trans ?_
  exact mul_le_mul_of_nonneg_left (twoSite_sum_marg_sq_ge μ a)
    (le_trans zero_le_one (twoSite_one_le_eta μ))

end Upper

/-! ## `η = 1 + |ρ|` cannot be improved

The lower bound is the extremal test vector and nothing else.  Testing the
ordering at `twoSiteTest μ c` turns it into a plain two-variable inequality with
*no* slack — the site means are zero there — and choosing
`c = (√V₁, ±√V₀)` with the sign of the covariance makes the two sides
`2V₀V₁ + 2|C|√(V₀V₁)` and `η·2V₀V₁`. -/

section Lower

variable (μ : FinDist (Bool → Bool))

/-- Spectral independence, evaluated at an extremal test vector: a plain
inequality between two quadratic expressions in the spin gaps, with no
remaining slack. -/
theorem twoSite_test_le_of_spectralIndependence {η : ℝ} (h : SpectralIndependence μ η)
    (c : Bool → ℝ) :
    twoSiteVar μ false * c false ^ 2 + 2 * twoSiteCov μ * (c false * c true)
        + twoSiteVar μ true * c true ^ 2
      ≤ η * (twoSiteVar μ false * c false ^ 2 + twoSiteVar μ true * c true ^ 2) := by
  have h1 := (spectralIndependence_iff η).mp h (twoSiteTest μ c)
  rwa [twoSite_quadForm_Cov, twoSiteDiff_test, twoSiteDiff_test,
    twoSite_sum_marg_sq_test] at h1

/-- **`1 + |ρ|` is the least admissible constant.**

If both sites are genuinely random — `0 < V₀` and `0 < V₁`, i.e. neither spin is
determined — then every `η` with `Cov μ ⪯ η·diag (marg μ)` satisfies
`1 + |ρ| ≤ η`.  Together with `twoSite_spectralIndependence` this pins the
spectral independence constant of the two-site system exactly. -/
theorem twoSite_eta_le_of_spectralIndependence (hV₀ : 0 < twoSiteVar μ false)
    (hV₁ : 0 < twoSiteVar μ true) {η : ℝ} (h : SpectralIndependence μ η) :
    twoSiteEta μ ≤ η := by
  have hr : 0 < Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) :=
    Real.sqrt_pos.mpr (mul_pos hV₀ hV₁)
  have hrsq : Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) ^ 2
      = twoSiteVar μ false * twoSiteVar μ true := Real.sq_sqrt (twoSite_var_mul_nonneg μ)
  obtain ⟨ε, hεsq, hεC⟩ : ∃ ε : ℝ, ε * ε = 1 ∧ twoSiteCov μ * ε = |twoSiteCov μ| := by
    by_cases hc : 0 ≤ twoSiteCov μ
    · exact ⟨1, by norm_num, by rw [mul_one, abs_of_nonneg hc]⟩
    · exact ⟨-1, by norm_num, by rw [mul_neg_one, abs_of_neg (not_le.mp hc)]⟩
  have h2 := twoSite_test_le_of_spectralIndependence μ h
    (fun v => cond v (ε * Real.sqrt (twoSiteVar μ false)) (Real.sqrt (twoSiteVar μ true)))
  simp only [cond_true, cond_false] at h2
  have hA : Real.sqrt (twoSiteVar μ true) ^ 2 = twoSiteVar μ true :=
    Real.sq_sqrt (twoSite_var_nonneg μ true)
  have hB : (ε * Real.sqrt (twoSiteVar μ false)) ^ 2 = twoSiteVar μ false := by
    rw [mul_pow, Real.sq_sqrt (twoSite_var_nonneg μ false)]
    nlinarith [hεsq]
  have hD : Real.sqrt (twoSiteVar μ true) * (ε * Real.sqrt (twoSiteVar μ false))
      = ε * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) := by
    rw [Real.sqrt_mul (twoSite_var_nonneg μ false)]
    ring
  rw [hA, hB, hD] at h2
  have hCe : 2 * twoSiteCov μ
        * (ε * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true))
      = 2 * |twoSiteCov μ| * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) := by
    rw [← hεC]; ring
  rw [hCe] at h2
  have h3 : |twoSiteCov μ|
      ≤ (η - 1) * Real.sqrt (twoSiteVar μ false * twoSiteVar μ true) := by
    have key : ∀ R Q : ℝ, 0 < R → R ^ 2 = Q →
        Q + 2 * |twoSiteCov μ| * R + Q ≤ η * (Q + Q) → |twoSiteCov μ| ≤ (η - 1) * R := by
      rintro R Q hR rfl hle
      nlinarith [hle, hR]
    exact key _ _ hr hrsq (by linarith [h2])
  rw [twoSiteEta, twoSiteCorr, abs_div, abs_of_pos hr]
  linarith [(div_le_iff₀ hr).mpr h3]

/-- **The spectral independence constants of the two-site system are exactly the
reals `≥ 1 + |ρ|`.**  The headline of the module: the constant is not merely
bounded, it is computed. -/
theorem twoSite_spectralIndependence_iff (hV₀ : 0 < twoSiteVar μ false)
    (hV₁ : 0 < twoSiteVar μ true) (η : ℝ) :
    SpectralIndependence μ η ↔ twoSiteEta μ ≤ η :=
  ⟨fun h => twoSite_eta_le_of_spectralIndependence μ hV₀ hV₁ h,
    fun h => (twoSite_spectralIndependence μ).mono h⟩

end Lower

/-! ## First sanity check: the product case returns `η = 1`

`Chains.ProductSpectralIndependence` proves `η = 1` for a product measure, via
`spectralIndependence_of_pairwiseIndep`.  Here that is not merely reproved but
*characterised*: for two sites the exact constant is `1` **iff** the measure is
pairwise independent, iff the `2 × 2` table has vanishing determinant.  Since
`twoSite_spectralIndependence_iff` says `1 + |ρ|` is least, this says the
product case is the only one where the degenerate constant is correct. -/

section Product

variable (μ : FinDist (Bool → Bool))

/-- All four cross entries of the covariance form vanish together: they are the
same number up to sign, because each block row of `Cov` sums to zero
(`Cov_sum_right`). -/
theorem twoSite_cov_cross_eq_zero (h : twoSiteCov μ = 0) (s t : Bool) :
    Cov μ (false, s) (true, t) = 0 := by
  have hrow : ∀ u : Bool,
      Cov μ (false, u) (true, true) + Cov μ (false, u) (true, false) = 0 := by
    intro u
    have := Cov_sum_right (μ := μ) (false, u) true
    simpa [Fintype.sum_bool] using this
  have hcol : ∀ u : Bool,
      Cov μ (false, true) (true, u) + Cov μ (false, false) (true, u) = 0 := by
    intro u
    have := Cov_sum_right (μ := μ) (true, u) false
    rw [Fintype.sum_bool, Cov_symm, Cov_symm (μ := μ) (true, u) (false, false)] at this
    exact this
  rw [twoSiteCov] at h
  have h1 := hrow true
  have h2 := hcol true
  have h3 := hcol false
  cases s <;> cases t <;> linarith [h1, h2, h3, hrow false]

/-- **Pairwise independence is the vanishing of the determinant.** -/
theorem twoSite_pairwiseIndep_iff : PairwiseIndep μ ↔ twoSiteCov μ = 0 := by
  constructor
  · intro h
    have := h (false, true) (true, true) (by decide)
    rw [twoSiteCov, Cov_apply, this, sub_self]
  · intro h p q hpq
    obtain ⟨v, s⟩ := p
    obtain ⟨u, t⟩ := q
    have hcov : ∀ a b : Bool, joint μ (false, a) (true, b)
        = marg μ (false, a) * marg μ (true, b) := by
      intro a b
      have := twoSite_cov_cross_eq_zero μ h a b
      rw [Cov_apply, sub_eq_zero] at this
      exact this
    cases v <;> cases u
    · exact absurd rfl hpq
    · exact hcov s t
    · rw [joint_symm, hcov t s, mul_comm]
    · exact absurd rfl hpq

/-- **The exact constant is `1` exactly when the covariance vanishes.**  The
degenerate case is included: if a site is deterministic then `ρ` is the junk
value `0`, the constant is `1`, and the measure really is pairwise
independent. -/
theorem twoSite_eta_eq_one_iff_cov : twoSiteEta μ = 1 ↔ twoSiteCov μ = 0 := by
  constructor
  · intro h
    have habs : |twoSiteCorr μ| = 0 := by rw [twoSiteEta] at h; linarith
    have hz : twoSiteCorr μ = 0 := abs_eq_zero.mp habs
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (twoSiteVar μ false * twoSiteVar μ true)) with hr | hr
    · refine twoSite_cov_eq_zero_of_var_mul_eq_zero μ ?_
      have hq := Real.sq_sqrt (twoSite_var_mul_nonneg μ)
      rw [← hr] at hq
      simpa using hq.symm
    · rw [twoSiteCorr, div_eq_zero_iff] at hz
      rcases hz with hz | hz
      · exact hz
      · exact absurd hz hr.ne'
  · intro h
    rw [twoSiteEta, twoSiteCorr, h, zero_div, abs_zero, add_zero]

/-- **The exact constant is `1` exactly in the product case.**  This is the
calibration against `Chains.ProductSpectralIndependence`: that module's `η = 1`
is correct, and for two sites it is correct *only* for a product measure. -/
theorem twoSite_eta_eq_one_iff_pairwiseIndep : twoSiteEta μ = 1 ↔ PairwiseIndep μ :=
  (twoSite_eta_eq_one_iff_cov μ).trans (twoSite_pairwiseIndep_iff μ).symm

/-- **The exact constant is `1` exactly when the `2 × 2` table has vanishing
determinant** — the statement in the four weights. -/
theorem twoSite_eta_eq_one_iff_det : twoSiteEta μ = 1
    ↔ μ (twoSiteCfg false false) * μ (twoSiteCfg true true)
      = μ (twoSiteCfg false true) * μ (twoSiteCfg true false) := by
  rw [twoSite_eta_eq_one_iff_cov, twoSite_cov_eq_det, sub_eq_zero]

/-- **A factorising table has `η = 1`.**  If the four probabilities factorise as
`μ(s,t) = φ(s)·ψ(t)` — the two-site product measure — then the exact constant is
the degenerate one, with no hypothesis on `φ` or `ψ` at all. -/
theorem twoSite_eta_eq_one_of_prod (φ ψ : Bool → ℝ)
    (h : ∀ s t : Bool, μ (twoSiteCfg s t) = φ s * ψ t) : twoSiteEta μ = 1 := by
  rw [twoSite_eta_eq_one_iff_det, h, h, h, h]
  ring

end Product

/-! ## Second sanity check: `η = 2 = |V|` at perfect correlation

`Techniques.SpectralIndependence` flags the measure on the two *constant*
configurations as the example showing `Cov ⪯ 1·diag (marg)` is false in general.
The formula reproduces exactly that: the table is diagonal, `ρ = 1`, and
`η = 2`, which is the value of the crude universal bound
`spectralIndependence_card` at `|V| = 2`.  So the universal bound is attained,
not merely valid. -/

section Perfect

/-- The measure on the **two constant configurations**, with mass `r` on the
all-`true` configuration and `1 − r` on the all-`false` one. -/
def twoSiteConst (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : FinDist (Bool → Bool) where
  p σ := if σ false = σ true then cond (σ false) r (1 - r) else 0
  p_nonneg σ := by
    dsimp only
    split
    · cases h : σ false
      · simp only [h, cond_false]; linarith
      · simp only [h, cond_true]; exact h0
    · exact le_rfl
  p_sum := by
    rw [twoSite_sum_config]
    norm_num

@[simp] theorem twoSiteConst_apply (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (s t : Bool) :
    twoSiteConst r h0 h1 (twoSiteCfg s t) = if s = t then cond s r (1 - r) else 0 := rfl

variable {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)

/-- Both sites have variance `r(1−r)`. -/
theorem twoSiteConst_var (v : Bool) : twoSiteVar (twoSiteConst r h0 h1) v = r * (1 - r) := by
  cases v
  · rw [twoSite_var_left]; norm_num
  · rw [twoSite_var_right]; norm_num

/-- The covariance is also `r(1−r)`: the two spins are equal. -/
theorem twoSiteConst_cov : twoSiteCov (twoSiteConst r h0 h1) = r * (1 - r) := by
  rw [twoSite_cov_eq_det]; norm_num; ring

/-- **The correlation coefficient is `1`.** -/
theorem twoSiteConst_corr (hr0 : 0 < r) (hr1 : r < 1) :
    twoSiteCorr (twoSiteConst r h0 h1) = 1 := by
  have hpos : 0 < r * (1 - r) := mul_pos hr0 (by linarith)
  rw [twoSiteCorr, twoSiteConst_var, twoSiteConst_var, twoSiteConst_cov,
    Real.sqrt_mul_self hpos.le, div_self hpos.ne']

/-- **The exact constant of the perfectly correlated two-site system is `2`.**

The witness that `Techniques.SpectralIndependence`'s `η = 1` is not universal —
and, by `twoSite_spectralIndependence_iff`, the witness that no constant below
`2` works here at all. -/
theorem twoSiteConst_eta (hr0 : 0 < r) (hr1 : r < 1) :
    twoSiteEta (twoSiteConst r h0 h1) = 2 := by
  rw [twoSiteEta, twoSiteConst_corr h0 h1 hr0 hr1]
  norm_num

/-- **`η = 2 = |V|`: the crude universal bound `spectralIndependence_card` is
attained.**  It is therefore sharp, not merely correct. -/
theorem twoSiteConst_eta_eq_card (hr0 : 0 < r) (hr1 : r < 1) :
    twoSiteEta (twoSiteConst r h0 h1) = (Fintype.card Bool : ℝ) := by
  rw [twoSiteConst_eta h0 h1 hr0 hr1, Fintype.card_bool]
  norm_num

/-- **The perfectly correlated system is `η`-spectrally independent exactly for
`η ≥ 2`.** -/
theorem twoSiteConst_spectralIndependence_iff (hr0 : 0 < r) (hr1 : r < 1) (η : ℝ) :
    SpectralIndependence (twoSiteConst r h0 h1) η ↔ 2 ≤ η := by
  have hpos : 0 < r * (1 - r) := mul_pos hr0 (by linarith)
  rw [twoSite_spectralIndependence_iff _
      (by rw [twoSiteConst_var]; exact hpos) (by rw [twoSiteConst_var]; exact hpos),
    twoSiteConst_eta h0 h1 hr0 hr1]

/-- **`Cov ⪯ 1·diag (marg)` is false**, with an explicit witness. -/
theorem twoSiteConst_not_spectralIndependence_one (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ SpectralIndependence (twoSiteConst r h0 h1) 1 := by
  rw [twoSiteConst_spectralIndependence_iff h0 h1 hr0 hr1]
  norm_num

/-- **The non-degeneracy hypothesis of `twoSite_eta_le_of_spectralIndependence`
cannot be dropped.**

At `r = 0` the measure is a point mass; the covariance form vanishes identically,
so `SpectralIndependence μ 0` holds, while `twoSiteEta μ = 1`.  The formula
`1 + |ρ|` is therefore the least admissible constant only away from a
deterministic system — which is exactly the situation in which `ρ` is a
correlation coefficient rather than a `0/0`. -/
theorem twoSiteConst_zero_degenerate :
    SpectralIndependence (twoSiteConst 0 (le_refl (0 : ℝ)) zero_le_one) 0
      ∧ twoSiteEta (twoSiteConst 0 (le_refl (0 : ℝ)) zero_le_one) = 1 := by
  refine ⟨(spectralIndependence_iff 0).mpr fun a => ?_, ?_⟩
  · rw [twoSite_quadForm_Cov, twoSiteConst_var, twoSiteConst_var, twoSiteConst_cov]
    norm_num
  · rw [twoSite_eta_eq_one_iff_cov, twoSiteConst_cov]
    norm_num

end Perfect

/-! ## The constant always lies in `[1, |V|]` -/

section Bracket

variable (μ : FinDist (Bool → Bool))

/-- **The exact constant lies in `[1, 2]`**, `2 = |V|`.  The lower end is the
product case (`twoSite_eta_eq_one_iff_pairwiseIndep`), the upper end is perfect
correlation (`twoSiteConst_eta`), and both are attained. -/
theorem twoSite_eta_mem_Icc : 1 ≤ twoSiteEta μ ∧ twoSiteEta μ ≤ (Fintype.card Bool : ℝ) := by
  refine ⟨twoSite_one_le_eta μ, ?_⟩
  rw [Fintype.card_bool]
  have := twoSite_eta_le_two μ
  norm_num
  linarith

/-- **The exact constant refines the crude universal bound.**  Both
`spectralIndependence_card` and `twoSite_spectralIndependence` are true, and the
second is at least as strong; by `twoSiteConst_eta_eq_card` they coincide exactly
at perfect correlation. -/
theorem twoSite_spectralIndependence_card_check :
    SpectralIndependence μ (twoSiteEta μ)
      ∧ SpectralIndependence μ (Fintype.card Bool)
      ∧ twoSiteEta μ ≤ (Fintype.card Bool : ℝ) :=
  ⟨twoSite_spectralIndependence μ, spectralIndependence_card μ, (twoSite_eta_mem_Icc μ).2⟩

end Bracket

/-! ## The audit: the local walk at two sites

`pinLocalWalk` requires `|Λ| + 1 < |V|`, so at `|V| = 2` the *only* admissible
pinning is the empty one — two sites is exactly the smallest system in which the
local walk exists.  It does exist, and it is not degenerate: `π_{∅,1}` is a
genuine distribution on the four (site, spin) pairs and `Q_∅` is the walk
"resample the configuration given the current spin, then read the *other*
site".

The audit runs the exact constant through
`Techniques.SpectralIndependenceConverse`'s equivalence and, independently,
computes `ℰ_{Q_∅}` from the definition of `pinLocalWalk`.  Both give the Poincaré
constant `1 − |ρ|`. -/

section LocalWalk

/-- **Two sites is the smallest system with a local walk.**  `pinLocalWalk` needs
`|Λ| + 1 < |V|`; at `|V| = 2` this holds for `Λ = ∅` and for nothing else. -/
theorem twoSite_card_succ_lt : ((∅ : Finset Bool).card) + 1 < Fintype.card Bool := by decide

variable (w : (Bool → Bool) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)

/-- The joint law read in the other order. -/
theorem twoSite_joint_symm (μ : FinDist (Bool → Bool)) (t s : Bool) :
    joint μ (true, t) (false, s) = μ (twoSiteCfg s t) := by
  rw [joint_symm, twoSite_joint]

/-- **The variance under `π_{∅,1}`, in closed form.**

`Var_{π_{∅,1}}(f) = (V₀b₀² + V₁b₁²)/2 + (m₀ − m₁)²/4`: the gap part halved, plus
a quarter of the squared difference of the two site means.  The second term is
invisible to the covariance form and is what makes the local walk's Poincaré
constant the *minimum* of `1 − |ρ|` and `2`. -/
theorem twoSite_Var_pinDist (f : Bool × Bool → ℝ) :
    Var (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt)) f
      = (twoSiteVar (gibbs w hw hZ) false * twoSiteDiff f false ^ 2
          + twoSiteVar (gibbs w hw hZ) true * twoSiteDiff f true ^ 2) / 2
        + (twoSiteMean (gibbs w hw hZ) f false
            - twoSiteMean (gibbs w hw hZ) f true) ^ 2 / 4 := by
  have hfr : ∀ p : Bool × Bool, freeRestrict (∅ : Finset Bool) f p = f p :=
    fun p => freeRestrict_of_not_mem (Finset.not_mem_empty p.1) f
  have hN : numFree (∅ : Finset Bool) = (2 : ℝ) := by
    rw [numFree_empty, Fintype.card_bool]; norm_num
  have hA : ∑ p : Bool × Bool, marg (gibbs w hw hZ) p * f p
      = twoSiteMean (gibbs w hw hZ) f false + twoSiteMean (gibbs w hw hZ) f true := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, twoSiteMean]
    ring
  rw [Var_eq_ip_sub_sq, ip_pinDist_self, Ex_pinDist, hN]
  simp only [hfr]
  rw [twoSite_sum_marg_sq, hA]
  ring

/-- **The detailed-balance cell of the local walk at two sites.**

`π_{∅,1}(x)·Q_∅(x,y) = joint(x,y)/2` off the diagonal block and `0` on it: with
`m = 2` free sites the normalisation `m(m−1) = 2` is the only constant in the
formula.  Everything below is this identity summed. -/
theorem twoSite_pinDist_mul_pinLocalWalk (x y : Bool × Bool) :
    pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt) x
        * pinLocalWalk w ∅ hw twoSite_card_succ_lt x y
      = if x.1 ≠ y.1 then joint (gibbs w hw hZ) x y / 2 else 0 := by
  have h1 : ((Fintype.card Bool - (∅ : Finset Bool).card : ℕ) : ℝ) = 2 := by
    norm_num [Fintype.card_bool]
  have h2 : ((Fintype.card Bool - ((∅ : Finset Bool).card + 1) : ℕ) : ℝ) = 1 := by
    norm_num [Fintype.card_bool]
  rw [pinDist_mul_pinLocalWalk, joint_gibbs, h1, h2]
  by_cases hne : x.1 = y.1
  · rw [if_neg fun h => h.2.2 hne, if_neg (not_not_intro hne)]
  · rw [if_pos ⟨Finset.not_mem_empty _, Finset.not_mem_empty _, hne⟩, if_pos hne, div_div]
    congr 1
    ring

/-- **The Dirichlet form of the local walk, computed directly.**

`ℰ_{Q_∅}(f) = ½ ∑_{s,t} μ(s,t)·(f(false,s) − f(true,t))²`.

This is the *second* route of the audit: it uses only `pinLocalWalk`'s
definition, `dirichlet_self_eq_pair` and the four table entries — not
`dirichlet_pinLocalWalk`, not `Cov`, and not spectral independence.  In
probabilistic terms `ℰ_{Q_∅}(f) = ½·E_μ[(X − Y)²]` for `X = f(false, σ_0)` and
`Y = f(true, σ_1)`: the local walk at two sites just swaps which coordinate you
look at. -/
theorem twoSite_dirichlet_pinLocalWalk (f : Bool × Bool → ℝ) :
    dirichlet (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
        (pinLocalWalk w ∅ hw twoSite_card_succ_lt) f f
      = 1 / 2 * (gibbs w hw hZ (twoSiteCfg false false)
            * (f (false, false) - f (true, false)) ^ 2
          + gibbs w hw hZ (twoSiteCfg false true)
            * (f (false, false) - f (true, true)) ^ 2
          + gibbs w hw hZ (twoSiteCfg true false)
            * (f (false, true) - f (true, false)) ^ 2
          + gibbs w hw hZ (twoSiteCfg true true)
            * (f (false, true) - f (true, true)) ^ 2) := by
  have hdiagL : ∀ s t : Bool,
      pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt) (false, s)
        * pinLocalWalk w ∅ hw twoSite_card_succ_lt (false, s) (false, t) = 0 := by
    intro s t
    rw [twoSite_pinDist_mul_pinLocalWalk, if_neg (by simp)]
  have hdiagR : ∀ s t : Bool,
      pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt) (true, s)
        * pinLocalWalk w ∅ hw twoSite_card_succ_lt (true, s) (true, t) = 0 := by
    intro s t
    rw [twoSite_pinDist_mul_pinLocalWalk, if_neg (by simp)]
  have hcrossL : ∀ s t : Bool,
      pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt) (false, s)
          * pinLocalWalk w ∅ hw twoSite_card_succ_lt (false, s) (true, t)
        = gibbs w hw hZ (twoSiteCfg s t) / 2 := by
    intro s t
    rw [twoSite_pinDist_mul_pinLocalWalk, if_pos (by simp), twoSite_joint]
  have hcrossR : ∀ t s : Bool,
      pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt) (true, t)
          * pinLocalWalk w ∅ hw twoSite_card_succ_lt (true, t) (false, s)
        = gibbs w hw hZ (twoSiteCfg s t) / 2 := by
    intro t s
    rw [twoSite_pinDist_mul_pinLocalWalk, if_pos (by simp), twoSite_joint_symm]
  rw [dirichlet_self_eq_pair
    (pinLocalWalk_stationary w ∅ hw hZ twoSite_card_succ_lt) f]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hdiagL, hdiagR, hcrossL, hcrossR]
  ring

/-- **The Dirichlet form of the local walk, in the same coordinates as the
variance.**

`ℰ_{Q_∅}(f) = (V₀b₀² + V₁b₁² − 2C·b₀b₁)/2 + (m₀ − m₁)²/2`.

Compare `twoSite_Var_pinDist`: the gap parts differ by the cross term `−2Cb₀b₁`
and the mean parts by a factor of two.  Both statements come from the four table
entries alone; nothing here has been through `Cov` or `quadForm`. -/
theorem twoSite_dirichlet_pinLocalWalk_eq (f : Bool × Bool → ℝ) :
    dirichlet (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
        (pinLocalWalk w ∅ hw twoSite_card_succ_lt) f f
      = (twoSiteVar (gibbs w hw hZ) false * twoSiteDiff f false ^ 2
          + twoSiteVar (gibbs w hw hZ) true * twoSiteDiff f true ^ 2
          - 2 * twoSiteCov (gibbs w hw hZ)
              * (twoSiteDiff f false * twoSiteDiff f true)) / 2
        + (twoSiteMean (gibbs w hw hZ) f false
            - twoSiteMean (gibbs w hw hZ) f true) ^ 2 / 2 := by
  have h00 : gibbs w hw hZ (twoSiteCfg false false)
      = 1 - gibbs w hw hZ (twoSiteCfg false true)
        - gibbs w hw hZ (twoSiteCfg true false)
        - gibbs w hw hZ (twoSiteCfg true true) := by
    have := twoSite_sum_mu (gibbs w hw hZ); linarith
  rw [twoSite_dirichlet_pinLocalWalk]
  simp only [twoSite_var_left, twoSite_var_right, twoSite_cov_eq_det, twoSiteMean,
    twoSiteDiff, twoSite_marg_left, twoSite_marg_right]
  rw [h00]
  ring

/-! ### Route one: through the equivalence with spectral independence -/

/-- **The local walk has Poincaré constant `1 − |ρ|`, through the general
equivalence.**

`Techniques.SpectralIndependenceConverse`'s
`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty` turns
`η`-spectral independence into a gap `(n − η)/(n − 1)`; at `n = 2` and
`η = 1 + |ρ|` that is `1 − |ρ|` on the nose. -/
theorem twoSite_spectralGapAtLeast_pinLocalWalk_via_spectralIndependence :
    SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
      (pinLocalWalk w ∅ hw twoSite_card_succ_lt)
      (1 - |twoSiteCorr (gibbs w hw hZ)|) := by
  have hn : 1 < Fintype.card Bool := by decide
  have h := (spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty w hw hZ hn
    (twoSiteEta (gibbs w hw hZ))).mp (twoSite_spectralIndependence (gibbs w hw hZ))
  have hc : ((Fintype.card Bool : ℝ) - twoSiteEta (gibbs w hw hZ))
      / ((Fintype.card Bool : ℝ) - 1) = 1 - |twoSiteCorr (gibbs w hw hZ)| := by
    rw [Fintype.card_bool, twoSiteEta]
    norm_num
    ring
  rw [hc] at h
  exact h

/-! ### Route two: directly from the closed forms -/

/-- **The local walk has Poincaré constant `1 − |ρ|`, computed directly.**

Nothing in this proof mentions `Cov`, `quadForm`, `SpectralIndependence`, or
`dirichlet_pinLocalWalk`: it is `twoSite_dirichlet_pinLocalWalk_eq` minus
`(1 − |ρ|)` times `twoSite_Var_pinDist`, which leaves
`(|ρ|(V₀b₀² + V₁b₁²) − 2Cb₀b₁)/2 + (1 + |ρ|)(m₀ − m₁)²/4`, both summands
nonnegative — the first by `twoSite_cross_le`. -/
theorem twoSite_spectralGapAtLeast_pinLocalWalk_direct :
    SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
      (pinLocalWalk w ∅ hw twoSite_card_succ_lt)
      (1 - |twoSiteCorr (gibbs w hw hZ)|) := by
  intro f
  rw [twoSite_Var_pinDist, twoSite_dirichlet_pinLocalWalk_eq]
  have hcross := twoSite_cross_le (gibbs w hw hZ) (twoSiteDiff f false) (twoSiteDiff f true)
  have hd := sq_nonneg (twoSiteMean (gibbs w hw hZ) f false
    - twoSiteMean (gibbs w hw hZ) f true)
  have habs := abs_nonneg (twoSiteCorr (gibbs w hw hZ))
  nlinarith [hcross, hd, habs, mul_nonneg hd habs]

/-- **The audit: two independent routes to the same Poincaré constant.**

The proposition is proved twice, once along each route — the general
spectral-independence equivalence on the left, the direct computation of
`ℰ_{Q_∅}` and `Var_{π_{∅,1}}` from the four table entries on the right.  That
both terms typecheck against the *same* statement is the content: the two
constants are not comparable, they are the same real expression, and there is no
slack in either route. -/
theorem twoSite_pinLocalWalk_audit :
    SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
        (pinLocalWalk w ∅ hw twoSite_card_succ_lt)
        (1 - |twoSiteCorr (gibbs w hw hZ)|)
      ∧ SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
        (pinLocalWalk w ∅ hw twoSite_card_succ_lt)
        (1 - |twoSiteCorr (gibbs w hw hZ)|) :=
  ⟨twoSite_spectralGapAtLeast_pinLocalWalk_via_spectralIndependence w hw hZ,
    twoSite_spectralGapAtLeast_pinLocalWalk_direct w hw hZ⟩

/-- **`1 − |ρ|` is the exact Poincaré constant of the local walk**, not merely a
lower bound: any admissible `γ` is at most `1 − |ρ|`.  The proof is the converse
half of the equivalence, so the sharpness of the spectral independence constant
transfers to sharpness of the gap with nothing lost. -/
theorem twoSite_le_of_spectralGapAtLeast_pinLocalWalk
    (hV₀ : 0 < twoSiteVar (gibbs w hw hZ) false)
    (hV₁ : 0 < twoSiteVar (gibbs w hw hZ) true) {γ : ℝ}
    (h : SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
      (pinLocalWalk w ∅ hw twoSite_card_succ_lt) γ) :
    γ ≤ 1 - |twoSiteCorr (gibbs w hw hZ)| := by
  have hn : 1 < Fintype.card Bool := by decide
  have hSI := spectralIndependence_of_spectralGapAtLeast_pinLocalWalk_empty w hw hZ hn h
  have hle := twoSite_eta_le_of_spectralIndependence (gibbs w hw hZ) hV₀ hV₁ hSI
  rw [twoSiteEta, Fintype.card_bool] at hle
  norm_num at hle
  linarith

/-- **The Poincaré constants of the local walk are exactly the reals
`≤ 1 − |ρ|`.**  The two-site counterpart of
`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty`, with the
constant computed rather than named. -/
theorem twoSite_spectralGapAtLeast_pinLocalWalk_iff
    (hV₀ : 0 < twoSiteVar (gibbs w hw hZ) false)
    (hV₁ : 0 < twoSiteVar (gibbs w hw hZ) true) (γ : ℝ) :
    SpectralGapAtLeast (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt twoSite_card_succ_lt))
        (pinLocalWalk w ∅ hw twoSite_card_succ_lt) γ
      ↔ γ ≤ 1 - |twoSiteCorr (gibbs w hw hZ)| :=
  ⟨fun h => twoSite_le_of_spectralGapAtLeast_pinLocalWalk w hw hZ hV₀ hV₁ h,
    fun h => (twoSite_spectralGapAtLeast_pinLocalWalk_direct w hw hZ).mono h⟩

end LocalWalk

end Arlib.MarkovChains
