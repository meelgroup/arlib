/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Product measures: tensorization of variance, and the Glauber gap `1/n`

`Chains/GlauberTensorization.lean` defines `ApproxTensorization` and proves both
directions of its equivalence with the spectral gap of the Glauber dynamics, plus
an end-to-end mixing bound.  What it never supplies is a *single weight* for which
`ApproxTensorization` actually holds, so the entire chain of results there is, as
it stands, an implication with no discharged hypothesis.  This module supplies the
first instance, and it is the sharpest one available: for a **product measure** the
tensorization constant is `C = 1`,

  `Var_μ(f) ≤ ∑_v μ[Var_v(f)]`,

which through `spectralGapAtLeast_glauber_of_approxTensorization` gives a spectral
gap of exactly `1/n` for the Gibbs sampler of a product measure, and through
`glauber_mixesWithin_of_approxTensorization` an `O(n · log(1/(ε√m)))` mixing bound.

## How the proof works

The organising object is a *family of projections indexed by subsets of the sites*.
For `Λ : Finset V` let `Q_Λ` be the kernel that resamples the spins in `Λ`
independently from their marginals and leaves the spins off `Λ` alone.  Because the
measure is a product, three things are true at once, and each is a factorwise
computation on `∏ v, …`:

* `Q_Λ` is **reversible** for the Gibbs measure — the detailed-balance identity
  holds coordinate by coordinate (`prodProj_reversible`);
* `Q_Λ ∘ₖ Q_{Λ'} = Q_{Λ ∪ Λ'}` (`prodProjMat_comp`), so the family is a commuting
  family of **idempotents**;
* `Q_∅` is the identity and `Q_univ` is the independent sampler for `μ`.

A self-adjoint idempotent has `ℰ_{Q}(f) = ⟪f, f⟫ - ⟪Q f, Q f⟫`, exactly as
`dirichlet_siteChain` says for the single-site update — and indeed `Q_{v}` *is* the
single-site heat-bath update, `μ`-almost everywhere
(`siteChain_eqOnSupport_prodProj`; the two kernels genuinely differ off the
support, where `Zloc` vanishes, which is why `Techniques.Transport` is imported).
So the quantity `⟪f, f⟫ - ⟪Q_Λ f, Q_Λ f⟫` starts at `0` for `Λ = ∅`, ends at
`Var_μ(f)` for `Λ = univ`, and increases by `μ[Var_v(Q_Λ f)]` when a site `v` is
added.  Since `Q_Λ` is an `L²(μ)`-contraction and commutes with `Q_{v}`,

  `μ[Var_v(Q_Λ f)] = ‖Q_Λ (f - Q_v f)‖² ≤ ‖f - Q_v f‖² = μ[Var_v(f)]`,

and a plain `Finset.induction_on` telescopes the whole thing.  **No ordering of the
sites is needed**: the statement being proved is a bound valid for every `Λ`
simultaneously, so the usual martingale filtration `∅ ⊆ Λ_1 ⊆ … ⊆ univ` never has
to be constructed.

## Main declarations

* `prodWeight`, `prodMarginal` — a product weight `w σ = ∏_v φ_v(σ_v)` and the
  induced single-site marginals; `Z_prodWeight` (`Z = ∏_v ∑_s φ_v(s)`) and
  `gibbs_prodWeight` (the Gibbs measure is the product of the marginals).
* `prodProjMat`, **`prodProj`** — the projection kernel `Q_Λ`, with
  `prodProjMat_empty`, `prodProjMat_singleton`, `prodProjMat_univ`.
* **`prodProjMat_comp`** — `Q_Λ ∘ Q_{Λ'} = Q_{Λ ∪ Λ'}`.  The one genuinely
  product-specific fact; commutation and idempotence are both corollaries.
* **`prodProj_reversible`**, `ip_act_prodProj`, `dirichlet_prodProj`,
  `ip_act_prodProj_le` — `Q_Λ` is a self-adjoint idempotent, hence an orthogonal
  projection, hence an `L²(μ)`-contraction.
* **`siteChain_eqOnSupport_prodProj`** — the single-site heat-bath update of a
  product weight *is* `Q_{v}`, `μ`-almost everywhere; hence `siteVar_prodWeight`.
* **`siteVar_act_prodProj_le`** — `μ[Var_v(Q_Λ f)] ≤ μ[Var_v(f)]`, the only
  inequality in the argument.
* **`ip_sub_act_prodProj_le_sum`** — the induction on `Λ`.
* **`approxTensorization_prodWeight`** — the headline: a product measure satisfies
  `1`-approximate tensorization of variance.
* **`spectralGapAtLeast_glauber_prodWeight`** — hence the Glauber dynamics of a
  product measure has spectral gap at least `1/n`, and
  **`glauber_mixesWithin_prodWeight`** — hence it mixes.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.GlauberTensorization
import Arlib.MarkovChains.Techniques.Transport
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Expanding a product of sums

`sum_prod_eq_prod_sum` is `Fintype.prod_sum` read in the direction this module
needs. -/

section ProdSum

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- **Expanding a product of sums**, in the direction this module uses it: a sum
over configurations of a product over sites is a product over sites of a sum over
spins.  Every appearance of the independence of the coordinates in this file goes
through this one identity. -/
theorem sum_prod_eq_prod_sum (g : V → S → ℝ) :
    ∑ τ : V → S, ∏ v, g v (τ v) = ∏ v, ∑ s, g v s :=
  (Fintype.prod_sum g).symm

end ProdSum

/-! ## Product weights

A *product weight* is `w σ = ∏_v φ_v(σ_v)`.  No positivity of the individual
`φ_v(s)` is assumed — only that each site normaliser `∑_s φ_v(s)` is positive,
which is exactly what is needed for the marginals to exist.  In particular a
product weight may vanish on configurations, as the hard-core model on the empty
graph does at activity `0`. -/

section ProdWeightBasic

variable {V : Type*} [Fintype V] {S : Type*}

/-- The **product weight** `w σ = ∏_v φ_v(σ_v)` attached to a family `φ` of
single-site weight functions. -/
def prodWeight (φ : V → S → ℝ) : (V → S) → ℝ := fun σ => ∏ v, φ v (σ v)

theorem prodWeight_apply (φ : V → S → ℝ) (σ : V → S) :
    prodWeight φ σ = ∏ v, φ v (σ v) := rfl

/-- A product of nonnegative site weights is nonnegative. -/
theorem prodWeight_nonneg {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (σ : V → S) :
    0 ≤ prodWeight φ σ := Finset.prod_nonneg fun v _ => hφ v (σ v)

/-- A product of positive site weights is positive. -/
theorem prodWeight_pos {φ : V → S → ℝ} (hφ : ∀ v s, 0 < φ v s) (σ : V → S) :
    0 < prodWeight φ σ := Finset.prod_pos fun v _ => hφ v (σ v)

end ProdWeightBasic

section ProdWeightZ

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- **The partition function of a product weight factorises**:
`Z(w) = ∏_v ∑_s φ_v(s)`.  A sum over `|S|^n` configurations collapses to a product
of `n` sums over `S`. -/
theorem Z_prodWeight (φ : V → S → ℝ) : Z (prodWeight φ) = ∏ v, ∑ s, φ v s := by
  rw [Z_apply]
  exact sum_prod_eq_prod_sum φ

/-- A product weight has positive total mass as soon as every site normaliser
does.  Note that no positivity of the individual weights is needed. -/
theorem Z_prodWeight_pos {φ : V → S → ℝ} (hc : ∀ v, 0 < ∑ s, φ v s) :
    0 < Z (prodWeight φ) := by
  rw [Z_prodWeight]
  exact Finset.prod_pos fun v _ => hc v

end ProdWeightZ

section Marginal

variable {V : Type*} {S : Type*} [Fintype S]

/-- The **site marginal** `p_v(s) = φ_v(s) / ∑_t φ_v(t)`: the law of the spin at
`v` under the Gibbs measure of the product weight. -/
noncomputable def prodMarginal (φ : V → S → ℝ) (v : V) (s : S) : ℝ := φ v s / ∑ t, φ v t

theorem prodMarginal_apply (φ : V → S → ℝ) (v : V) (s : S) :
    prodMarginal φ v s = φ v s / ∑ t, φ v t := rfl

theorem prodMarginal_nonneg {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) (v : V) (s : S) : 0 ≤ prodMarginal φ v s :=
  div_nonneg (hφ v s) (hc v).le

/-- Each site marginal is a probability distribution on the spins. -/
theorem sum_prodMarginal {φ : V → S → ℝ} (hc : ∀ v, 0 < ∑ s, φ v s) (v : V) :
    ∑ s, prodMarginal φ v s = 1 := by
  simp only [prodMarginal]
  rw [← Finset.sum_div, div_self (hc v).ne']

end Marginal

section GibbsProd

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- **The Gibbs measure of a product weight is the product of its marginals.**
This is the statement that "product weight" and "product measure" mean the same
thing; everything below is really about the measure, not the weight. -/
theorem gibbs_prodWeight {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) (σ : V → S) :
    gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) σ
      = ∏ v, prodMarginal φ v (σ v) := by
  simp only [prodMarginal]
  rw [gibbs_apply, prodWeight_apply, Z_prodWeight, ← Finset.prod_div_distrib]

/-- The Gibbs measure of a strictly positive product weight is fully supported. -/
theorem gibbs_prodWeight_pos {φ : V → S → ℝ} (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) (σ : V → S) :
    0 < gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc) σ :=
  div_pos (prodWeight_pos hφ σ) (Z_prodWeight_pos hc)

end GibbsProd

/-! ## Products of indicators

Two bookkeeping identities.  A product of `0/1` agreement indicators over a set of
sites is the indicator of "the two configurations agree on that set"; taken over
all of `V` this is the identity matrix, and taken over `V \ {v}` it is the
indicator of `AgreeOff v`. -/

section Indicators

variable {V : Type*} [Fintype V] {S : Type*} [DecidableEq S]

/-- A product of agreement indicators over all sites is the identity matrix. -/
theorem prod_ite_eq_indicator (σ τ : V → S) :
    ∏ u : V, (if τ u = σ u then (1 : ℝ) else 0) = if τ = σ then 1 else 0 := by
  by_cases h : τ = σ
  · rw [if_pos h]
    exact Finset.prod_eq_one fun u _ => if_pos (by rw [h])
  · rw [if_neg h]
    obtain ⟨u, hu⟩ : ∃ u, τ u ≠ σ u := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (mem_univ u) (if_neg hu)

end Indicators

section IndicatorsErase

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [DecidableEq S]

/-- A product of agreement indicators over the sites other than `v` is the
indicator of `AgreeOff v`. -/
theorem prod_ite_erase_eq_agreeOff (v : V) (σ τ : V → S) :
    ∏ u ∈ univ.erase v, (if τ u = σ u then (1 : ℝ) else 0)
      = if AgreeOff v σ τ then 1 else 0 := by
  by_cases h : AgreeOff v σ τ
  · rw [if_pos h]
    exact Finset.prod_eq_one fun u hu => if_pos (h u (Finset.mem_erase.mp hu).1).symm
  · rw [if_neg h]
    simp only [AgreeOff] at h
    push Not at h
    obtain ⟨u, hu, hne⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hu, mem_univ u⟩)
      (if_neg fun k => hne k.symm)

end IndicatorsErase

section EraseSplit

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*}

/-- Splitting a product weight off the site `v`. -/
theorem prodWeight_eq_mul_erase (φ : V → S → ℝ) (σ : V → S) (v : V) :
    prodWeight φ σ = φ v (σ v) * ∏ u ∈ univ.erase v, φ u (σ u) :=
  (Finset.mul_prod_erase univ (fun u => φ u (σ u)) (mem_univ v)).symm

end EraseSplit

/-! ## The projection kernels of a product measure

`prodProj hφ hc Λ` resamples the spins inside `Λ` independently from their
marginals and leaves the spins outside `Λ` untouched.  This is a *family* of
kernels indexed by the subsets of the site set, and its two structural properties
— reversibility and the composition law `Q_Λ ∘ Q_{Λ'} = Q_{Λ ∪ Λ'}` — are both
proved factorwise on the defining product, which is precisely where the product
structure of the measure is consumed. -/

section ProdProj

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable (φ : V → S → ℝ)

/-- The transition matrix of the **subset-resampling kernel** `Q_Λ`: from `σ`, draw
the spin at each site of `Λ` independently from its marginal and keep the spins off
`Λ`. -/
noncomputable def prodProjMat (Λ : Finset V) (σ τ : V → S) : ℝ :=
  ∏ v, (if v ∈ Λ then prodMarginal φ v (τ v) else if τ v = σ v then 1 else 0)

theorem prodProjMat_apply (Λ : Finset V) (σ τ : V → S) :
    prodProjMat φ Λ σ τ
      = ∏ v, (if v ∈ Λ then prodMarginal φ v (τ v) else if τ v = σ v then 1 else 0) := rfl

variable {φ}

theorem prodProjMat_nonneg (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (Λ : Finset V) (σ τ : V → S) : 0 ≤ prodProjMat φ Λ σ τ := by
  refine Finset.prod_nonneg fun v _ => ?_
  split
  · exact prodMarginal_nonneg hφ hc v (τ v)
  · split
    · exact zero_le_one
    · exact le_rfl

/-- Each row of `Q_Λ` is a probability distribution: the row is itself a product
measure, whose `v`-th factor is either a marginal or a point mass. -/
theorem sum_prodProjMat (hc : ∀ v, 0 < ∑ s, φ v s) (Λ : Finset V) (σ : V → S) :
    ∑ τ, prodProjMat φ Λ σ τ = 1 := by
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ univ) => prodProjMat_apply φ Λ σ τ,
    sum_prod_eq_prod_sum fun (v : V) (s : S) =>
      (if v ∈ Λ then prodMarginal φ v s else if s = σ v then 1 else 0)]
  refine Finset.prod_eq_one fun v _ => ?_
  by_cases hv : v ∈ Λ
  · simp only [if_pos hv]
    exact sum_prodMarginal hc v
  · simp [hv]

/-- The **subset-resampling kernel** `Q_Λ` of a product measure. -/
noncomputable def prodProj (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (Λ : Finset V) : FinChain (V → S) where
  P := prodProjMat φ Λ
  P_nonneg := prodProjMat_nonneg hφ hc Λ
  P_sum := sum_prodProjMat hc Λ

@[simp] theorem prodProj_apply (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (Λ : Finset V) (σ τ : V → S) : prodProj hφ hc Λ σ τ = prodProjMat φ Λ σ τ := rfl

/-- Resampling no sites is the identity. -/
theorem prodProjMat_empty (σ τ : V → S) :
    prodProjMat φ ∅ σ τ = if τ = σ then 1 else 0 := by
  rw [prodProjMat_apply, ← prod_ite_eq_indicator σ τ]
  exact Finset.prod_congr rfl fun v _ => if_neg (Finset.notMem_empty v)

/-- Resampling the single site `v` keeps the spins off `v` and draws the spin at
`v` from its marginal. -/
theorem prodProjMat_singleton (v : V) (σ τ : V → S) :
    prodProjMat φ {v} σ τ = prodMarginal φ v (τ v) * (if AgreeOff v σ τ then 1 else 0) := by
  have h2 : ∀ u ∈ univ.erase v,
      (if u ∈ ({v} : Finset V) then prodMarginal φ u (τ u) else if τ u = σ u then 1 else 0)
        = (if τ u = σ u then (1 : ℝ) else 0) := fun u hu =>
    if_neg (by simpa using (Finset.mem_erase.mp hu).1)
  rw [prodProjMat_apply, ← Finset.mul_prod_erase univ _ (mem_univ v),
    if_pos (Finset.mem_singleton_self v), Finset.prod_congr rfl h2,
    prod_ite_erase_eq_agreeOff]

/-- Resampling every site is the independent sampler: each row of `Q_univ` is the
Gibbs measure itself. -/
theorem prodProjMat_univ (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (σ τ : V → S) :
    prodProjMat φ univ σ τ
      = gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) τ := by
  rw [prodProjMat_apply, gibbs_prodWeight hφ hc]
  exact Finset.prod_congr rfl fun v _ => if_pos (mem_univ v)

/-- **The composition law.**  Resampling `Λ'` and then `Λ` resamples `Λ ∪ Λ'`:

  `Q_Λ ∘ Q_{Λ'} = Q_{Λ ∪ Λ'}`.

This is the one genuinely product-specific fact in the module, and everything else
is bookkeeping around it: taking `Λ' = Λ` it says the family consists of
idempotents, and comparing it with itself after `Finset.union_comm` it says the
family commutes.  The proof is a four-case evaluation of a single sum over the
spins at one site — the point being that after `sum_prod_eq_prod_sum` the sum over
intermediate *configurations* has become a product over sites of sums over
*spins*, which is where independence of the coordinates enters. -/
theorem prodProjMat_comp (hc : ∀ v, 0 < ∑ s, φ v s) (Λ Λ' : Finset V) (σ τ : V → S) :
    ∑ ρ, prodProjMat φ Λ σ ρ * prodProjMat φ Λ' ρ τ = prodProjMat φ (Λ ∪ Λ') σ τ := by
  have key : ∀ ρ : V → S, prodProjMat φ Λ σ ρ * prodProjMat φ Λ' ρ τ
      = ∏ v, ((if v ∈ Λ then prodMarginal φ v (ρ v) else if ρ v = σ v then 1 else 0)
          * (if v ∈ Λ' then prodMarginal φ v (τ v) else if τ v = ρ v then 1 else 0)) :=
    fun ρ => by rw [prodProjMat_apply, prodProjMat_apply, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun ρ (_ : ρ ∈ univ) => key ρ,
    sum_prod_eq_prod_sum fun (v : V) (s : S) =>
      ((if v ∈ Λ then prodMarginal φ v s else if s = σ v then 1 else 0)
        * (if v ∈ Λ' then prodMarginal φ v (τ v) else if τ v = s then 1 else 0)),
    prodProjMat_apply]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases h1 : v ∈ Λ
  · rw [if_pos (Finset.mem_union_left _ h1)]
    by_cases h2 : v ∈ Λ'
    · simp only [if_pos h1, if_pos h2, ← Finset.sum_mul, sum_prodMarginal hc v, one_mul]
    · simp only [if_pos h1, if_neg h2]
      simp
  · by_cases h2 : v ∈ Λ'
    · rw [if_pos (Finset.mem_union_right _ h2)]
      simp only [if_neg h1, if_pos h2, ← Finset.sum_mul]
      simp
    · rw [if_neg (by simp [h1, h2])]
      simp only [if_neg h1, if_neg h2]
      simp

end ProdProj

/-! ## `Q_Λ` is an orthogonal projection

Reversibility plus idempotence is all that is needed: the Dirichlet form of a
self-adjoint idempotent collapses to a difference of squared norms, and the
operator is an `L²(μ)`-contraction.  This repeats, for the whole family, the
argument `Chains/Glauber.lean` gives for a single site. -/

section Projection

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- **`Q_Λ` is reversible with respect to the Gibbs measure of the product
weight.**  Detailed balance holds factorwise: at a site of `Λ` both sides carry
`φ_v(σ_v) · φ_v(τ_v) / ∑_s φ_v(s)`, and at a site off `Λ` both sides vanish unless
the two configurations agree there, in which case they are equal on the nose. -/
theorem prodProj_reversible (Λ : Finset V) :
    Reversible (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (prodProj hφ hc Λ) := by
  intro σ τ
  rw [prodProj_apply, prodProj_apply, gibbs_apply, gibbs_apply, prodWeight_apply,
    prodWeight_apply, prodProjMat_apply, prodProjMat_apply, div_mul_eq_mul_div,
    div_mul_eq_mul_div]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ Λ
  · rw [if_pos hv, if_pos hv, prodMarginal_apply, prodMarginal_apply]
    ring
  · rw [if_neg hv, if_neg hv]
    by_cases h : τ v = σ v
    · rw [if_pos h, if_pos h.symm, h]
    · rw [if_neg h, if_neg fun k => h k.symm]
      ring

/-- The Gibbs measure of the product weight is stationary for `Q_Λ`. -/
theorem prodProj_stationary (Λ : Finset V) :
    Stationary (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (prodProj hφ hc Λ) := (prodProj_reversible hφ hc Λ).stationary

/-- The action of `Q_Λ` after `Q_{Λ'}` is the action of `Q_{Λ ∪ Λ'}`. -/
theorem act_prodProj_comp (Λ Λ' : Finset V) (f : (V → S) → ℝ) :
    (prodProj hφ hc Λ).act ((prodProj hφ hc Λ').act f)
      = (prodProj hφ hc (Λ ∪ Λ')).act f := by
  funext σ
  simp only [FinKernel.act_apply, prodProj_apply]
  calc ∑ ρ, prodProjMat φ Λ σ ρ * ∑ τ, prodProjMat φ Λ' ρ τ * f τ
      = ∑ ρ, ∑ τ, prodProjMat φ Λ σ ρ * prodProjMat φ Λ' ρ τ * f τ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
    _ = ∑ τ, ∑ ρ, prodProjMat φ Λ σ ρ * prodProjMat φ Λ' ρ τ * f τ := Finset.sum_comm
    _ = ∑ τ, prodProjMat φ (Λ ∪ Λ') σ τ * f τ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← Finset.sum_mul, prodProjMat_comp hc Λ Λ' σ τ]

/-- `Q_Λ` is idempotent: resampling the same block twice is resampling it once. -/
theorem act_prodProj_idem (Λ : Finset V) (f : (V → S) → ℝ) :
    (prodProj hφ hc Λ).act ((prodProj hφ hc Λ).act f) = (prodProj hφ hc Λ).act f := by
  rw [act_prodProj_comp hφ hc Λ Λ f, Finset.union_self]

/-- Resampling no sites does nothing. -/
theorem act_prodProj_empty (f : (V → S) → ℝ) : (prodProj hφ hc ∅).act f = f := by
  funext σ
  rw [FinKernel.act_apply]
  simp only [prodProj_apply, prodProjMat_empty]
  have h : ∀ τ : V → S, (if τ = σ then (1 : ℝ) else 0) * f τ = if τ = σ then f τ else 0 := by
    intro τ
    split <;> simp
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_ite_eq' univ σ f, if_pos (mem_univ σ)]

/-- **Resampling every site erases the function**: `Q_univ f` is the constant
`μ(f)`.  This is the top end of the telescoping identity. -/
theorem act_prodProj_univ (f : (V → S) → ℝ) :
    (prodProj hφ hc univ).act f
      = fun _ => Ex (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f := by
  funext σ
  rw [FinKernel.act_apply, Ex_apply]
  exact Finset.sum_congr rfl fun τ _ => by
    rw [prodProj_apply, prodProjMat_univ hφ hc σ τ]

/-- The self-adjoint-idempotent identity `⟪f, Q_Λ f⟫_μ = ⟪Q_Λ f, Q_Λ f⟫_μ`. -/
theorem ip_act_prodProj (Λ : Finset V) (f : (V → S) → ℝ) :
    ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f
        ((prodProj hφ hc Λ).act f)
      = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
          ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f) := by
  have h := ip_act_comm (prodProj_reversible hφ hc Λ) f ((prodProj hφ hc Λ).act f)
  rwa [act_prodProj_idem hφ hc Λ f] at h

/-- **The Dirichlet form of `Q_Λ` collapses**:
`ℰ_{Q_Λ}(f) = ⟪f, f⟫_μ - ⟪Q_Λ f, Q_Λ f⟫_μ`.  The exact analogue, for a block of
sites, of `dirichlet_siteChain`. -/
theorem dirichlet_prodProj (Λ : Finset V) (f : (V → S) → ℝ) :
    dirichlet (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (prodProj hφ hc Λ) f f
      = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f f
        - ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f) := by
  rw [dirichlet_apply, ip_act_prodProj hφ hc Λ f]

/-- **`Q_Λ` is an `L²(μ)`-contraction**: `‖Q_Λ f‖²_μ ≤ ‖f‖²_μ`.  This is the
inequality that makes the error term of the telescoping induction monotone. -/
theorem ip_act_prodProj_le (Λ : Finset V) (f : (V → S) → ℝ) :
    ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f)
      ≤ ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f f := by
  rw [← ip_act_prodProj hφ hc Λ f]
  exact ip_act_self_le (prodProj_stationary hφ hc Λ) f

/-- **The Pythagorean form**: `‖f - Q_Λ f‖²_μ = ‖f‖²_μ - ‖Q_Λ f‖²_μ`. -/
theorem ip_sub_act_prodProj_self (Λ : Finset V) (f : (V → S) → ℝ) :
    ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (fun σ => f σ - (prodProj hφ hc Λ).act f σ)
        (fun σ => f σ - (prodProj hφ hc Λ).act f σ)
      = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f f
        - ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f) := by
  set μ := gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) with hμ
  have expand : ∀ σ : V → S,
      μ σ * (f σ - (prodProj hφ hc Λ).act f σ) * (f σ - (prodProj hφ hc Λ).act f σ)
        = μ σ * f σ * f σ - 2 * (μ σ * f σ * (prodProj hφ hc Λ).act f σ)
          + μ σ * (prodProj hφ hc Λ).act f σ * (prodProj hφ hc Λ).act f σ :=
    fun σ => by ring
  have hsum : ip μ (fun σ => f σ - (prodProj hφ hc Λ).act f σ)
        (fun σ => f σ - (prodProj hφ hc Λ).act f σ)
      = ip μ f f - 2 * ip μ f ((prodProj hφ hc Λ).act f)
        + ip μ ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f) := by
    simp only [ip_apply]
    rw [Finset.sum_congr rfl fun σ _ => expand σ, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, ip_act_prodProj hφ hc Λ f]
  ring

end Projection

/-! ## The single-site update of a product weight

The heat-bath update at `v` is `Q_{v}`, but only `μ`-almost everywhere: off the
support of the Gibbs measure the local partition function may vanish and
`siteUpdate` then holds still by fiat, whereas `Q_{v}` still resamples.  The
`EqOnSupport` machinery of `Techniques/Transport.lean` is exactly what is needed to
ignore that discrepancy, since every quantity of the `L²(μ)` theory weights the row
at `σ` by `μ(σ)`. -/

section SingleSiteZloc

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- **The local partition function of a product weight factorises**:
`Zloc(σ, v) = (∑_s φ_v(s)) · ∏_{u ≠ v} φ_u(σ_u)`.  The first factor is the site
normaliser and the second is common to `Zloc` and to `w`, so it cancels in the
transition probabilities — which is why the update at `v` sees nothing of `σ`. -/
theorem Zloc_prodWeight (φ : V → S → ℝ) (σ : V → S) (v : V) :
    Zloc (prodWeight φ) σ v = (∑ s, φ v s) * ∏ u ∈ univ.erase v, φ u (σ u) := by
  rw [Zloc_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prodWeight_eq_mul_erase φ (update σ v s) v, update_self]
  congr 1
  exact Finset.prod_congr rfl fun u hu => by rw [update_of_ne (Finset.mem_erase.mp hu).1]

end SingleSiteZloc

section SingleSite

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- **The heat-bath update of a product weight resamples from the marginal.**  At a
configuration of positive weight the single-site update at `v` is exactly the
one-site resampling kernel `Q_{v}`: the new spin is drawn from `p_v`, with no
dependence on the rest of the configuration.  This is the concrete form of
"the coordinates are independent". -/
theorem siteUpdate_prodWeight (hc : ∀ v, 0 < ∑ s, φ v s) (v : V) {σ : V → S}
    (hσ : prodWeight φ σ ≠ 0) (τ : V → S) :
    siteUpdate (prodWeight φ) v σ τ = prodProjMat φ {v} σ τ := by
  have hR : (∏ u ∈ univ.erase v, φ u (σ u)) ≠ 0 := by
    intro h
    exact hσ (by rw [prodWeight_eq_mul_erase φ σ v, h, mul_zero])
  have hZl : Zloc (prodWeight φ) σ v ≠ 0 := by
    rw [Zloc_prodWeight]
    exact mul_ne_zero (hc v).ne' hR
  rw [siteUpdate_of_Zloc_ne_zero hZl, prodProjMat_singleton]
  by_cases hA : AgreeOff v σ τ
  · have hEq : (∏ u ∈ univ.erase v, φ u (τ u)) = ∏ u ∈ univ.erase v, φ u (σ u) :=
      Finset.prod_congr rfl fun u hu => by rw [hA u (Finset.mem_erase.mp hu).1]
    rw [if_pos hA, if_pos hA, mul_one, Zloc_prodWeight, prodWeight_eq_mul_erase φ τ v, hEq,
      prodMarginal_apply, div_eq_div_iff (mul_ne_zero (hc v).ne' hR) (hc v).ne']
    ring
  · rw [if_neg hA, if_neg hA, mul_zero]

/-- **The single-site heat-bath update of a product weight is `Q_{v}`,
`μ`-almost everywhere.**  They are not equal as matrices: where the local
partition function vanishes `siteUpdate` holds still while `Q_{v}` resamples.  But
those rows carry no Gibbs mass, so `Techniques/Transport.lean` lets the whole
`L²(μ)` theory be read off `Q_{v}` instead. -/
theorem siteChain_eqOnSupport_prodProj (hφ : ∀ v s, 0 ≤ φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) (v : V) :
    EqOnSupport (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (siteChain (prodWeight φ) (prodWeight_nonneg hφ) v) (prodProj hφ hc {v}) := by
  intro σ hσ τ
  exact siteUpdate_prodWeight hc v
    (fun h => hσ (gibbs_eq_zero (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) h)) τ

/-- **The mean conditional variance of a product measure**, in terms of the
resampling kernel: `μ[Var_v(f)] = ⟪f, f⟫_μ - ⟪Q_v f, Q_v f⟫_μ`. -/
theorem siteVar_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (v : V) (f : (V → S) → ℝ) :
    siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f
      = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f f
        - ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc {v}).act f) ((prodProj hφ hc {v}).act f) := by
  rw [siteVar_apply, (siteChain_eqOnSupport_prodProj hφ hc v).dirichlet_eq f f,
    dirichlet_prodProj hφ hc {v} f]

/-- The mean conditional variance as a squared distance:
`μ[Var_v(f)] = ‖f - Q_v f‖²_μ`. -/
theorem siteVar_prodWeight_eq_ip_sub (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (v : V) (f : (V → S) → ℝ) :
    siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f
      = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
          (fun σ => f σ - (prodProj hφ hc {v}).act f σ)
          (fun σ => f σ - (prodProj hφ hc {v}).act f σ) := by
  rw [siteVar_prodWeight hφ hc v f, ip_sub_act_prodProj_self hφ hc {v} f]

end SingleSite

/-! ## The telescoping induction

Everything is now in place.  The quantity `‖f‖² - ‖Q_Λ f‖²` is `0` at `Λ = ∅` and
`Var_μ(f)` at `Λ = univ`, and adding one site to `Λ` increases it by
`μ[Var_v(Q_Λ f)]`, which is at most `μ[Var_v(f)]`.  A `Finset.induction_on` on `Λ`
does the rest. -/

section Induction

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- **The commutation of the projections.**  For a product measure the single-site
resampling at `v` commutes with the block resampling at `Λ`, since both composites
are the resampling at `Λ ∪ {v}`. -/
theorem act_prodProj_comm (v : V) (Λ : Finset V) (f : (V → S) → ℝ) :
    (prodProj hφ hc Λ).act ((prodProj hφ hc {v}).act f)
      = (prodProj hφ hc {v}).act ((prodProj hφ hc Λ).act f) := by
  rw [act_prodProj_comp hφ hc Λ {v} f, act_prodProj_comp hφ hc {v} Λ f, Finset.union_comm]

/-- **The error term of the induction is monotone**:
`μ[Var_v(Q_Λ f)] ≤ μ[Var_v(f)]`.

By commutation, `Q_Λ f - Q_v Q_Λ f = Q_Λ (f - Q_v f)`, and `Q_Λ` is an
`L²(μ)`-contraction; so passing a function through `Q_Λ` can only decrease the mean
conditional variance at a site.  This is the only inequality in the whole proof —
everything else is an identity. -/
theorem siteVar_act_prodProj_le (v : V) (Λ : Finset V) (f : (V → S) → ℝ) :
    siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v
        ((prodProj hφ hc Λ).act f)
      ≤ siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f := by
  have hg : (fun σ => (prodProj hφ hc Λ).act f σ
        - (prodProj hφ hc {v}).act ((prodProj hφ hc Λ).act f) σ)
      = (prodProj hφ hc Λ).act (fun σ => f σ - (prodProj hφ hc {v}).act f σ) := by
    rw [FinKernel.act_sub, act_prodProj_comm hφ hc v Λ f]
  rw [siteVar_prodWeight_eq_ip_sub hφ hc v ((prodProj hφ hc Λ).act f), hg,
    siteVar_prodWeight_eq_ip_sub hφ hc v f]
  exact ip_act_prodProj_le hφ hc Λ (fun σ => f σ - (prodProj hφ hc {v}).act f σ)

/-- **The induction.**  For every set `Λ` of sites,

  `‖f‖²_μ - ‖Q_Λ f‖²_μ ≤ ∑_{v ∈ Λ} μ[Var_v(f)]`.

The base case `Λ = ∅` is `Q_∅ = id`.  For the step, the increment on adding a site
`a` is exactly `μ[Var_a(Q_Λ f)]` — this is `dirichlet_prodProj` for the singleton
`{a}` applied to `Q_Λ f`, i.e. the Pythagorean identity for the projection `Q_a` —
and `siteVar_act_prodProj_le` bounds it by `μ[Var_a(f)]`.  No ordering of the sites
appears: `Finset.induction_on` suffices because the statement is uniform in `Λ`. -/
theorem ip_sub_act_prodProj_le_sum (f : (V → S) → ℝ) (Λ : Finset V) :
    ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f f
        - ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc Λ).act f) ((prodProj hφ hc Λ).act f)
      ≤ ∑ v ∈ Λ, siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f := by
  refine Finset.induction_on Λ ?_ ?_
  · rw [Finset.sum_empty, act_prodProj_empty hφ hc f, sub_self]
  · intro a T ha ih
    have hstep : (prodProj hφ hc (insert a T)).act f
        = (prodProj hφ hc {a}).act ((prodProj hφ hc T).act f) := by
      rw [act_prodProj_comp hφ hc {a} T f, ← Finset.insert_eq]
    have h1 : siteVar (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) a
          ((prodProj hφ hc T).act f)
        = ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc T).act f) ((prodProj hφ hc T).act f)
          - ip (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
              ((prodProj hφ hc {a}).act ((prodProj hφ hc T).act f))
              ((prodProj hφ hc {a}).act ((prodProj hφ hc T).act f)) :=
      siteVar_prodWeight hφ hc a ((prodProj hφ hc T).act f)
    have h2 := siteVar_act_prodProj_le hφ hc a T f
    rw [Finset.sum_insert ha, hstep]
    linarith

end Induction

/-! ## The payoff

Approximate tensorization with the optimal constant `C = 1`, and the two
consequences `Chains/GlauberTensorization.lean` was built to draw from it. -/

section Payoff

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- **Tensorization of variance for a product measure.**

  `Var_μ(f) ≤ ∑_v μ[Var_v(f)]`

for `μ` the Gibbs measure of a product weight — that is, `ApproxTensorization`
holds with the optimal constant `C = 1`.  (No constant smaller than `1` is possible
for any measure: take `f` depending on a single site.)

This is the first weight for which the hypothesis of
`Chains/GlauberTensorization.lean` is discharged, so it is what makes the
equivalence proved there, and the mixing bound built on it, non-vacuous.

The proof is `ip_sub_act_prodProj_le_sum` at `Λ = univ`, where `Q_univ f` is the
constant `μ(f)` and the left-hand side becomes `⟪f, f⟫_μ - (μ f)² = Var_μ(f)`. -/
theorem approxTensorization_prodWeight :
    ApproxTensorization (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) 1 := by
  intro f
  have h := ip_sub_act_prodProj_le_sum hφ hc f univ
  rw [act_prodProj_univ hφ hc f, ip_const, ← Var_eq_ip_sub_sq] at h
  rw [one_mul]
  exact h

section Dynamics

variable [Nonempty V]

/-- **The Glauber dynamics of a product measure has spectral gap at least `1/n`.**

Combining `approxTensorization_prodWeight` with
`spectralGapAtLeast_glauber_of_approxTensorization`: the Gibbs sampler of a product
measure over `n` sites satisfies the Poincaré inequality with constant `1/n`, so
its relaxation time is at most `n`.  This is the exact answer — the coordinates are
independent, so `n` steps are needed just to touch every site — and it is the
calibration the general theory has to be consistent with. -/
theorem spectralGapAtLeast_glauber_prodWeight :
    SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) := by
  have h := spectralGapAtLeast_glauber_of_approxTensorization (C := 1) one_pos
    (approxTensorization_prodWeight hφ hc)
  rwa [one_mul] at h

end Dynamics

end Payoff

section Mixing

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 < φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
variable [Nonempty V]

/-- **End to end: the Gibbs sampler of a product measure mixes in `O(n · log …)`
steps.**

For a strictly positive product weight, the lazy Glauber dynamics is within
total-variation distance `ε` of the product measure `μ`, from *every* starting
configuration, after

  `t ≥ 2n · ln(1 / (2 ε √m))`

steps, where `m` is any lower bound on `μ`.  This is
`glauber_mixesWithin_of_approxTensorization` with its tensorization hypothesis
discharged at `C = 1` and its full-support hypothesis discharged from positivity of
the weight — the first time that theorem is applied to an actual measure.

The lower bound `m` is left as a hypothesis, exactly as in the general statement;
for a product weight one may take `m = ∏_v (min_s φ_v(s)) / ∏_v (∑_s φ_v(s))`. -/
theorem glauber_mixesWithin_prodWeight {m ε : ℝ} (hm : 0 < m)
    (hmin : ∀ σ, m ≤ gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc) σ)
    (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (2 * ε * Real.sqrt m)) ≤ (1 / (2 * (Fintype.card V : ℝ))) * t) :
    MixesWithin (glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)).lazy
      (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc)) ε t := by
  refine glauber_mixesWithin_of_approxTensorization (C := 1) le_rfl
    (approxTensorization_prodWeight (fun v s => (hφ v s).le) hc)
    (gibbs_prodWeight_pos hφ hc) hm hmin hε ?_
  rw [mul_one]
  exact ht

end Mixing

end Arlib.MarkovChains

