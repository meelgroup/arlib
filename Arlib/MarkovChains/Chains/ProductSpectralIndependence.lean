/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A product measure is pairwise independent at every pinning — the first instance of the
central theorem

`Chains.SpectralIndependenceMixing` proves the monograph's central implication:
spectral independence at *every* pinning gives the Glauber dynamics a Poincaré
inequality, and at `η = 1` the constant is exactly `1/n`.  It closes by observing
that **nothing in the development discharges that hypothesis for any concrete
weight**, so the theorem — and with it
`Techniques.SpectralIndependence.spectralIndependence_of_pairwiseIndep`, which had
no consumers — was an implication with an empty domain.  This module supplies the
first instance.

The instance is the product weight `w σ = ∏_v φ_v(σ_v)` of `Chains.ProductMeasure`,
and the reason it is the right one is the second half of the file: **a pinned
product weight is again a product weight**.  Conditioning a product measure on any
set of coordinates leaves a product measure, with a point mass in place of the
pinned marginals, so the hypothesis "spectral independence at every pinning"
collapses to the single unpinned computation.  This is the same "conditioning does
not leave the category" move that `Chains.Pinning` and `Chains.PinnedGlauber` are
built on, one level down: there it is the *weight* that stays a weight, here it is
the *product* structure that survives.

## The audit, and what it is worth

Feeding the two halves into
`SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_pairwiseIndep` gives

  `γ(P_Glauber) ≥ 1/n`  for the Gibbs sampler of a product measure,

through: pairwise independence ⟹ `SpectralIndependence … 1` ⟹ local gaps
`γ_j = 1` at every pinning ⟹ the Improved Random Walk Theorem ⟹ the Glauber gap.
That is `spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence`.

`ProductMeasure.spectralGapAtLeast_glauber_prodWeight` proves the *same statement*
by approximate tensorization of variance — a telescoping `Finset.induction_on`
over subsets of the sites, with no complex, no link, no local walk and no pinning
anywhere in it.  The two routes share only the definitions of `gibbs`, `glauber`
and `SpectralGapAtLeast`.

**They agree exactly, not up to a constant.**  Both conclude
`SpectralGapAtLeast μ P_Glauber (1 / (Fintype.card V : ℝ))` under the identical
hypotheses `hφ`, `hc`, `[Nonempty V]` — the two statements are literally the same
proposition, which is what `spectralGapAtLeast_glauber_prodWeight_audit` records by
proving that proposition twice, once along each route.  Neither route has slack at
this point: `1/n` is the exact relaxation time of the Glauber dynamics of a product
measure, since `n` steps are needed just to touch every site.  Two independent
proofs of the same constant is the strongest consistency check this area admits,
and it is now available.

## Main declarations

The module runs on four general facts about *any* spin system, which live in
`Techniques.LocalSpectralIndependence`: `spinEvent_eq_filter_agreesOn`,
`spinEvent₂_eq_filter_agreesOn`, `marg_gibbs_eq_Z_pinWeight` and
`joint_gibbs_eq_Z_pinWeight`, which say that the one- and two-site marginals of
a Gibbs measure are the partition functions of one- and two-site *pinnings*.
That is the form in which the product structure can be used at all, since
`pinWeight` of a product weight is again a product weight.

* **`prodPin`**, **`pinWeight_prodWeight`** — the pinned site weights, and the
  statement that **a pinned product weight is a product weight**:
  `pinWeight (prodWeight φ) Λ ζ = prodWeight (prodPin φ Λ ζ)`, an equality of
  functions, with `prodPin φ Λ ζ v` a point mass at `ζ v` for `v ∈ Λ` and `φ v`
  otherwise.
* `sum_prodPin`, `Z_pinWeight_prodWeight`, `sum_prodPin_pos` — the pinned
  partition function `∏_v (φ_v(ζ_v) or ∑_s φ_v(s))`, and the fact that its
  positivity forces positivity of every site normaliser of the pinned family (the
  converse is `ProductMeasure.Z_prodWeight_pos` read through
  `pinWeight_prodWeight`).  This is what lets the pinned instance be produced from
  the pinning hypothesis alone, with no extra positivity assumption.
* `Z_pinWeight_prodWeight_singleton`, `Z_pinWeight_prodWeight_pair`,
  **`Z_pinWeight_prodWeight_pair_mul`** — the factorisation
  `Z(pin{v,u}) · Z = Z(pin{v}) · Z(pin{u})`, which *is* pairwise independence in
  unnormalised form.
* **`marg_gibbs_prodWeight`** — `marg μ (v,s) = prodMarginal φ v s`: the marginal
  of `Techniques.SpectralIndependence` and the marginal of `Chains.ProductMeasure`
  are the same number.  They are defined in different files for different purposes
  and are *not* definitionally equal, so this reconciliation comes first.
* **`pairwiseIndep_gibbs_prodWeight`** and `joint_gibbs_prodWeight` — the Gibbs
  measure of a product weight has pairwise independent coordinates.  Note the
  hypotheses: only `0 ≤ φ v s` and `0 < ∑_s φ v s` are needed.  **No positivity of
  the individual weights is required** — a degenerate `φ` with vanishing, or even
  point-mass, marginals is still pairwise independent, and the statement is not
  vacuous there.
* **`pairwiseIndep_gibbsPin_prodWeight`**, `spectralIndependence_gibbsPin_prodWeight`
  — the same at every pinning, which is the shape
  `Chains.SpectralIndependenceMixing` consumes.
* **`spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence`** — the
  end-to-end result, and `spectralGapAtLeast_glauber_prodWeight_audit`, the
  two-route agreement.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.ProductMeasure
import Arlib.MarkovChains.Chains.SpectralIndependenceMixing

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## A pinned product weight is a product weight

This is the structural half of the module, and it is what makes "spectral
independence at *every* pinning" cost no more than the unpinned computation.
Pinning `Λ` to `ζ` replaces the site weight `φ v` by the point mass at `ζ v` for
each `v ∈ Λ`, and leaves the other sites alone; the resulting family is
`prodPin φ Λ ζ`, and the pinned weight is *literally* its product weight — an
equality of functions, not an equality of Gibbs measures.

Two consequences are recorded because both are consumed below.  The pinned
partition function factorises into one factor per site, so it is positive exactly
when every factor is; and each factor is the site normaliser of the pinned family.
Hence the pinning hypothesis `0 < Z (pinWeight …)` carried around by
`Chains.SpectralIndependenceMixing` is *exactly* the hypothesis `hc` that
`Chains.ProductMeasure` needs for the pinned family, with nothing left over. -/

section ProdPinDef

variable {V : Type*} [DecidableEq V] {S : Type*} [DecidableEq S] {φ : V → S → ℝ}

/-- The **pinned site weights**: at a pinned site `v ∈ Λ` the weight is
concentrated on the pinned spin `ζ v`, and elsewhere it is unchanged. -/
def prodPin (φ : V → S → ℝ) (Λ : Finset V) (ζ : V → S) : V → S → ℝ :=
  fun v s => if v ∈ Λ then (if s = ζ v then φ v s else 0) else φ v s

theorem prodPin_apply (φ : V → S → ℝ) (Λ : Finset V) (ζ : V → S) (v : V) (s : S) :
    prodPin φ Λ ζ v s = if v ∈ Λ then (if s = ζ v then φ v s else 0) else φ v s := rfl

theorem prodPin_nonneg (hφ : ∀ v s, 0 ≤ φ v s) (Λ : Finset V) (ζ : V → S) (v : V) (s : S) :
    0 ≤ prodPin φ Λ ζ v s := by
  rw [prodPin_apply]
  split
  · split
    · exact hφ v s
    · exact le_rfl
  · exact hφ v s

end ProdPinDef

section ProdPinWeight

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [DecidableEq S]

/-- **A pinned product weight is again a product weight.**

`pinWeight (prodWeight φ) Λ ζ = prodWeight (prodPin φ Λ ζ)`.

Both sides are read factorwise: on a configuration agreeing with the pinning
every factor is untouched, and on a configuration disagreeing at some `v ∈ Λ`
the `v`-th factor of the right-hand side is zero, which is what the `if` of
`pinWeight` does globally.

This is the analogue, one level down, of `Chains.Pinning`'s observation that
conditioning does not leave the category of weights: here the *product* structure
survives conditioning as well, which is why spectral independence has to be
proved only once and not once per pinning. -/
theorem pinWeight_prodWeight (φ : V → S → ℝ) (Λ : Finset V) (ζ : V → S) :
    pinWeight (prodWeight φ) Λ ζ = prodWeight (prodPin φ Λ ζ) := by
  funext σ
  rw [pinWeight_apply, prodWeight_apply, prodWeight_apply]
  by_cases h : AgreesOn Λ ζ σ
  · rw [if_pos h]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [prodPin_apply]
    by_cases hv : v ∈ Λ
    · rw [if_pos hv, if_pos (h v hv)]
    · rw [if_neg hv]
  · rw [if_neg h]
    simp only [AgreesOn] at h
    push Not at h
    obtain ⟨v, hv, hne⟩ := h
    refine (Finset.prod_eq_zero (mem_univ v) ?_).symm
    rw [prodPin_apply, if_pos hv, if_neg hne]

end ProdPinWeight

section ProdPinSum

variable {V : Type*} [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The site normaliser of the pinned family: the pinned spin's weight at a
pinned site, the original normaliser elsewhere. -/
theorem sum_prodPin (φ : V → S → ℝ) (Λ : Finset V) (ζ : V → S) (v : V) :
    ∑ s, prodPin φ Λ ζ v s = if v ∈ Λ then φ v (ζ v) else ∑ s, φ v s := by
  by_cases hv : v ∈ Λ
  · rw [if_pos hv,
      Finset.sum_congr rfl fun s (_ : s ∈ (univ : Finset S)) =>
        (by rw [prodPin_apply, if_pos hv] :
          prodPin φ Λ ζ v s = if s = ζ v then φ v s else 0)]
    simp
  · rw [if_neg hv]
    exact Finset.sum_congr rfl fun s _ => by rw [prodPin_apply, if_neg hv]

end ProdPinSum

section ProdPinZ

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- **The pinned partition function factorises.**  One factor per site: the
weight of the pinned spin at a pinned site, and the site normaliser elsewhere. -/
theorem Z_pinWeight_prodWeight (φ : V → S → ℝ) (Λ : Finset V) (ζ : V → S) :
    Z (pinWeight (prodWeight φ) Λ ζ)
      = ∏ v, (if v ∈ Λ then φ v (ζ v) else ∑ s, φ v s) := by
  rw [pinWeight_prodWeight, Z_prodWeight]
  exact Finset.prod_congr rfl fun v _ => sum_prodPin φ Λ ζ v

/-- **A charged pinning has a positive normaliser at every site.**

The hypothesis `0 < Z (pinWeight (prodWeight φ) Λ ζ)` — which is exactly what
`Chains.SpectralIndependenceMixing` quantifies its spectral-independence
assumption over — already gives the pinned family the hypothesis `hc` of
`Chains.ProductMeasure`.  Nothing else about the pinning is needed, and in
particular no positivity of the individual weights `φ v s`. -/
theorem sum_prodPin_pos (hφ : ∀ v s, 0 ≤ φ v s) {Λ : Finset V} {ζ : V → S}
    (hZ : 0 < Z (pinWeight (prodWeight φ) Λ ζ)) (v : V) :
    0 < ∑ s, prodPin φ Λ ζ v s := by
  rcases (Finset.sum_nonneg fun s (_ : s ∈ (univ : Finset S)) =>
      prodPin_nonneg hφ Λ ζ v s).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hZ' : Z (pinWeight (prodWeight φ) Λ ζ) = ∏ u, ∑ s, prodPin φ Λ ζ u s := by
      rw [pinWeight_prodWeight, Z_prodWeight]
    rw [hZ', Finset.prod_eq_zero (mem_univ v) heq.symm] at hZ
    exact lt_irrefl 0 hZ

end ProdPinZ

/-! ## The two-site factorisation

Pairwise independence in unnormalised form:
`Z(pin{v,u}) · Z = Z(pin{v}) · Z(pin{u})` for distinct sites `v ≠ u`.  Each of
the three pinned partition functions is a product over sites by
`Z_pinWeight_prodWeight`; splitting the pinned sites off with
`Finset.mul_prod_erase` leaves a common factor and the identity is `ring`.

This is where the independence of the coordinates is consumed, and it is the only
place. -/

section Factorisation

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The one-site pinned partition function: the weight of the pinned spin times
the normalisers of the other sites. -/
theorem Z_pinWeight_prodWeight_singleton (φ : V → S → ℝ) (v : V) (s : S) :
    Z (pinWeight (prodWeight φ) {v} (fun _ => s))
      = φ v s * ∏ u ∈ univ.erase v, ∑ t, φ u t := by
  rw [Z_pinWeight_prodWeight, ← Finset.mul_prod_erase univ _ (mem_univ v),
    if_pos (Finset.mem_singleton_self v)]
  congr 1
  exact Finset.prod_congr rfl fun u hu =>
    if_neg (by simpa using (Finset.mem_erase.mp hu).1)

/-- The two-site pinned partition function at distinct sites. -/
theorem Z_pinWeight_prodWeight_pair (φ : V → S → ℝ) {v u : V} (h : v ≠ u) (s t : S) :
    Z (pinWeight (prodWeight φ) {v, u} (fun x => if x = v then s else t))
      = φ v s * (φ u t * ∏ x ∈ (univ.erase v).erase u, ∑ r, φ x r) := by
  have hu' : u ∈ univ.erase v := Finset.mem_erase.mpr ⟨Ne.symm h, mem_univ u⟩
  rw [Z_pinWeight_prodWeight, ← Finset.mul_prod_erase univ _ (mem_univ v),
    ← Finset.mul_prod_erase (univ.erase v) _ hu',
    if_pos (Finset.mem_insert_self v {u}), if_pos rfl,
    if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self u)), if_neg (Ne.symm h)]
  congr 2
  refine Finset.prod_congr rfl fun x hx => ?_
  have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
  have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
  exact if_neg (by simp [hxu, hxv])

/-- **The two-site factorisation.**

  `Z(pin{v,u}) · Z(w) = Z(pin{v}) · Z(pin{u})`  for `v ≠ u`.

Divide through by `Z(w)²` and this is `joint = marg · marg`; it is stated
unnormalised because in that form it is an identity between products of site
weights, with no division and no positivity hypothesis at all. -/
theorem Z_pinWeight_prodWeight_pair_mul (φ : V → S → ℝ) {v u : V} (h : v ≠ u) (s t : S) :
    Z (pinWeight (prodWeight φ) {v, u} (fun x => if x = v then s else t)) * Z (prodWeight φ)
      = Z (pinWeight (prodWeight φ) {v} (fun _ => s))
        * Z (pinWeight (prodWeight φ) {u} (fun _ => t)) := by
  have herase : (univ.erase u).erase v = (univ.erase v).erase u := by
    ext x; simp only [Finset.mem_erase, mem_univ, and_true]; tauto
  have hu' : u ∈ univ.erase v := Finset.mem_erase.mpr ⟨Ne.symm h, mem_univ u⟩
  have hv' : v ∈ univ.erase u := Finset.mem_erase.mpr ⟨h, mem_univ v⟩
  rw [Z_pinWeight_prodWeight_pair φ h s t, Z_pinWeight_prodWeight_singleton,
    Z_pinWeight_prodWeight_singleton, Z_prodWeight,
    ← Finset.mul_prod_erase univ (fun x => ∑ r, φ x r) (mem_univ v),
    ← Finset.mul_prod_erase (univ.erase v) (fun x => ∑ r, φ x r) hu',
    ← Finset.mul_prod_erase (univ.erase u) (fun x => ∑ r, φ x r) hv', herase]
  ring

end Factorisation

/-! ## Pairwise independence of a product measure

The two halves meet.  `marg_gibbs_prodWeight` reconciles the marginal of
`Techniques.SpectralIndependence` with the one of `Chains.ProductMeasure` — they
are different definitions of the same number, and the identification is not
definitional — and `pairwiseIndep_gibbs_prodWeight` is the two-site statement.

**On the hypotheses.**  Only `0 ≤ φ v s` and `0 < ∑_s φ v s` appear.  Pairwise
independence does *not* need the marginals to be positive: a `φ` with vanishing
entries, or even a `φ` that is a point mass at some site (the pinned case), is
covered.  This matters, because the pinned families produced below are exactly of
that degenerate kind. -/

section PairwiseIndep

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- **The two marginals agree.**  `marg μ (v,s)`, built from `Pr` in
`Techniques.SpectralIndependence`, equals `prodMarginal φ v s = φ_v(s)/∑_t φ_v(t)`,
built from the weights in `Chains.ProductMeasure`.  The two definitions are made
for different purposes in different files and are not definitionally equal; this
is the reconciliation, and everything below is stated in terms of it. -/
theorem marg_gibbs_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    (v : V) (s : S) :
    marg (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) (v, s)
      = prodMarginal φ v s := by
  have hR : (∏ u ∈ univ.erase v, ∑ t, φ u t) ≠ 0 :=
    (Finset.prod_pos fun u _ => hc u).ne'
  have hv : (∑ t, φ v t) ≠ 0 := (hc v).ne'
  rw [marg_gibbs_eq_Z_pinWeight, Z_pinWeight_prodWeight_singleton, Z_prodWeight,
    ← Finset.mul_prod_erase univ (fun x => ∑ t, φ x t) (mem_univ v), prodMarginal_apply]
  field_simp

/-- **The Gibbs measure of a product weight has pairwise independent
coordinates.**

This is the first discharge of `Techniques.SpectralIndependence.PairwiseIndep` in
the development, and hence the first consumer of
`spectralIndependence_of_pairwiseIndep`.

The proof is not probabilistic.  `ProductMeasure.gibbs_prodWeight` says the Gibbs
measure *is* the product of its marginals, so the two-site statement has to be a
computation over `Finset.prod`; carried out on the pinned partition functions it is
exactly `Z_pinWeight_prodWeight_pair_mul`, `Z(pin{v,u}) · Z = Z(pin{v}) · Z(pin{u})`,
divided through by `Z²`.  The only hypotheses are nonnegativity of the weights and
positivity of the site normalisers — degenerate site weights are allowed. -/
theorem pairwiseIndep_gibbs_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s) :
    PairwiseIndep (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) := by
  rintro ⟨v, s⟩ ⟨u, t⟩ hvu
  have hZ : Z (prodWeight φ) ≠ 0 := (Z_prodWeight_pos hc).ne'
  rw [marg_gibbs_eq_Z_pinWeight, marg_gibbs_eq_Z_pinWeight,
    joint_gibbs_eq_Z_pinWeight _ _ hvu, div_mul_div_comm,
    ← Z_pinWeight_prodWeight_pair_mul φ hvu s t]
  field_simp

/-- The joint law of the spins at two distinct sites is the product of the two
site marginals, in the notation of `Chains.ProductMeasure`. -/
theorem joint_gibbs_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    {v u : V} (h : v ≠ u) (s t : S) :
    joint (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) (v, s) (u, t)
      = prodMarginal φ v s * prodMarginal φ u t := by
  rw [pairwiseIndep_gibbs_prodWeight hφ hc (v, s) (u, t) h, marg_gibbs_prodWeight hφ hc,
    marg_gibbs_prodWeight hφ hc]

end PairwiseIndep

/-! ## Every pinning at once

`Chains.SpectralIndependenceMixing` asks for its hypothesis at *every* pinning
carrying positive mass.  By `pinWeight_prodWeight` each such conditional measure
is the Gibbs measure of a product weight, and by `sum_prodPin_pos` the pinning
hypothesis is precisely the positivity that measure needs; so the quantifier
costs one rewrite. -/

section Pinned

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- **A conditional product measure is a product measure.**  The Gibbs measure of
a pinned product weight is the Gibbs measure of the pinned product weight family
`prodPin φ Λ ζ`, as distributions on the whole configuration space.  Stated as an
equality of `FinDist`s, so that no dependent rewriting under the positivity proofs
is ever needed. -/
theorem gibbsPin_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) {Λ : Finset V} {ζ : V → S}
    (hZ : 0 < Z (pinWeight (prodWeight φ) Λ ζ)) :
    gibbsPin (prodWeight φ) (prodWeight_nonneg hφ) Λ ζ hZ
      = gibbs (prodWeight (prodPin φ Λ ζ)) (prodWeight_nonneg (prodPin_nonneg hφ Λ ζ))
          (Z_prodWeight_pos (sum_prodPin_pos hφ hZ)) := by
  refine FinDist.ext fun σ => ?_
  rw [gibbsPin_apply, gibbs_apply, pinWeight_prodWeight]

/-- **Pairwise independence survives conditioning.**  Every conditional Gibbs
measure of a product weight has pairwise independent coordinates — including the
degenerate ones, where the pinned sites carry point masses.

This is the hypothesis of
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_pairwiseIndep`,
verbatim. -/
theorem pairwiseIndep_gibbsPin_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (Λ : Finset V) (ζ : V → S)
    (hZ : 0 < Z (pinWeight (prodWeight φ) Λ ζ)) :
    PairwiseIndep (gibbsPin (prodWeight φ) (prodWeight_nonneg hφ) Λ ζ hZ) := by
  rw [gibbsPin_prodWeight hφ hZ]
  exact pairwiseIndep_gibbs_prodWeight (prodPin_nonneg hφ Λ ζ) (sum_prodPin_pos hφ hZ)

/-- **Spectral independence with `η = 1` at every pinning.**  In the monograph's
normalisation this is `0`-spectral independence, the smallest constant available;
by `one_sub_marg_le_of_spectralIndependence` no smaller one is possible for a
measure with a marginal below `1`. -/
theorem spectralIndependence_gibbsPin_prodWeight (hφ : ∀ v s, 0 ≤ φ v s) (Λ : Finset V)
    (ζ : V → S) (hZ : 0 < Z (pinWeight (prodWeight φ) Λ ζ)) :
    SpectralIndependence (gibbsPin (prodWeight φ) (prodWeight_nonneg hφ) Λ ζ hZ) 1 :=
  spectralIndependence_of_pairwiseIndep (pairwiseIndep_gibbsPin_prodWeight hφ Λ ζ hZ)

end Pinned

/-! ## The end-to-end audit

The central theorem, instantiated.  Note which of its side conditions are met and
how: `η = 1` satisfies `η ≤ 3/2` with room (the binding constraint of the
assembly, and the one place where it is weaker than the monograph), `0 ≤ η` is
derived rather than assumed by `nonneg_of_spectralIndependence`, and `1 ≤ η` — the
hypothesis of the `div_card` form — holds with equality.  At `η = 1` every level
gap `siGamma` is `1`, every improved factor `Γ_i` is `1`, the sum of the `Γ_i` is
`n`, and the constant is `1/n` on the nose. -/

section Audit

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- **The Glauber dynamics of a product measure has spectral gap at least `1/n` —
through spectral independence.**

The full chain, with every hypothesis discharged:

```
  pairwise independence of the conditional measure at every pinning   (this file)
    ⟹ SpectralIndependence … 1                (spectralIndependence_of_pairwiseIndep)
    ⟹ γ(Q_τ) = 1 for the local walk at every pinning   (LocalSpectralIndependence)
    ⟹ γ(P^∨∧_n) ≥ Γ_{n−1}/∑_{i<n} Γ_i = 1/n              (ImprovedRandomWalk)
    ⟹ γ(P_Glauber) ≥ 1/n                                  (GlauberViaLevels)
```

`Chains.ProductMeasure.spectralGapAtLeast_glauber_prodWeight` proves **the same
statement** by approximate tensorization of variance, sharing with this route
nothing but the definitions of `gibbs`, `glauber` and `SpectralGapAtLeast`.  The
two constants agree *exactly* — see `spectralGapAtLeast_glauber_prodWeight_audit`
and the module docstring. -/
theorem spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence
    (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s) :
    SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 :=
    ⟨Fintype.card V - 1, by have := Fintype.card_pos (α := V); omega⟩
  exact spectralGapAtLeast_glauber_of_pairwiseIndep (prodWeight φ) (prodWeight_nonneg hφ)
    (Z_prodWeight_pos hc) hm fun Λ ζ hZΛ => pairwiseIndep_gibbsPin_prodWeight hφ Λ ζ hZΛ

/-- **The audit: two independent proofs of `1/n`.**

The proposition below is proved twice, once by each route — approximate
tensorization (`Chains.ProductMeasure`) on the left, spectral independence and the
Improved Random Walk Theorem (this file) on the right.  That both terms typecheck
against the *same* statement is the content: the two constants are not merely
comparable, they are the same real expression `1 / (Fintype.card V : ℝ)`, under
the same hypotheses, with no slack introduced by either route.

This is the strongest consistency check available in this area, and it also
retires the non-vacuity complaint that closes
`Chains.SpectralIndependenceMixing`: `spectralIndependence_of_pairwiseIndep` now
has a consumer, and the `η = 1 ⟹ 1/n` calibration is an audit rather than a
conditional. -/
theorem spectralGapAtLeast_glauber_prodWeight_audit
    (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s) :
    SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ))
      ∧ SpectralGapAtLeast (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) :=
  ⟨spectralGapAtLeast_glauber_prodWeight hφ hc,
    spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence hφ hc⟩

end Audit

end Arlib.MarkovChains

