/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The converse: a Poincaré inequality for the local walk gives spectral independence

`Techniques.LocalSpectralIndependence` proves `lem:QandPsi` — spectral
independence of the conditional measure gives the local walk `Q_η` a Poincaré
inequality — and it does so through the **exact identity**

`ℰ_{Q_η}(f) = m/(m−1) · Var_{π_{η,1}}(f) − quadForm (Cov μ_η) f̃ / (m(m−1))`,

`m = n − |Λ|` the number of free sites, `f̃ = freeRestrict Λ f`
(`dirichlet_pinLocalWalk`).  Because it is an identity and not an inequality,
reading it in the other direction costs nothing: a *lower* bound on `ℰ_{Q_η}`
is an *upper* bound on `quadForm (Cov μ_η)`, which is exactly the semidefinite
ordering `Cov ⪯ η · diag (marg)` that `Techniques.SpectralIndependence` takes as
the definition of spectral independence.  This module is that reading, and the
constants come out as exact inverses of each other:

* forward   `SpectralIndependence μ_η η` ⟹ gap `(m − η)/(m − 1)`;
* converse  gap `γ`                      ⟹ `SpectralIndependence μ_η (m − γ(m−1))`,

and `m − ((m − η)/(m − 1))·(m − 1) = η` on the nose, so the two compose to the
identity in both directions.  That equivalence is
`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk`, the headline here.

## What is proved *here*, and a correction to the obvious paraphrase

The monograph's converse — [CSV23, `lem:opt-relax-SI`], i.e. Zongchen Chen,
Daniel Štefankovič, Eric Vigoda, *Spectral Independence and Local-to-Global
Techniques for Optimal Mixing of Markov Chains*, arXiv:2307.13826 (2023), which
quotes it from Anari–Jain–Koehler–Pham–Vuong (which of their papers is meant is
not recorded anywhere in this library) — reads:

> if for any pinning `τ` on a subset `S` of vertices, **the Glauber dynamics**
> for `μ_τ` has relaxation time bounded by `≤ C·(n−|S|)`, then `μ` is
> `(C−1)`-spectrally independent.

The chain there is the *Glauber dynamics*, not the local walk `Q_τ`, and the
factor `n − |S|` is the Glauber slowdown (one site is resampled per step), which
the local walk does not have.  So `lem:opt-relax-SI` is **not** what this module
proves.  What is proved here is the local-walk converse: the exact inverse of
`spectralGapAtLeast_pinLocalWalk`, and the sharper statement per pinning.  The
shape of the constant does match: the monograph's `η` is our `η − 1`
(`Techniques.SpectralIndependence`), so its `(C−1)`-spectral independence is our
`C`-spectral independence, and `C` there plays the role of `m − γ(m−1)` here.

`lem:opt-relax-SI` itself is proved in `Chains.GlauberToSpectralIndependence`,
and by a route that needs no converse Random Walk Theorem: it never mentions the
local walk, but tests the Glauber Poincaré inequality at the *linear statistics*
`σ ↦ ∑_v a (v, σ v)`, where the left-hand side is the covariance form on the nose
(`quadForm_Cov`) and the right-hand side is
`(1/n)∑_v μ[Var_v]` (`dirichlet_glauber`).  That is
`spectralIndependence_pinned_of_relaxationTime_freeGlauber`, with the pinned
chain built honestly as `freeGlauber` — the mixture over the *free* sites, not
`glauber (pinWeight …)`, which carries holding probability `|Λ|/|V|`.  Composing
it with `spectralGapAtLeast_pinLocalWalk` gives the missing step in the form this
module could not supply,
`spectralGapAtLeast_pinLocalWalk_of_relaxationTime_freeGlauber`, and composing
further with `Chains.SpectralIndependenceMixing` closes the round trip
(`spectralGapAtLeast_glauber_of_optimalRelaxationTime`).

## Which quantifier moves

The quantifiers do **not** have to move together: one pinning's gap gives that
pinning's spectral independence.  The reason is `Cov_eq_zero_of_marg_eq_one` —
a site whose spin is already determined contributes a row of zeros to the
covariance form — so for a *pinned* measure `quadForm (Cov μ_τ)` cannot see the
pinned coordinates at all, and the test vectors `f̃` reachable from functions on
the free pairs already exhaust the form.  For an arbitrary weight `w` carrying a
free set `Λ` (the generality in which `pinDist` and `pinLocalWalk` are stated)
that is false, and the conclusion degrades to the restricted ordering
`quadForm (Cov μ) (freeRestrict Λ a) ≤ η ∑_p marg p · (freeRestrict Λ a p)²`.
That restricted form is
`quadForm_Cov_freeRestrict_le_marg_of_spectralGapAtLeast`, and being a pinned
weight is the only extra hypothesis anything here needs.

Two further notes on what the converse needs that the forward direction did not.

*No centering.*  The forward direction had to evaluate spectral independence at
a site shift of `f̃`, because it needed to turn a second moment into a variance
(`quadForm_Cov_add_site`).  Going the other way the inequality points the
friendly way — `m·Var_π(f) ≤ ∑_p marg p · f̃ p²` with the deficit
`(∑_p marg p · f̃ p)²/m` thrown away — and no shift is used anywhere below.  The
slack is recorded exactly in `numFree_mul_Var_pinDist`, and it costs nothing:
the round trip is still an equivalence.

*Non-degeneracy is free.*  The constant `m − γ(m−1)` must be nonnegative for the
last step (a second moment dominates `m·Var`, so the constant multiplying it
must not be negative).  This is not a hypothesis: `π_{η,1}` spreads over at
least two free sites, so the indicator of one free site has positive variance
(`Var_pinDist_siteIndicator`), and the identity together with `psd_Cov` then
forces `γ ≤ m/(m−1)` (`numFree_sub_mul_nonneg`).

* `numFree_mul_Var_pinDist`, `numFree_mul_Var_pinDist_le` — `m·Var_π(f)` against
  the second moment of `f̃`, exactly and then as an inequality.
* **`quadForm_Cov_freeRestrict_le_of_spectralGapAtLeast`** — the identity,
  rearranged: a gap `γ` bounds `quadForm (Cov μ) f̃` by `(m − γ(m−1))·m·Var_π(f)`.
* `exists_not_mem_of_card_succ_lt`, `freeRestrict_siteIndicator`,
  `sum_marg_siteIndicator`, `Var_pinDist_siteIndicator`,
  **`numFree_sub_mul_nonneg`** — the non-degeneracy of `π_{η,1}` and hence
  `0 ≤ m − γ(m−1)`.
* `marg_eq_zero_of_marg_eq_one`, **`Cov_eq_zero_of_marg_eq_one`** — a
  deterministic site is invisible to the covariance form.
* `quadForm_Cov_freeRestrict_eq`, `marg_gibbsPin_eq_one`,
  `exists_marg_gibbsPin_eq_one` — hence for a pinned measure the covariance form
  only sees the free pairs.
* **`quadForm_Cov_freeRestrict_le_marg_of_spectralGapAtLeast`** and
  `sum_marg_freeRestrict_sq_le` — the restricted ordering, in the second-moment
  shape that `SpectralIndependence` is stated against.
* **`spectralIndependence_of_spectralGapAtLeast_pinLocalWalk`** — the converse
  at a pinning, with constant `m − γ(m−1)`.
* **`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk`** — the two
  directions as a single equivalence, with no loss in either constant.
* `spectralIndependence_of_spectralGapAtLeast_pinLocalWalk_empty` and
  `spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty` — the
  unpinned case, where no zero-row argument is needed because
  `freeRestrict ∅ = id`, and which therefore holds for an arbitrary weight.

Everything here is proved from first principles with no `sorry`, and no
eigenvalue, spectrum or Hermitian matrix appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LocalSpectralIndependence

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The variance of `π_{η,1}` against a second moment

`ip_pinDist_self` and `Ex_pinDist` express the two moments of `π_{η,1}` as sums
against `marg`, divided by `m`.  Combining them gives `m·Var_π(f)` as a second
moment minus a nonnegative deficit; throwing the deficit away is the only slack
in this module, and the round trip below shows it costs nothing. -/

section VarBound

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **`m` times the variance under `π_{η,1}`, exactly.**

`m · Var_{π_{η,1}}(f) = ∑_p marg p · f̃ p² − (∑_p marg p · f̃ p)² / m`,

with `m = n − |Λ|` and `f̃ = freeRestrict Λ f`.  The subtracted term is the
square of the mean, and it is the entire difference between the second moment
that spectral independence bounds and the variance that the Poincaré inequality
bounds. -/
theorem numFree_mul_Var_pinDist (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card < Fintype.card V) (f : V × S → ℝ) :
    numFree Λ * Var (pinDist w Λ hw hZ hΛ) f
      = (∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p ^ 2)
        - (∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p) ^ 2 / numFree Λ := by
  have hN : numFree Λ ≠ 0 := (numFree_pos hΛ).ne'
  rw [Var_eq_ip_sub_sq, ip_pinDist_self w Λ hw hZ hΛ f, Ex_pinDist w Λ hw hZ hΛ f]
  field_simp

/-- **`m·Var_π(f)` is at most the second moment of `f̃`.**  The deficit thrown
away is the square of the mean; see `numFree_mul_Var_pinDist`. -/
theorem numFree_mul_Var_pinDist_le (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card < Fintype.card V) (f : V × S → ℝ) :
    numFree Λ * Var (pinDist w Λ hw hZ hΛ) f
      ≤ ∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p ^ 2 := by
  have hN : 0 < numFree Λ := numFree_pos hΛ
  have hdef : 0 ≤ (∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p) ^ 2 / numFree Λ :=
    div_nonneg (sq_nonneg _) hN.le
  rw [numFree_mul_Var_pinDist]
  linarith

end VarBound

/-! ## The identity, rearranged

This is the whole mathematical content of the module.  `dirichlet_pinLocalWalk`
is an equation between `ℰ_{Q_η}(f)`, `Var_{π_{η,1}}(f)` and
`quadForm (Cov μ) f̃`; solving it for the covariance term turns a Poincaré
inequality into a bound on the covariance form. -/

section Rearrange

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The rearranged identity.**

If the local walk `Q_η` has Poincaré constant `γ` with respect to `π_{η,1}`,
then for every `f`

`quadForm (Cov μ) (freeRestrict Λ f) ≤ (m − γ(m−1)) · (m · Var_{π_{η,1}}(f))`,

with `m = n − |Λ|`.  This is `dirichlet_pinLocalWalk` solved for the covariance
term and nothing else; the hypothesis is used only at the single `f` in
question, so the statement is really a pointwise rearrangement of the identity.

Note that this holds for an *arbitrary* nonnegative weight `w`: the set `Λ`
enters only through the counting of free sites.  Upgrading the conclusion from
the restricted vectors `freeRestrict Λ f` to all vectors is where `w` has to be
a pinned weight; see `quadForm_Cov_freeRestrict_eq`. -/
theorem quadForm_Cov_freeRestrict_le_of_spectralGapAtLeast (w : (V → S) → ℝ) (Λ : Finset V)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) {γ : ℝ}
    (hgap : SpectralGapAtLeast (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk w Λ hw hΛ) γ) (f : V × S → ℝ) :
    quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f)
      ≤ (numFree Λ - γ * (numFree Λ - 1))
          * (numFree Λ * Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f) := by
  have hN : 0 < numFree Λ := numFree_pos (Nat.lt_of_succ_lt hΛ)
  have hN1 : 0 < numFree Λ - 1 := by
    have := one_lt_numFree hΛ
    linarith
  have hprod : 0 < numFree Λ * (numFree Λ - 1) := mul_pos hN hN1
  set V₀ : ℝ := Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f with hV₀
  set C : ℝ := quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f) with hC
  have hid := dirichlet_pinLocalWalk w Λ hw hZ hΛ f
  have hg := hgap f
  rw [hid] at hg
  have hdiv : C / (numFree Λ * (numFree Λ - 1))
      ≤ numFree Λ / (numFree Λ - 1) * V₀ - γ * V₀ := by linarith
  have hmul := (div_le_iff₀ hprod).mp hdiv
  have heq : (numFree Λ / (numFree Λ - 1) * V₀ - γ * V₀) * (numFree Λ * (numFree Λ - 1))
      = (numFree Λ - γ * (numFree Λ - 1)) * (numFree Λ * V₀) := by
    field_simp
  linarith [heq ▸ hmul]

end Rearrange

/-! ## `π_{η,1}` is not a point mass

The last step of the converse multiplies a second moment by the constant
`m − γ(m−1)`, so that constant must be nonnegative.  It is, and no hypothesis is
needed: `π_{η,1}` charges at least two free sites, so the indicator of one free
site is a function of positive variance, and the identity plus `psd_Cov` then
caps `γ` at `m/(m−1)`. -/

section Indicator

variable {V : Type*} [DecidableEq V] {S : Type*}

/-- The indicator of a free site, restricted to the free pairs, is itself: the
restriction is invisible because the site is free. -/
theorem freeRestrict_siteIndicator {Λ : Finset V} {v₀ : V} (hv₀ : v₀ ∉ Λ) :
    freeRestrict Λ (fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0)
      = fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0 := by
  funext p
  rw [freeRestrict_apply]
  by_cases h : p.1 = v₀
  · rw [if_neg (by rw [h]; exact hv₀)]
  · rw [if_neg h]
    split <;> rfl

end Indicator

section NonDegenerate

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- With at least two free sites there is a free site to point at. -/
theorem exists_not_mem_of_card_succ_lt {Λ : Finset V} (hΛ : Λ.card + 1 < Fintype.card V) :
    ∃ v : V, v ∉ Λ := by
  by_contra hc
  push Not at hc
  have : (univ : Finset V) ⊆ Λ := fun v _ => hc v
  have hle : Fintype.card V ≤ Λ.card := by
    simpa [Finset.card_univ] using Finset.card_le_card this
  omega

/-- The marginals sum to one over the pairs at a fixed site, read on `V × S`. -/
theorem sum_marg_siteIndicator (μ : FinDist (V → S)) (v₀ : V) :
    (∑ p : V × S, marg μ p * (if p.1 = v₀ then (1 : ℝ) else 0)) = 1 := by
  have hstep : ∀ v : V,
      (∑ s : S, marg μ (v, s) * (if ((v, s) : V × S).1 = v₀ then (1 : ℝ) else 0))
        = if v = v₀ then (1 : ℝ) else 0 := by
    intro v
    by_cases h : v = v₀
    · subst h
      rw [if_pos rfl, Finset.sum_congr rfl fun s _ => by rw [if_pos rfl, mul_one], sum_marg]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun s _ => by rw [if_neg h, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun v _ => hstep v,
    Finset.sum_ite_eq' univ v₀ fun _ => (1 : ℝ), if_pos (Finset.mem_univ _)]

/-- **The indicator of a free site has variance `1/m − 1/m²` under `π_{η,1}`.**
In particular it is positive as soon as there are two free sites, so `π_{η,1}`
is never a point mass and the Poincaré inequality for `Q_η` has content. -/
theorem Var_pinDist_siteIndicator (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card < Fintype.card V) {v₀ : V} (hv₀ : v₀ ∉ Λ) :
    Var (pinDist w Λ hw hZ hΛ) (fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0)
      = 1 / numFree Λ - 1 / numFree Λ ^ 2 := by
  have hN : numFree Λ ≠ 0 := (numFree_pos hΛ).ne'
  have hfr : freeRestrict Λ (fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0)
      = fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0 := freeRestrict_siteIndicator hv₀
  have hA : (∑ p : V × S, marg (gibbs w hw hZ) p
      * freeRestrict Λ (fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0) p) = 1 := by
    simp only [hfr]
    exact sum_marg_siteIndicator _ v₀
  have hB : (∑ p : V × S, marg (gibbs w hw hZ) p
      * freeRestrict Λ (fun p : V × S => if p.1 = v₀ then (1 : ℝ) else 0) p ^ 2) = 1 := by
    refine Eq.trans ?_ hA
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hfr]
    by_cases h : p.1 = v₀ <;> simp [h]
  rw [Var_eq_ip_sub_sq, ip_pinDist_self w Λ hw hZ hΛ _, Ex_pinDist w Λ hw hZ hΛ _, hA, hB]
  field_simp

/-- **The constant produced by the converse is nonnegative.**

A Poincaré constant for `Q_η` can never exceed `m/(m−1)`: the identity
`dirichlet_pinLocalWalk` writes `ℰ_{Q_η}(f)` as `m/(m−1)·Var_π(f)` minus a
nonnegative quantity (`psd_Cov`), and `Var_pinDist_siteIndicator` supplies a
test function of positive variance.  Hence `0 ≤ m − γ(m−1)`, which is what the
final step of the converse needs and which is *not* an extra hypothesis. -/
theorem numFree_sub_mul_nonneg (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) {γ : ℝ}
    (hgap : SpectralGapAtLeast (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk w Λ hw hΛ) γ) :
    0 ≤ numFree Λ - γ * (numFree Λ - 1) := by
  have hN : 0 < numFree Λ := numFree_pos (Nat.lt_of_succ_lt hΛ)
  have hN1 : 1 < numFree Λ := one_lt_numFree hΛ
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_of_card_succ_lt hΛ
  set f : V × S → ℝ := fun p => if p.1 = v₀ then (1 : ℝ) else 0 with hf
  have hvar : Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f
      = 1 / numFree Λ - 1 / numFree Λ ^ 2 :=
    Var_pinDist_siteIndicator w Λ hw hZ (Nat.lt_of_succ_lt hΛ) hv₀
  have hpos : 0 < numFree Λ * Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f := by
    rw [hvar]
    have h1 : numFree Λ * (1 / numFree Λ - 1 / numFree Λ ^ 2)
        = (numFree Λ - 1) / numFree Λ := by
      field_simp
    rw [h1]
    exact div_pos (by linarith) hN
  have hle := quadForm_Cov_freeRestrict_le_of_spectralGapAtLeast w Λ hw hZ hΛ hgap f
  have h0 : 0 ≤ quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f) :=
    (psd_Cov (gibbs w hw hZ)).nonneg _
  nlinarith

end NonDegenerate

/-! ## A deterministic site is invisible to the covariance form

For a *pinned* measure the pinned sites carry no randomness, and a site with no
randomness contributes a row of zeros to `Cov`.  This is the step that lets one
pinning's gap give that pinning's spectral independence, with no coupling of
quantifiers: the vectors `freeRestrict Λ a` already exhaust the covariance form
of `μ_τ`. -/

section Deterministic

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {μ : FinDist (V → S)}

/-- **A site with a sure spin has no other charged spin.** -/
theorem marg_eq_zero_of_marg_eq_one {v : V} {s t : S} (h : marg μ (v, s) = 1) (ht : t ≠ s) :
    marg μ (v, t) = 0 := by
  have hsum : ∑ u, marg μ (v, u) = 1 := sum_marg v
  have hsub : ∑ u ∈ ({s, t} : Finset S), marg μ (v, u) ≤ ∑ u, marg μ (v, u) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun u _ _ => marg_nonneg (v, u)
  rw [Finset.sum_pair (Ne.symm ht)] at hsub
  have hnn : 0 ≤ marg μ (v, t) := marg_nonneg (v, t)
  rw [hsum, h] at hsub
  linarith

/-- **A deterministic site contributes a row of zeros to the covariance form.**

If `μ` puts all its mass on the spin `s` at the site `v`, then
`Cov μ (v, t) q = 0` for every spin `t` and every pair `q`.  For `t ≠ s` both
terms of `joint − marg·marg` vanish outright; for `t = s` the event `σ v = s`
has probability one, so the joint probability equals the marginal of `q` and the
two terms cancel.

This is the exact statement that makes the converse a per-pinning result: for a
conditional measure `μ_τ` the pinned coordinates are already decided, so the
covariance form of `μ_τ` does not see them. -/
theorem Cov_eq_zero_of_marg_eq_one {v : V} {s : S} (h : marg μ (v, s) = 1) (t : S)
    (q : V × S) : Cov μ (v, t) q = 0 := by
  by_cases ht : t = s
  · subst ht
    have e1 : marg μ q - joint μ (v, t) q
        = ∑ σ, μ σ * spinInd q σ * (1 - spinInd (v, t) σ) := by
      rw [marg_eq_sum, joint_eq_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun σ _ => by ring
    have e2 : (1 : ℝ) - marg μ (v, t) = ∑ σ, μ σ * (1 - spinInd (v, t) σ) := by
      have hsplit : ∑ σ, μ σ * (1 - spinInd (v, t) σ)
          = (∑ σ, μ σ) - ∑ σ, μ σ * spinInd (v, t) σ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun σ _ => by ring
      rw [hsplit, μ.sum_coe, marg_eq_sum]
    have e3 : ∑ σ, μ σ * spinInd q σ * (1 - spinInd (v, t) σ)
        ≤ ∑ σ, μ σ * (1 - spinInd (v, t) σ) := by
      refine Finset.sum_le_sum fun σ _ => ?_
      have hq1 : spinInd q σ ≤ 1 := by
        simp only [spinInd]; split <;> norm_num
      have hq0 : 0 ≤ spinInd q σ := by
        simp only [spinInd]; split <;> norm_num
      have hrest : 0 ≤ μ σ * (1 - spinInd (v, t) σ) := by
        refine mul_nonneg (μ.coe_nonneg σ) ?_
        simp only [spinInd]; split <;> norm_num
      nlinarith
    have hge : joint μ (v, t) q ≤ marg μ q := by
      rw [joint_symm]
      exact joint_le_marg q (v, t)
    rw [← e2, h] at e3
    have e4 : marg μ q - joint μ (v, t) q ≤ 0 := by
      rw [e1]
      linarith
    rw [Cov_apply, h, one_mul]
    linarith
  · have hzero : marg μ (v, t) = 0 := marg_eq_zero_of_marg_eq_one h ht
    have hj : joint μ (v, t) q = 0 :=
      le_antisymm (hzero ▸ joint_le_marg (v, t) q) (joint_nonneg _ _)
    rw [Cov_apply, hj, hzero, zero_mul, sub_zero]

/-- **Restricting to the free pairs does not change the covariance form**, when
every pinned site has a sure spin.  Both the row and the column at a pinned site
are zero (the form is symmetric), so the terms `freeRestrict` deletes were zero
already. -/
theorem quadForm_Cov_freeRestrict_eq (Λ : Finset V)
    (hdet : ∀ v ∈ Λ, ∃ s : S, marg μ (v, s) = 1) (a : V × S → ℝ) :
    quadForm (Cov μ) (freeRestrict Λ a) = quadForm (Cov μ) a := by
  have hrow : ∀ p q : V × S, p.1 ∈ Λ → Cov μ p q = 0 := by
    intro p q hp
    obtain ⟨s, hs⟩ := hdet p.1 hp
    have := Cov_eq_zero_of_marg_eq_one hs p.2 q
    rwa [Prod.mk.eta] at this
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : p.1 ∈ Λ
  · rw [hrow p q hp]; ring
  · by_cases hq : q.1 ∈ Λ
    · rw [Cov_symm, hrow q p hq]; ring
    · rw [freeRestrict_of_not_mem hp, freeRestrict_of_not_mem hq]

end Deterministic

/-! ## The pinned marginals

`Chains.PinnedGlauber.siteMarginal_pinWeight_of_mem` already says the marginal
at an already-pinned site is a point mass; translated through `marg_gibbs` it is
exactly the hypothesis `Cov_eq_zero_of_marg_eq_one` wants. -/

section PinnedMarg

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The pinned marginal is a point mass.**  `marg (μ_τ) (v, τ v) = 1` at every
pinned site `v ∈ Λ`. -/
theorem marg_gibbsPin_eq_one (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (τ : V → S)
    (hZ : 0 < Z (pinWeight w Λ τ)) {v : V} (hv : v ∈ Λ) :
    marg (gibbsPin w hw Λ τ hZ) (v, τ v) = 1 := by
  have hd := congrFun (congrArg FinDist.p
    (siteMarginal_pinWeight_of_mem w hw hZ hv)) (τ v)
  rw [siteMarginal_apply, FinDist.dirac_apply, if_pos rfl] at hd
  rw [show gibbsPin w hw Λ τ hZ = gibbs (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) hZ from rfl,
    marg_gibbs]
  exact hd

/-- Every pinned site of a conditional Gibbs measure is deterministic — the
hypothesis of `quadForm_Cov_freeRestrict_eq`. -/
theorem exists_marg_gibbsPin_eq_one (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V)
    (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ)) (v : V) (hv : v ∈ Λ) :
    ∃ s : S, marg (gibbsPin w hw Λ τ hZ) (v, s) = 1 :=
  ⟨τ v, marg_gibbsPin_eq_one w hw Λ τ hZ hv⟩

end PinnedMarg

/-! ## The converse

The three pieces assemble.  For an arbitrary weight the conclusion is the
restricted ordering; for a pinned weight the restriction is vacuous and the
conclusion is spectral independence on the nose. -/

section Converse

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The restricted ordering.**

For an arbitrary nonnegative weight `w` with free set `Λ`, a Poincaré constant
`γ` for `Q_η` bounds the covariance form on the vectors supported on the free
pairs:

`quadForm (Cov μ) (freeRestrict Λ a) ≤ (m − γ(m−1)) · ∑_p marg p · (freeRestrict Λ a p)²`.

This is spectral independence *restricted to the free coordinates*, and it is
all that the identity gives without knowing that `w` is a pinned weight. -/
theorem quadForm_Cov_freeRestrict_le_marg_of_spectralGapAtLeast (w : (V → S) → ℝ)
    (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V)
    {γ : ℝ} (hgap : SpectralGapAtLeast (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk w Λ hw hΛ) γ) (a : V × S → ℝ) :
    quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ a)
      ≤ (numFree Λ - γ * (numFree Λ - 1))
          * ∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ a p ^ 2 := by
  have hK : 0 ≤ numFree Λ - γ * (numFree Λ - 1) := numFree_sub_mul_nonneg w Λ hw hZ hΛ hgap
  have h1 := quadForm_Cov_freeRestrict_le_of_spectralGapAtLeast w Λ hw hZ hΛ hgap a
  have h2 := numFree_mul_Var_pinDist_le w Λ hw hZ (Nat.lt_of_succ_lt hΛ) a
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

/-- Restricting to the free pairs can only shrink a second moment. -/
theorem sum_marg_freeRestrict_sq_le (μ : FinDist (V → S)) (Λ : Finset V) (a : V × S → ℝ) :
    (∑ p : V × S, marg μ p * freeRestrict Λ a p ^ 2)
      ≤ ∑ p : V × S, marg μ p * a p ^ 2 := by
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p.1 ∈ Λ
  · rw [freeRestrict_of_mem hp]
    have : 0 ≤ marg μ p * a p ^ 2 := mul_nonneg (marg_nonneg p) (sq_nonneg _)
    simpa using this
  · rw [freeRestrict_of_not_mem hp]

/-- **The converse of `lem:QandPsi`, at a pinning.**

If the local walk `Q_τ` at the pinning `τ` on `Λ` has Poincaré constant `γ` with
respect to `π_{τ,1}`, then the conditional Gibbs measure `μ_τ` is
`(m − γ(m−1))`-spectrally independent, `m = n − |Λ|`.

Everything is the rearranged identity: `dirichlet_pinLocalWalk` turns the
Poincaré inequality into an upper bound on `quadForm (Cov μ_τ) f̃`,
`numFree_mul_Var_pinDist_le` replaces `m·Var_π` by the second moment that
spectral independence is stated against, and `quadForm_Cov_freeRestrict_eq`
removes the restriction to free pairs — the pinned sites are deterministic, so
the covariance form never saw them.  No centering and no site shift is used, in
contrast with the forward direction.

The constant is the exact inverse of the forward one; see
`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk`. -/
theorem spectralIndependence_of_spectralGapAtLeast_pinLocalWalk (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ))
    (hΛ : Λ.card + 1 < Fintype.card V) {γ : ℝ}
    (hgap : SpectralGapAtLeast
      (pinDist (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hΛ) γ) :
    SpectralIndependence (gibbsPin w hw Λ τ hZ) (numFree Λ - γ * (numFree Λ - 1)) := by
  refine (spectralIndependence_iff _).mpr fun a => ?_
  have hK : 0 ≤ numFree Λ - γ * (numFree Λ - 1) :=
    numFree_sub_mul_nonneg (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ hΛ hgap
  have hfree : quadForm (Cov (gibbsPin w hw Λ τ hZ)) (freeRestrict Λ a)
      = quadForm (Cov (gibbsPin w hw Λ τ hZ)) a :=
    quadForm_Cov_freeRestrict_eq Λ (exists_marg_gibbsPin_eq_one w hw Λ τ hZ) a
  have hbound : quadForm (Cov (gibbsPin w hw Λ τ hZ)) (freeRestrict Λ a)
      ≤ (numFree Λ - γ * (numFree Λ - 1))
          * ∑ p : V × S, marg (gibbsPin w hw Λ τ hZ) p * freeRestrict Λ a p ^ 2 :=
    quadForm_Cov_freeRestrict_le_marg_of_spectralGapAtLeast
      (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ hΛ hgap a
  have hmom := sum_marg_freeRestrict_sq_le (gibbsPin w hw Λ τ hZ) Λ a
  rw [hfree] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hmom hK)

/-- **Spectral independence and the local-walk Poincaré inequality are
equivalent, with no loss in either constant.**

`μ_τ` is `η`-spectrally independent **iff** the local walk `Q_τ` has Poincaré
constant `(m − η)/(m − 1)`, where `m = n − |Λ|` is the number of free sites.

The forward direction is `spectralGapAtLeast_pinLocalWalk_pinned`
(`Techniques.LocalSpectralIndependence`); the backward direction is the theorem
above, whose constant `m − γ(m−1)` evaluates at `γ = (m − η)/(m − 1)` to exactly
`η`.  Both directions are consequences of the *same* identity
`dirichlet_pinLocalWalk`, which is why nothing is lost: an identity read from
left to right and from right to left.

In the monograph's normalisation (our `η` is its `1 + η`) the right-hand side is
`γ(Q_τ) ≥ 1 − η_monograph/(n − |Λ| − 1)`, so this says that bound is not merely
sufficient but *characteristic* of spectral independence at that pinning. -/
theorem spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ))
    (hΛ : Λ.card + 1 < Fintype.card V) (η : ℝ) :
    SpectralIndependence (gibbsPin w hw Λ τ hZ) η
      ↔ SpectralGapAtLeast
          (pinDist (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ (Nat.lt_of_succ_lt hΛ))
          (pinLocalWalk (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hΛ)
          ((numFree Λ - η) / (numFree Λ - 1)) := by
  have hN1 : numFree Λ - 1 ≠ 0 := by
    have := one_lt_numFree hΛ
    linarith
  constructor
  · intro h
    exact spectralGapAtLeast_pinLocalWalk_pinned w hw Λ τ hZ hΛ h
  · intro h
    have hcon := spectralIndependence_of_spectralGapAtLeast_pinLocalWalk w hw Λ τ hZ hΛ h
    have harith : numFree Λ - (numFree Λ - η) / (numFree Λ - 1) * (numFree Λ - 1) = η := by
      field_simp
      ring
    rwa [harith] at hcon

/-! ### The unpinned case

At `Λ = ∅` the restriction `freeRestrict ∅` is the identity, so the zero-row
argument is not needed and the converse holds for an *arbitrary* nonnegative
weight, not only for a pinned one. -/

/-- **The converse at the empty pinning, for an arbitrary weight.**

A Poincaré constant `γ` for the unpinned local walk makes `gibbs w` spectrally
independent with constant `n − γ(n−1)`.  Unlike the pinned statement this needs
no hypothesis on `w` at all: `freeRestrict ∅` is the identity, so the restricted
ordering *is* the ordering. -/
theorem spectralIndependence_of_spectralGapAtLeast_pinLocalWalk_empty (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (hn : 1 < Fintype.card V) {γ : ℝ}
    (hgap : SpectralGapAtLeast
      (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt (by simpa using hn)))
      (pinLocalWalk w ∅ hw (by simpa using hn)) γ) :
    SpectralIndependence (gibbs w hw hZ)
      ((Fintype.card V : ℝ) - γ * ((Fintype.card V : ℝ) - 1)) := by
  have hid : freeRestrict (∅ : Finset V) = fun f : V × S → ℝ => f := by
    funext f p
    rw [freeRestrict_apply, if_neg (Finset.notMem_empty p.1)]
  refine (spectralIndependence_iff _).mpr fun a => ?_
  have h := quadForm_Cov_freeRestrict_le_marg_of_spectralGapAtLeast w ∅ hw hZ
    (by simpa using hn) hgap a
  rw [hid, numFree_empty] at h
  exact h

/-- **The equivalence at the empty pinning**, for an arbitrary weight: `gibbs w`
is `η`-spectrally independent iff the unpinned local walk has Poincaré constant
`(n − η)/(n − 1)`. -/
theorem spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk_empty (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (hn : 1 < Fintype.card V) (η : ℝ) :
    SpectralIndependence (gibbs w hw hZ) η
      ↔ SpectralGapAtLeast
          (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt (by simpa using hn)))
          (pinLocalWalk w ∅ hw (by simpa using hn))
          (((Fintype.card V : ℝ) - η) / ((Fintype.card V : ℝ) - 1)) := by
  have hN1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
    linarith
  constructor
  · intro h
    exact spectralGapAtLeast_pinLocalWalk_empty w hw hZ hn h
  · intro h
    have hcon := spectralIndependence_of_spectralGapAtLeast_pinLocalWalk_empty w hw hZ hn h
    have harith : (Fintype.card V : ℝ)
        - ((Fintype.card V : ℝ) - η) / ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 1)
        = η := by
      field_simp
      ring
    rwa [harith] at hcon

end Converse

end Arlib.MarkovChains
