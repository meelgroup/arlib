/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Optimal relaxation time implies spectral independence

This module proves `lem:opt-relax-SI` of the source monograph — Zongchen Chen,
Daniel Štefankovič, Eric Vigoda, *Spectral Independence and Local-to-Global
Techniques for Optimal Mixing of Markov Chains*, arXiv:2307.13826 (2023), cited
below as [CSV23] — which attributes the lemma to Anari–Jain–Koehler–Pham–Vuong
(which of their papers is meant is not recorded anywhere in this library):
**a Glauber dynamics that mixes optimally is spectrally independent.**  It is the converse of the development's
central implication, `Chains.SpectralIndependenceMixing`, and it closes the loop:
spectral independence is not merely *sufficient* for an `O(n)` relaxation time,
it is *necessary*.

`Techniques.SpectralIndependenceConverse` proves the analogous converse for the
**local walk** `Q_τ`, by reading the exact identity `dirichlet_pinLocalWalk`
backwards, and records that this does not give `lem:opt-relax-SI`, because the
chain there is the Glauber dynamics and the passage from a Glauber gap to a
local-walk gap would be a converse Random Walk Theorem.  That is right, and the
route taken here avoids the local walk entirely.  It is shorter than the forward
direction and uses only two facts already in the library:

* `Techniques.SpectralIndependence.quadForm_Cov` — the covariance form evaluated
  at `a` **is** the variance of the linear statistic `spinComb a`,
  `σ ↦ ∑_v a (v, σ v)`; and
* `Chains.GlauberTensorization.dirichlet_glauber` — the Dirichlet form of the
  Glauber dynamics **is** `(1/n) ∑_v μ[Var_v(f)]`.

So one tests the Glauber Poincaré inequality at the *linear statistics* only.
The left-hand side is then the covariance form on the nose, and the right-hand
side needs the one new inequality of this module:

  `μ[Var_v(spinComb a)] ≤ ∑_s marg μ (v,s) · a (v,s)²`.

**This step is exact where it looks lossy.**  Resampling the spin at `v` changes
exactly one summand of `∑_u a (u, σ u)`, and the other `n − 1` summands *cancel*
rather than merely being bounded: `siteVar` is a Dirichlet form, and a Dirichlet
form only ever sees the increments `f σ − f τ` along transitions, which for the
single-site update at `v` are `a (v, σ v) − a (v, τ v)`.  That is
`siteVar_congr_of_agreeOff`, and it is an equality.  The only inequality is the
last one, "a conditional variance is at most a conditional second moment", which
here is `⟪g, P_v g⟫ ≥ 0` — positive semidefiniteness of the heat-bath update,
itself free (`Glauber.siteChain_nonnegDefinite`).  So the constant is not merely
of the right order; it is the monograph's, exactly:

  **relaxation time `≤ C·n`  ⟹  `λ_max(Ψ_μ) ≤ C`**,

which in this development's normalisation (our `η` is the monograph's `1 + η`;
see `Techniques.SpectralIndependence`) is `SpectralIndependence μ C`, i.e. the
monograph's `(C−1)`-spectral independence.

**What "exactly" does and does not mean.**  The *constant of the statement* is
carried across with no degradation: no factor of two, no `C + 1`, no `n`.  The
*deduction* is not lossless pointwise, and it should not be expected to be — a
measure can be more spectrally independent than its relaxation time reveals.  The
entire slack is the discarded term `⟪P_v g, P_v g⟫` of `siteVar_le_ip_self`, the
mean square of the conditional mean of `s ↦ a (v,s)`, and it vanishes exactly
when that conditional mean does.  For the two-site model
`μ(00) = μ(11) = (1+δ)/4`, `μ(01) = μ(10) = (1−δ)/4` the true gap is `(1−δ)/2`
and the true constant is `1 + δ`, while this theorem returns `1/(1−δ)`; the two
agree to first order and coincide at `δ = 0`, the product case, where the
theorem is tight.

## The pinned statement, and the factor `n − |S|`

The monograph quantifies over pinnings, and asks that the Glauber dynamics *for
`μ_τ`* have relaxation time `≤ C·(n − |S|)`.  `Chains.PinnedGlauber` warns
(`siteChainPin_of_mem`, and `docs/dev/MarkovChains-ROADMAP.md` §3.6) that `glauber (pinWeight w Λ τ)`
is **not** that chain: it averages over all `|V|` sites and the `|Λ|` pinned ones
are no-ops, so it is the conditional Glauber dynamics *with holding probability*
`|Λ|/|V|`.  Getting this right is the whole content of the pinned statement, so
the chain the monograph means is built here, as `freeGlauber`: the mixture of
single-site updates with the uniform weights on the *free* sites.  Then

  `ℰ_{P_GD}(f) ≥ ((n−|Λ|)/n) · ℰ_{freeGlauber}(f)`,

with no hypothesis beyond `siteVar ≥ 0` — the pinned sites need not be shown to
be no-ops, only to contribute nonnegatively — and the two factors of `n − |Λ|`
cancel exactly:

  `((n−|Λ|)/n) · 1/(C·(n−|Λ|)) = 1/(C·n)`.

That is why the monograph's `n − |S|` is the right normalisation and no other
would do.

## Main declarations

* `agreeOff_of_siteUpdate_ne_zero`, **`siteVar_congr_of_agreeOff`** — a Dirichlet
  form sees only increments along transitions, so two functions with equal
  single-site increments have equal mean conditional variance.  This is the
  cancellation of the other `n − 1` sites, as an identity.
* `siteVar_le_ip_self`, `spinComb_sub_of_agreeOff`, **`siteVar_spinComb_le`** and
  `sum_siteVar_spinComb_le` — **the core inequality**, for an arbitrary
  nonnegative weight.
* **`spectralIndependence_of_approxTensorization`** — `C`-approximate
  tensorization of variance implies `C`-spectral independence, with *the same
  constant*.  This is the honest core: the Glauber dynamics enters only through
  `GlauberTensorization`'s equivalence.
* **`spectralIndependence_of_spectralGapAtLeast_glauber`** and
  **`spectralIndependence_of_relaxationTime_glauber`** — the unpinned
  `lem:opt-relax-SI`: gap `γ` gives `SpectralIndependence μ (1/(γn))`, so
  relaxation time `≤ Cn` gives `λ_max(Ψ_μ) ≤ C`.
* `freeSiteWeight`, **`freeGlauber`**, `dirichlet_freeGlauber`,
  `dirichlet_freeGlauber_empty`, **`dirichlet_freeGlauber_le`**,
  `spectralGapAtLeast_glauber_of_freeGlauber` — the conditional Glauber dynamics
  on the free sites, and the factor `(n−|Λ|)/n` relating it to the all-sites
  chain.
* **`spectralIndependence_of_relaxationTime_freeGlauber`**,
  `spectralIndependence_gibbsPin_of_card_le` and
  **`spectralIndependence_pinned_of_relaxationTime_freeGlauber`** —
  `lem:opt-relax-SI` at one pinning and then at every pinning.
* **`spectralGapAtLeast_pinLocalWalk_of_relaxationTime_freeGlauber`** — a
  *converse Random Walk Theorem*, which `Techniques.SpectralIndependenceConverse`
  reports as unavailable: composing this module with
  `Techniques.LocalSpectralIndependence` takes a Glauber gap at a pinning to a
  local-walk gap at that pinning.
* **`spectralGapAtLeast_glauber_of_relaxationTime_freeGlauber`** and
  **`spectralGapAtLeast_glauber_of_optimalRelaxationTime`** — the round trip,
  Glauber gap ⟹ spectral independence ⟹ Glauber gap, and the fact that it is
  **lossless exactly at `C = 1`**; the first docstring says what it costs
  otherwise.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.GlauberTensorization
import Arlib.MarkovChains.Chains.SpectralIndependenceMixing
import Arlib.MarkovChains.Techniques.SpectralIndependenceConverse

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## A Dirichlet form sees only single-site increments

The mean conditional variance `siteVar` is a Dirichlet form, and
`dirichlet_self_eq_pair` writes it as `½ ∑_{σ,τ} μ(σ) P_v(σ,τ) (f σ − f τ)²`.
The single-site update charges no pair that disagrees away from `v`, so only the
increments of `f` across a change of the spin at `v` matter.  For a linear
statistic those increments involve one summand, and the remaining `n − 1`
summands cancel identically. -/

section Increments

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The single-site update charges only configurations agreeing off `v`.**
Both branches of `siteUpdate` are supported on `AgreeOff v σ ·`: the degenerate
branch is the identity row, and the main branch carries the guard explicitly. -/
theorem agreeOff_of_siteUpdate_ne_zero {w : (V → S) → ℝ} {v : V} {σ τ : V → S}
    (h : siteUpdate w v σ τ ≠ 0) : AgreeOff v σ τ := by
  by_cases hz : Zloc w σ v = 0
  · rw [siteUpdate_of_Zloc_eq_zero hz] at h
    by_cases hts : τ = σ
    · rw [hts]; exact agreeOff_rfl v σ
    · rw [if_neg hts] at h; exact absurd rfl h
  · rw [siteUpdate_of_Zloc_ne_zero hz] at h
    by_cases hA : AgreeOff v σ τ
    · exact hA
    · rw [if_neg hA] at h; exact absurd rfl h

/-- **Equal single-site increments give equal mean conditional variance.**

If `f σ − f τ = g σ − g τ` whenever `σ` and `τ` agree away from `v`, then
`μ[Var_v(f)] = μ[Var_v(g)]`.  This is an *identity*, not an estimate, and it is
the step that makes the core inequality below tight: a Dirichlet form is a sum
over transitions of squared increments, and the single-site update at `v` makes
no transition that changes any other site
(`agreeOff_of_siteUpdate_ne_zero`). -/
theorem siteVar_congr_of_agreeOff (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) {f g : (V → S) → ℝ}
    (h : ∀ σ τ : V → S, AgreeOff v σ τ → f σ - f τ = g σ - g τ) :
    siteVar w hw hZ v f = siteVar w hw hZ v g := by
  have key : ∀ σ τ : V → S,
      gibbs w hw hZ σ * siteChain w hw v σ τ * (f σ - f τ) ^ 2
        = gibbs w hw hZ σ * siteChain w hw v σ τ * (g σ - g τ) ^ 2 := by
    intro σ τ
    by_cases hP : siteChain w hw v σ τ = 0
    · rw [hP]; ring
    · have hP' : siteUpdate w v σ τ ≠ 0 := by rwa [siteChain_apply] at hP
      rw [h σ τ (agreeOff_of_siteUpdate_ne_zero hP')]
  rw [siteVar_eq_pair, siteVar_eq_pair,
    Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => key σ τ]

/-- **A conditional variance is at most a second moment.**

`μ[Var_v(f)] ≤ ⟪f, f⟫_μ`, because `μ[Var_v(f)] = ⟪f,f⟫_μ − ⟪f, P_v f⟫_μ` and the
heat-bath update is positive semidefinite (`siteChain_nonnegDefinite`, itself a
consequence of self-adjoint idempotence — no eigenvalue).  This is the only
inequality in the core estimate below. -/
theorem siteVar_le_ip_self (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteVar w hw hZ v f ≤ ip (gibbs w hw hZ) f f := by
  have h := siteChain_nonnegDefinite w hw hZ v f
  rw [siteVar_apply, dirichlet_apply]
  linarith

end Increments

/-! ## The core inequality

Testing the Glauber Poincaré inequality at a linear statistic `spinComb a` needs
an upper bound on `μ[Var_v(spinComb a)]` in terms of the marginals, and the
bound is the second moment of the single site `v` alone. -/

section CombIncrement

variable {V : Type*} [Fintype V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **A single-site move changes one summand of a linear statistic.**

If `σ` and `τ` agree away from `v` then
`spinComb a σ − spinComb a τ = a (v, σ v) − a (v, τ v)`: the other `n − 1`
summands of `∑_u a (u, σ u)` cancel termwise.  This is the cancellation that has
to be an equality rather than a bound for the core inequality below to carry the
monograph's constant. -/
theorem spinComb_sub_of_agreeOff (a : V × S → ℝ) {v : V} {σ τ : V → S}
    (h : AgreeOff v σ τ) :
    spinComb a σ - spinComb a τ = a (v, σ v) - a (v, τ v) := by
  rw [spinComb_eq, spinComb_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_single v ?_ ?_
  · intro u _ hu
    rw [h u hu, sub_self]
  · intro hc
    exact absurd (mem_univ v) hc

end CombIncrement

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The core inequality.**

`μ[Var_v(spinComb a)] ≤ ∑_s μ(σ v = s) · a (v,s)²`.

Two steps, one exact and one an inequality.  `siteVar_congr_of_agreeOff` with
`spinComb_sub_of_agreeOff` replaces `spinComb a` by the single-site function
`σ ↦ a (v, σ v)` — *exactly*, because the mean conditional variance at `v` only
sees increments across a change at `v`.  Then `siteVar_le_ip_self` drops the
conditional mean, and `sum_mu_coord` reads the resulting second moment off the
marginals at `v`.

Stated for an arbitrary nonnegative weight `w` with positive partition function;
no pinning, no spectral independence and no Glauber dynamics appears. -/
theorem siteVar_spinComb_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (a : V × S → ℝ) :
    siteVar w hw hZ v (spinComb a)
      ≤ ∑ s, marg (gibbs w hw hZ) (v, s) * a (v, s) ^ 2 := by
  have hcongr : siteVar w hw hZ v (spinComb a) = siteVar w hw hZ v (fun σ => a (v, σ v)) :=
    siteVar_congr_of_agreeOff w hw hZ v fun _ _ hA => spinComb_sub_of_agreeOff a hA
  have hip : ip (gibbs w hw hZ) (fun σ => a (v, σ v)) (fun σ => a (v, σ v))
      = ∑ s, marg (gibbs w hw hZ) (v, s) * a (v, s) ^ 2 := by
    rw [ip_apply,
      Finset.sum_congr rfl fun σ (_ : σ ∈ (univ : Finset (V → S))) =>
        (by ring : gibbs w hw hZ σ * a (v, σ v) * a (v, σ v)
          = gibbs w hw hZ σ * a (v, σ v) ^ 2)]
    exact sum_mu_coord (gibbs w hw hZ) v fun s => a (v, s) ^ 2
  rw [hcongr, ← hip]
  exact siteVar_le_ip_self w hw hZ v _

/-- **The core inequality, summed over the sites.**

`∑_v μ[Var_v(spinComb a)] ≤ ∑_p marg μ p · a p²`, the right-hand side being
exactly the quadratic form `quadForm (diag (marg μ)) a` that spectral
independence compares the covariance form against. -/
theorem sum_siteVar_spinComb_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (a : V × S → ℝ) :
    ∑ v, siteVar w hw hZ v (spinComb a)
      ≤ ∑ p : V × S, marg (gibbs w hw hZ) p * a p ^ 2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun v _ => siteVar_spinComb_le w hw hZ v a

end Core

/-! ## From a Poincaré inequality to spectral independence

`quadForm_Cov` says the covariance form at `a` is `Var_μ(spinComb a)`, so any
upper bound on the variance of a *linear statistic* by the local quantities is a
spectral independence statement.  Approximate tensorization is such a bound, and
`GlauberTensorization` already knows it is the same thing as a Glauber gap. -/

section FromTensorization

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **Approximate tensorization implies spectral independence, with the same
constant.**

`Var_μ(f) ≤ C ∑_v μ[Var_v(f)]` for every `f` gives `Cov_μ ⪯ C · diag(marg_μ)`.
Only the linear statistics `f = spinComb a` are used, which is why the constant
survives unchanged: `quadForm_Cov` turns the left-hand side into the covariance
form and `sum_siteVar_spinComb_le` turns the right-hand side into the diagonal
form.

This is the mathematical core of `lem:opt-relax-SI`; the Glauber dynamics enters
only through `approxTensorization_of_spectralGapAtLeast_glauber`. -/
theorem spectralIndependence_of_approxTensorization (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) {C : ℝ} (hC : 0 ≤ C) (hAT : ApproxTensorization w hw hZ C) :
    SpectralIndependence (gibbs w hw hZ) C := by
  refine (spectralIndependence_iff C).mpr fun a => ?_
  rw [quadForm_Cov]
  calc Var (gibbs w hw hZ) (spinComb a)
      ≤ C * ∑ v, siteVar w hw hZ v (spinComb a) := hAT _
    _ ≤ C * ∑ p : V × S, marg (gibbs w hw hZ) p * a p ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_siteVar_spinComb_le w hw hZ a) hC

section GlauberGap

variable [Nonempty V]

/-- **A Glauber Poincaré inequality implies spectral independence.**

A Poincaré constant `γ > 0` for the Glauber dynamics gives
`SpectralIndependence μ (1/(γ·n))`.  Note the reciprocal: the *smaller* the gap,
the *larger* the spectral independence constant, as it must be. -/
theorem spectralIndependence_of_spectralGapAtLeast_glauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {γ : ℝ} (hγ : 0 < γ)
    (hgap : SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) γ) :
    SpectralIndependence (gibbs w hw hZ) (1 / (γ * (Fintype.card V : ℝ))) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact spectralIndependence_of_approxTensorization w hw hZ
    (le_of_lt (div_pos one_pos (mul_pos hγ hn)))
    (approxTensorization_of_spectralGapAtLeast_glauber hγ hgap)

/-- **`lem:opt-relax-SI`, unpinned** ([CSV23, `lem:opt-relax-SI`], first sentence).

*If the Glauber dynamics for `μ` has relaxation time at most `C·n`, then
`λ_max(Ψ_μ) ≤ C`.*

Relaxation time `≤ Cn` is the Poincaré inequality with constant `1/(Cn)`, and the
conclusion `λ_max(Ψ_μ) ≤ C` is `SpectralIndependence μ C` (see
`Techniques.SpectralIndependence` for the dictionary `Cov = D·Ψ`).  The constant
is the monograph's exactly, with no degradation across the implication; the
implication itself is an inequality, and the module docstring measures its slack
against a two-site model.

Two things this does *not* need, which the monograph's statement has: the spin
set is an arbitrary finite type, not `{0,1}`, and no ergodicity, positivity or
marginal-boundedness hypothesis appears. -/
theorem spectralIndependence_of_relaxationTime_glauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) {C : ℝ} (hC : 0 < C)
    (hgap : SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (1 / (C * (Fintype.card V : ℝ)))) :
    SpectralIndependence (gibbs w hw hZ) C := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h := spectralIndependence_of_spectralGapAtLeast_glauber w hw hZ
    (div_pos one_pos (mul_pos hC hn)) hgap
  have harith : 1 / (1 / (C * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ)) = C := by
    field_simp
  rwa [harith] at h

end GlauberGap

end FromTensorization

/-! ## The Glauber dynamics of a conditional system

`glauber (pinWeight w Λ τ)` is *not* the chain the monograph calls "the Glauber
dynamics for `μ_τ`": it picks uniformly among all `|V|` sites, and the `|Λ|`
pinned ones do nothing (`PinnedGlauber.siteChainPin_of_mem`), so it is the
intended chain slowed down by the factor `(n − |Λ|)/n`.  The intended chain is
built here directly, as the mixture of single-site updates with the uniform
weights on the free sites. -/

section FreeSiteWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The uniform probability weights on the **free** sites of a pinning: `0` at a
pinned site and `1/(n − |Λ|)` elsewhere. -/
noncomputable def freeSiteWeight (Λ : Finset V) : V → ℝ :=
  fun v => if v ∈ Λ then 0 else 1 / numFree Λ

theorem freeSiteWeight_apply (Λ : Finset V) (v : V) :
    freeSiteWeight Λ v = if v ∈ Λ then 0 else 1 / numFree Λ := rfl

theorem freeSiteWeight_nonneg (Λ : Finset V) (v : V) : 0 ≤ freeSiteWeight Λ v := by
  rw [freeSiteWeight_apply]
  split
  · exact le_rfl
  · refine div_nonneg zero_le_one ?_
    simp only [numFree]
    exact Nat.cast_nonneg _

/-- The free-site weights are a probability distribution on sites, as soon as
some site is free. -/
theorem sum_freeSiteWeight {Λ : Finset V} (hΛ : Λ.card < Fintype.card V) :
    ∑ v, freeSiteWeight Λ v = 1 := by
  have hN : numFree Λ ≠ 0 := (numFree_pos hΛ).ne'
  have hcard : (((univ : Finset V) \ Λ).card : ℝ) = numFree Λ := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Λ), Finset.card_univ]
    rfl
  have h1 : ∀ v : V,
      freeSiteWeight Λ v = if v ∈ (univ : Finset V) \ Λ then 1 / numFree Λ else 0 := by
    intro v
    rw [freeSiteWeight_apply]
    by_cases hv : v ∈ Λ <;> simp [hv]
  rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, hcard, mul_one_div, div_self hN]

end FreeSiteWeight

section FreeGlauber

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The Glauber dynamics of the conditional system.**

Pick a site uniformly at random *among the free ones* and perform the heat-bath
update there.  Applied to a pinned weight `pinWeight w Λ τ` this is the chain the
monograph means by "the Glauber dynamics for `μ_τ`", a chain that moves at
`n − |Λ|` sites, in contrast with `PinnedGlauber.glauberPin`, which averages over
all `n` sites and holds still at the `|Λ|` pinned ones.

The hypothesis `hΛ` is genuinely part of the data: with every site pinned there
is no probability distribution on free sites to average against. -/
noncomputable def freeGlauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V)
    (hΛ : Λ.card < Fintype.card V) : FinChain (V → S) :=
  FinKernel.mixWeights (freeSiteWeight Λ) (freeSiteWeight_nonneg Λ) (sum_freeSiteWeight hΛ)
    (siteChain w hw)

/-- The Gibbs measure is reversible for the free-site chain — inherited from
`siteChain_reversible` through `mixWeights`. -/
theorem freeGlauber_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (hΛ : Λ.card < Fintype.card V) :
    Reversible (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) :=
  mixWeights_reversible _ _ fun v => siteChain_reversible w hw hZ v

/-- The free-site chain is positive semidefinite, again inherited. -/
theorem freeGlauber_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (hΛ : Λ.card < Fintype.card V) :
    NonnegDefinite (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) :=
  mixWeights_nonnegDefinite _ _ fun v => siteChain_nonnegDefinite w hw hZ v

/-- **The Dirichlet form of the free-site chain**:
`ℰ_{freeGlauber}(f) = (1/(n−|Λ|)) ∑_{v ∉ Λ} μ[Var_v(f)]`, written as a sum over
all sites against the free-site weights. -/
theorem dirichlet_freeGlauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (hΛ : Λ.card < Fintype.card V) (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) f f
      = ∑ v, freeSiteWeight Λ v * siteVar w hw hZ v f := by
  rw [freeGlauber, dirichlet_mixWeights]
  exact Finset.sum_congr rfl fun v _ => by rw [siteVar_apply]

section NonemptyV

variable [Nonempty V]

/-- **The audit at the empty pinning**: with nothing pinned, the free-site chain
has the same Dirichlet form as the Glauber dynamics, so the two have the same
Poincaré constants.  (They are not the same term: one is a `mixWeights`, the
other an `avg`.) -/
theorem dirichlet_freeGlauber_empty (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (freeGlauber w hw ∅ (by simpa using Fintype.card_pos)) f f
      = dirichlet (gibbs w hw hZ) (glauber w hw) f f := by
  rw [dirichlet_freeGlauber, dirichlet_glauber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [freeSiteWeight_apply, if_neg (Finset.notMem_empty v), numFree_empty]

/-- **The all-sites chain dominates `(n−|Λ|)/n` times the free-site chain.**

`((n−|Λ|)/n) · ℰ_{freeGlauber}(f) ≤ ℰ_{P_GD}(f)`.

This is the factor recorded in `docs/dev/MarkovChains-ROADMAP.md` §3.6, and the proof needs *less* than
that discussion: the pinned sites are not shown to be no-ops, only to contribute
a nonnegative amount to `∑_v μ[Var_v(f)]`.  For a pinned weight they contribute
exactly `0` (`PinnedGlauber.siteChainPin_of_mem`), so the inequality is then an
equality — but nothing below needs that, and it is not proved here. -/
theorem dirichlet_freeGlauber_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (hΛ : Λ.card < Fintype.card V) (f : (V → S) → ℝ) :
    numFree Λ / (Fintype.card V : ℝ) * dirichlet (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) f f
      ≤ dirichlet (gibbs w hw hZ) (glauber w hw) f f := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hN : (0 : ℝ) < numFree Λ := numFree_pos hΛ
  have hstep : numFree Λ * ∑ v, freeSiteWeight Λ v * siteVar w hw hZ v f
      ≤ ∑ v, siteVar w hw hZ v f := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ Λ
    · rw [freeSiteWeight_apply, if_pos hv, zero_mul, mul_zero]
      exact siteVar_nonneg w hw hZ v f
    · rw [freeSiteWeight_apply, if_neg hv]
      refine le_of_eq ?_
      field_simp
  rw [dirichlet_glauber, dirichlet_freeGlauber]
  calc numFree Λ / (Fintype.card V : ℝ) * ∑ v, freeSiteWeight Λ v * siteVar w hw hZ v f
      = 1 / (Fintype.card V : ℝ)
          * (numFree Λ * ∑ v, freeSiteWeight Λ v * siteVar w hw hZ v f) := by ring
    _ ≤ 1 / (Fintype.card V : ℝ) * ∑ v, siteVar w hw hZ v f :=
        mul_le_mul_of_nonneg_left hstep (by positivity)

/-- **A free-site Poincaré inequality gives an all-sites one, scaled by
`(n−|Λ|)/n`.**  The slowdown of the pinned Glauber dynamics, as a gap
statement. -/
theorem spectralGapAtLeast_glauber_of_freeGlauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (Λ : Finset V) (hΛ : Λ.card < Fintype.card V)
    {g : ℝ} (hgap : SpectralGapAtLeast (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) g) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (numFree Λ / (Fintype.card V : ℝ) * g) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hfac : (0 : ℝ) ≤ numFree Λ / (Fintype.card V : ℝ) :=
    div_nonneg (numFree_pos hΛ).le hn.le
  intro f
  calc numFree Λ / (Fintype.card V : ℝ) * g * Var (gibbs w hw hZ) f
      = numFree Λ / (Fintype.card V : ℝ) * (g * Var (gibbs w hw hZ) f) := by ring
    _ ≤ numFree Λ / (Fintype.card V : ℝ)
          * dirichlet (gibbs w hw hZ) (freeGlauber w hw Λ hΛ) f f :=
        mul_le_mul_of_nonneg_left (hgap f) hfac
    _ ≤ dirichlet (gibbs w hw hZ) (glauber w hw) f f :=
        dirichlet_freeGlauber_le w hw hZ Λ hΛ f

end NonemptyV

end FreeGlauber

/-! ## `lem:opt-relax-SI` at a pinning

Conditioning does not leave the category (`Chains.Pinning`), so the unpinned
theorem applies verbatim to `pinWeight w Λ τ`; the only work is the bookkeeping
of the two factors `n − |Λ|`, which cancel. -/

section FullyPinned

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **A fully pinned measure is spectrally independent with any nonnegative
constant.**

When every site is pinned the conditional measure is a point mass, so its
covariance form vanishes identically (`Cov_eq_zero_of_marg_eq_one`, through
`quadForm_Cov_freeRestrict_eq` with `Λ = univ`).  This is the degenerate case the
free-site chain cannot cover — there is no free site to update — and it is what
lets the pinned statement below quantify over *all* pinnings, as the monograph's
`defn:SI` and `Chains.SpectralIndependenceMixing` both do. -/
theorem spectralIndependence_gibbsPin_of_card_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ)) {C : ℝ} (hC : 0 ≤ C)
    (hΛ : Fintype.card V ≤ Λ.card) :
    SpectralIndependence (gibbsPin w hw Λ τ hZ) C := by
  have h1 : Λ.card ≤ Fintype.card V := by
    simpa [Finset.card_univ] using Finset.card_le_univ Λ
  have huniv : Λ = univ := Finset.eq_univ_of_card Λ (le_antisymm h1 hΛ)
  refine (spectralIndependence_iff C).mpr fun a => ?_
  have hzero : quadForm (Cov (gibbsPin w hw Λ τ hZ)) a = 0 := by
    rw [← quadForm_Cov_freeRestrict_eq Λ (exists_marg_gibbsPin_eq_one w hw Λ τ hZ) a]
    have hfr : freeRestrict Λ a = fun _ : V × S => (0 : ℝ) := by
      funext p
      exact freeRestrict_of_mem (by rw [huniv]; exact mem_univ p.1) a
    rw [hfr]
    simp [quadForm]
  rw [hzero]
  exact mul_nonneg hC
    (Finset.sum_nonneg fun p _ => mul_nonneg (marg_nonneg p) (sq_nonneg _))

end FullyPinned

section Pinned

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **`lem:opt-relax-SI` at one pinning** ([CSV23, `lem:opt-relax-SI`], second
sentence).

*If the Glauber dynamics for `μ_τ` has relaxation time at most `C·(n − |Λ|)`,
then `μ_τ` is `C`-spectrally independent* — the monograph's `(C−1)`-spectral
independence, in its normalisation.

The arithmetic that makes the statement work is

  `((n−|Λ|)/n) · 1/(C·(n−|Λ|)) = 1/(C·n)`:

the free-site gap `1/(C·(n−|Λ|))` becomes an all-sites gap of `1/(C·n)` after the
slowdown of `dirichlet_freeGlauber_le`, and `1/(C·n)` is exactly what the
unpinned theorem consumes.  The factor `n − |Λ|` in the monograph's hypothesis is
therefore not a convenience: it is the unique normalisation for which the pinned
statement has the same constant as the unpinned one. -/
theorem spectralIndependence_of_relaxationTime_freeGlauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ))
    (hΛ : Λ.card < Fintype.card V) {C : ℝ} (hC : 0 < C)
    (hgap : SpectralGapAtLeast (gibbsPin w hw Λ τ hZ)
      (freeGlauber (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) Λ hΛ)
      (1 / (C * numFree Λ))) :
    SpectralIndependence (gibbsPin w hw Λ τ hZ) C := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hN : (0 : ℝ) < numFree Λ := numFree_pos hΛ
  have hgibbs : gibbsPin w hw Λ τ hZ
      = gibbs (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) hZ := rfl
  rw [hgibbs] at hgap ⊢
  have h := spectralGapAtLeast_glauber_of_freeGlauber (pinWeight w Λ τ)
    (pinWeight_nonneg hw Λ τ) hZ Λ hΛ hgap
  have harith : numFree Λ / (Fintype.card V : ℝ) * (1 / (C * numFree Λ))
      = 1 / (C * (Fintype.card V : ℝ)) := by
    field_simp
  rw [harith] at h
  exact spectralIndependence_of_relaxationTime_glauber _ _ hZ hC h

/-- **`lem:opt-relax-SI`, in full.**

*If for every pinning `τ` on a subset `Λ` the Glauber dynamics for `μ_τ` has
relaxation time at most `C·(n − |Λ|)`, then every `μ_τ` is `C`-spectrally
independent* — the monograph's "`μ` is `(C−1)`-spectrally independent", since
`defn:SI` quantifies over pinnings.

The conclusion is stated at *every* pinning, including the degenerate ones with
no free site, which is exactly the shape
`Chains.SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence`
consumes.  The hypothesis is only required where it can be stated, at pinnings
that leave a free site. -/
theorem spectralIndependence_pinned_of_relaxationTime_freeGlauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) {C : ℝ} (hC : 0 < C)
    (hgap : ∀ (Λ : Finset V) (τ : V → S) (hZΛ : 0 < Z (pinWeight w Λ τ))
      (hΛ : Λ.card < Fintype.card V),
      SpectralGapAtLeast (gibbsPin w hw Λ τ hZΛ)
        (freeGlauber (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) Λ hΛ)
        (1 / (C * numFree Λ)))
    (Λ : Finset V) (τ : V → S) (hZΛ : 0 < Z (pinWeight w Λ τ)) :
    SpectralIndependence (gibbsPin w hw Λ τ hZΛ) C := by
  by_cases hΛ : Λ.card < Fintype.card V
  · exact spectralIndependence_of_relaxationTime_freeGlauber w hw Λ τ hZΛ hΛ hC
      (hgap Λ τ hZΛ hΛ)
  · exact spectralIndependence_gibbsPin_of_card_le w hw Λ τ hZΛ hC.le (by omega)

/-- **A converse Random Walk Theorem, at one pinning.**

`Techniques.SpectralIndependenceConverse` records that the passage from a Glauber
gap to a local-walk gap "is a converse to the Random Walk Theorem and is not
available here".  It is available now, and needs nothing new: this module takes
the Glauber gap to spectral independence, and
`Techniques.LocalSpectralIndependence` takes spectral independence to a
local-walk gap.  Composing,

  `T_relax(Glauber for μ_τ) ≤ C·m`  ⟹  `γ(Q_τ) ≥ (m − C)/(m − 1)`,  `m = n − |Λ|`.

By `spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk` the second
implication is an *equivalence*, so the composite is exactly as good as the
first implication and no worse. -/
theorem spectralGapAtLeast_pinLocalWalk_of_relaxationTime_freeGlauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ))
    (hΛ : Λ.card + 1 < Fintype.card V) {C : ℝ} (hC : 0 < C)
    (hgap : SpectralGapAtLeast (gibbsPin w hw Λ τ hZ)
      (freeGlauber (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) Λ (Nat.lt_of_succ_lt hΛ))
      (1 / (C * numFree Λ))) :
    SpectralGapAtLeast
      (pinDist (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hΛ)
      ((numFree Λ - C) / (numFree Λ - 1)) :=
  (spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk w hw Λ τ hZ hΛ C).mp
    (spectralIndependence_of_relaxationTime_freeGlauber w hw Λ τ hZ
      (Nat.lt_of_succ_lt hΛ) hC hgap)

end Pinned

/-! ## The round trip

`Chains.SpectralIndependenceMixing` turns spectral independence at every pinning
back into a Glauber Poincaré inequality.  Composing it with the theorem above
gives a statement of the form "Glauber gap ⟹ Glauber gap", and the honest
question is what the composition costs. -/

section RoundTrip

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The round trip: Glauber gap ⟹ spectral independence ⟹ Glauber gap.**

Assume that at *every* pinning `τ` on `Λ` the conditional Glauber dynamics has
relaxation time at most `C·(n − |Λ|)`, with `1 ≤ C ≤ 3/2`.  Then the *unpinned*
Glauber dynamics satisfies the Poincaré inequality with constant

  `Γ_{n−1}/n`,  `Γ_{n−1} = ∏_{d=1}^{n−1} (d + 2 − 2C)/d`.

**What the round trip loses.**  We started from a relaxation time `≤ Cn` (the
`Λ = ∅` case of the hypothesis) and came back with `n/Γ_{n−1}`, so the loss is
the factor `1/Γ_{n−1}`, which is `1` at `C = 1` and grows polynomially in `n` as
`C` increases — not a constant factor.  Two further losses are in the
*hypotheses* rather than the constant: the return leg needs the gap at every
pinning where the outward leg needed it only at one, and it is restricted to
`C ≤ 3/2`.

**None of this loss is in this module.**  The outward leg carries its constant
unchanged, and
`Techniques.SpectralIndependence.one_sub_marg_le_of_spectralIndependence` shows
that constant cannot be pushed below `1`, so it contributes no factor to the
composite at all.  All of the degradation is in the return leg: the `C ≤ 3/2`
restriction and the `Γ` factor are artefacts of
`Techniques.ImprovedRandomWalk` weakening `1/(1 − γ/2)` to `2γ − 1`, as
`Chains.SpectralIndependenceMixing`'s module docstring analyses at length.  So
this composite is a *measurement of the return leg's loss*, and a demonstration
that the two directions of the theory are not yet inverse to each other. -/
theorem spectralGapAtLeast_glauber_of_relaxationTime_freeGlauber (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ} (hm : Fintype.card V = m + 1)
    {C : ℝ} (hC1 : 1 ≤ C) (hC : C ≤ 3 / 2)
    (hgap : ∀ (Λ : Finset V) (τ : V → S) (hZΛ : 0 < Z (pinWeight w Λ τ))
      (hΛ : Λ.card < Fintype.card V),
      SpectralGapAtLeast (gibbsPin w hw Λ τ hZΛ)
        (freeGlauber (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) Λ hΛ)
        (1 / (C * numFree Λ))) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (improvedFactor (siGamma (m + 1) C) m / (Fintype.card V : ℝ)) :=
  spectralGapAtLeast_glauber_of_spectralIndependence_div_card w hw hZ hm hC1 hC
    (spectralIndependence_pinned_of_relaxationTime_freeGlauber w hw
      (lt_of_lt_of_le zero_lt_one hC1) hgap)

/-- **The round trip is lossless exactly at `C = 1`.**

*If at every pinning the conditional Glauber dynamics has relaxation time at most
`n − |Λ|`, then the Glauber dynamics has relaxation time at most `n`.*

At `C = 1` every `Γ_i` of the theorem above equals `1`, the sum is `n`, and the
returned constant is exactly `1/n` — the same constant the hypothesis asserts at
the empty pinning.  So the composite is the identity here, which is the
calibration point for the whole loop: `C = 1` is the monograph's `0`-spectral
independence, the value a product measure attains
(`Chains.ProductSpectralIndependence`), and `1/n` is the true relaxation time of
the Glauber dynamics of a product measure.

For `C > 1` the loop is strictly lossy; see the previous docstring. -/
theorem spectralGapAtLeast_glauber_of_optimalRelaxationTime (w : (V → S) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ} (hm : Fintype.card V = m + 1)
    (hgap : ∀ (Λ : Finset V) (τ : V → S) (hZΛ : 0 < Z (pinWeight w Λ τ))
      (hΛ : Λ.card < Fintype.card V),
      SpectralGapAtLeast (gibbsPin w hw Λ τ hZΛ)
        (freeGlauber (pinWeight w Λ τ) (pinWeight_nonneg hw Λ τ) Λ hΛ)
        (1 / numFree Λ)) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) (1 / (Fintype.card V : ℝ)) := by
  refine spectralGapAtLeast_glauber_of_spectralIndependence_one w hw hZ hm ?_
  refine spectralIndependence_pinned_of_relaxationTime_freeGlauber w hw zero_lt_one ?_
  intro Λ τ hZΛ hΛ
  simpa using hgap Λ τ hZΛ hΛ

end RoundTrip

end Arlib.MarkovChains
