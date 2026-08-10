/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Pinned dynamics, marginals, and the local walk of a spin system

`Chains.Pinning` established that **conditioning does not leave the category**:
`pinWeight w Λ η` is again a nonnegative weight, so a conditional Gibbs measure
is a Gibbs measure.  This module cashes that observation in.  It does two
things.

First it *states* the instantiations.  Each is a one-liner, and that is exactly
the point: the pinned single-site update and the pinned Glauber dynamics are
reversible with respect to the conditional Gibbs measure and positive
semidefinite, with no new proof, and pinning twice is pinning once
(`gibbsPin_pinWeight_union`).  The local-to-global induction of §6 of the
monograph — Zongchen Chen, Daniel Štefankovič, Eric Vigoda, *Spectral
Independence and Local-to-Global Techniques for Optimal Mixing of Markov
Chains*, arXiv:2307.13826 (2023), cited below as [CSV23] — runs over *all*
pinnings simultaneously, so having these available uniformly in `Λ` and `η` is
what makes that induction expressible at all.

Second it builds the two objects the induction actually consumes, the
monograph's `π_{η,1}` and the local walk `Q_η` (both [CSV23]).  Both are
carried on (site, spin) pairs `V × S`, which
is the spin-system counterpart of the ground set of `Techniques.LocalWalk`, and
they are built here from *masses* rather than from conditional probabilities:
`siteMass w v s` is the total weight of the configurations with `σ v = s` and
`pairMass w u v a b` the total weight of those with `σ u = a` and `σ v = b`.
Writing `Q_η` with these numerators makes detailed balance a one-line symmetry
(`pairMass_comm`) instead of a computation with conditional probabilities, and
it keeps every degenerate branch (a pinned site, a null marginal) visibly zero.

Following the convention of the development, the definitions take a *general*
weight `w` together with the set `Λ` of already-pinned sites; the intended
instance is `w = pinWeight w₀ Λ η`, and the lemmas about pinned marginals are
stated in that form.  Nothing about the construction needs `w` to be pinned —
only the counting of free sites uses `Λ`.

* `gibbsPin`, `siteChainPin`, `glauberPin` — the conditional Gibbs measure and
  the two pinned chains, with **`glauberPin_reversible`**,
  `glauberPin_stationary`, **`glauberPin_nonnegDefinite`** and their
  `siteChainPin` counterparts, each inherited verbatim from `Chains.Glauber`.
* `Z_pinWeight_union`, **`gibbsPin_pinWeight_union`** — pinning twice is
  pinning once.
* `siteChainPin_of_mem` — a pinned site is a no-op, so `glauberPin` is the
  conditional Glauber dynamics *with holding probability* `|Λ|/|V|`.  Stated
  because anything that feeds a pinned gap into a local-to-global estimate has
  to know that factor is there.
* `siteMass`, `pairMass` — the one- and two-site masses, with `sum_siteMass`
  (`∑_s siteMass = Z`), `sum_pairMass`, **`pairMass_comm`** and
  `pairMass_le_siteMass`.
* `siteMarginal` — the single-site marginal of `gibbs w` as a `FinDist S`, with
  `siteMarginal_eq_Pr` (it really is the probability of `{σ | σ v = s}`) and the
  compatibility results **`siteMarginal_pinWeight_of_mem`** (the marginal at an
  already-pinned site is the point mass at `η v`) and
  `siteMarginal_pinWeight_insert` (pinning `v` to `s` and then looking at `v`
  gives the point mass at `s`).  `Z_pinWeight_insert` records the companion
  identity `siteMass (pinWeight w Λ η) v s = Z (pinWeight w (insert v Λ) …)`:
  the one-site marginal *is* the mass of the one-site-larger pinning.
* **`pinDist`** — the monograph's `π_{η,1}`: choose a free site uniformly, then
  a spin from its marginal.  Needs at least one free site, so
  `Λ.card < Fintype.card V` sits in the data, as `FinDist` demands.
* **`pinLocalWalk`** — the local walk `Q_η` on one-site extensions, mirroring
  `Techniques.LocalWalk.localWalk`, with `pinDist_mul_pinLocalWalk` (the
  detailed-balance cell), **`pinLocalWalk_reversible`**,
  `pinLocalWalk_stationary` and `pinLocalWalk_diag`.

* `pinGraph`, `mu_graphWeight_pinGraph`, `mu_graphWeight_insert_pinGraph`,
  `mu_graphWeight_insert_two_pinGraph` — the dictionary to the encoded
  simplicial complex of `Chains.LevelEncoding`, and hence
  **`pinDist_eq_linkDist`** and **`pinLocalWalk_eq_localWalk`**: the local walk
  built here on `V × S` and the one built in `Techniques.LocalWalk` on the
  ground set of the complex are the *same matrix*, entry by entry, degenerate
  rows included.  This is the consistency check between the two halves of the
  development, and it is what will let a bound proved for one be used for the
  other.

As in `Techniques.LocalWalk`, `Q_η` is *not* asserted to be positive
semidefinite: it is the non-backtracking walk and the assertion is false.
Positive semidefiniteness here belongs to `glauberPin` and `siteChainPin`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Chains.LevelEncoding
import Arlib.MarkovChains.Chains.Pinning
import Arlib.MarkovChains.Techniques.LocalWalk
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The pinned category is closed

Every object of `Chains.SpinSystem` and `Chains.Glauber` applied to
`pinWeight w Λ η` is an object of the conditional system.  The definitions here
are pure abbreviations; they exist so that downstream statements about "the
Glauber dynamics of the system conditioned on `η`" can be written without
repeating the `pinWeight_nonneg` plumbing. -/

section Closed

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The **conditional Gibbs measure** `μ_η`: the Gibbs measure of the pinned
weight.  By `Pinning.gibbsPin_eq_cond` this really is `μ` conditioned on the
pinned event. -/
noncomputable def gibbsPin (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) : FinDist (V → S) :=
  gibbs (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ

@[simp] theorem gibbsPin_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) (σ : V → S) :
    gibbsPin w hw Λ η hZ σ = pinWeight w Λ η σ / Z (pinWeight w Λ η) := rfl

/-- The **pinned single-site heat-bath chain** at the site `v`: the single-site
update of the conditional system. -/
noncomputable def siteChainPin (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (v : V) : FinChain (V → S) :=
  siteChain (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) v

theorem siteChainPin_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (v : V) (σ τ : V → S) :
    siteChainPin w hw Λ η v σ τ = siteUpdate (pinWeight w Λ η) v σ τ := rfl

/-- The pinned single-site update is reversible with respect to the conditional
Gibbs measure.  This is `Glauber.siteChain_reversible` at the pinned weight; no
theory about conditional measures is involved. -/
theorem siteChainPin_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) (v : V) :
    Reversible (gibbsPin w hw Λ η hZ) (siteChainPin w hw Λ η v) :=
  siteChain_reversible (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ v

/-- The conditional Gibbs measure is stationary for the pinned single-site
update. -/
theorem siteChainPin_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) (v : V) :
    Stationary (gibbsPin w hw Λ η hZ) (siteChainPin w hw Λ η v) :=
  (siteChainPin_reversible w hw Λ η hZ v).stationary

/-- The pinned single-site update is positive semidefinite — still a
self-adjoint idempotent, still no eigenvalue. -/
theorem siteChainPin_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V)
    (η : V → S) (hZ : 0 < Z (pinWeight w Λ η)) (v : V) :
    NonnegDefinite (gibbsPin w hw Λ η hZ) (siteChainPin w hw Λ η v) :=
  siteChain_nonnegDefinite (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ v

/-- **A pinned site is a no-op.**  On the support of the conditional measure the
single-site update at an *already pinned* site `v` is the identity row: the
conditional law of `σ v` given the rest is the point mass at `η v`, which is
where `σ` already is.

This is worth recording explicitly, because it means `glauberPin` is the Glauber
dynamics of the conditional system *with holding*: it picks uniformly among all
`|V|` sites, and the `|Λ|` pinned ones do nothing.  A chain that picks uniformly
among the `|V| - |Λ|` free sites is `glauberPin` sped up by the factor
`|V| / (|V| - |Λ|)`, and its Dirichlet form — hence its Poincaré constant —
differs by exactly that factor.  Anything that feeds a pinned Glauber gap into a
local-to-global estimate has to say which of the two it means. -/
theorem siteChainPin_of_mem (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {Λ : Finset V} {η : V → S}
    {v : V} (hv : v ∈ Λ) {σ : V → S} (hσ : AgreesOn Λ η σ) (hpos : 0 < pinWeight w Λ η σ)
    (τ : V → S) :
    siteChainPin w hw Λ η v σ τ = if τ = σ then 1 else 0 := by
  have h0 : ∀ s ∈ (univ : Finset S), s ≠ σ v → pinWeight w Λ η (update σ v s) = 0 := by
    intro s _ hs
    refine pinWeight_of_not_agreesOn fun hA => hs ?_
    have h1 : s = η v := by
      have h2 := hA v hv
      rwa [update_self] at h2
    rw [h1, hσ v hv]
  have hZloc : Zloc (pinWeight w Λ η) σ v = pinWeight w Λ η σ := by
    rw [Zloc_apply,
      Finset.sum_eq_single (σ v) h0 fun hc => absurd (Finset.mem_univ (σ v)) hc,
      update_eq_self]
  rw [siteChainPin_apply, siteUpdate_of_Zloc_ne_zero (by rw [hZloc]; exact hpos.ne'), hZloc]
  by_cases hτ : τ = σ
  · subst hτ
    rw [if_pos (agreeOff_rfl v τ), if_pos rfl, div_self hpos.ne']
  · rw [if_neg hτ]
    by_cases hA : AgreeOff v σ τ
    · rw [if_pos hA]
      have hz : pinWeight w Λ η τ = 0 := by
        refine pinWeight_of_not_agreesOn fun hAg => hτ ?_
        funext u
        by_cases hu : u = v
        · subst hu
          rw [hAg u hv, hσ u hv]
        · exact (hA u hu).symm
      rw [hz, zero_div]
    · rw [if_neg hA]

section Glauber

variable [Nonempty V]

/-- The **pinned Glauber dynamics**: the Glauber dynamics of the conditional
system.  Note that it resamples *all* sites, including the pinned ones; at a
pinned site the conditional law is a point mass, so the chain holds still there
(`siteMarginal_pinWeight_of_mem`).  This is the chain the local-to-global
induction analyses at every pinning. -/
noncomputable def glauberPin (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S) :
    FinChain (V → S) :=
  glauber (pinWeight w Λ η) (pinWeight_nonneg hw Λ η)

theorem glauberPin_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (σ τ : V → S) :
    glauberPin w hw Λ η σ τ
      = (1 / (Fintype.card V : ℝ))
        * ∑ v, siteChain (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) v σ τ := rfl

/-- **The pinned Glauber dynamics is reversible with respect to the conditional
Gibbs measure.**  Nothing is proved here: `Glauber.glauber_reversible` already
covers every nonnegative weight, and `pinWeight w Λ η` is one. -/
theorem glauberPin_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) :
    Reversible (gibbsPin w hw Λ η hZ) (glauberPin w hw Λ η) :=
  glauber_reversible (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ

/-- The conditional Gibbs measure is stationary for the pinned Glauber
dynamics. -/
theorem glauberPin_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) :
    Stationary (gibbsPin w hw Λ η hZ) (glauberPin w hw Λ η) :=
  glauber_stationary (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ

/-- **The pinned Glauber dynamics is positive semidefinite.**  Together with a
Poincaré inequality for the conditional system this is what turns a pinned
spectral gap into a pinned *absolute* spectral gap; the local-to-global
argument needs it at every level of the induction. -/
theorem glauberPin_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V)
    (η : V → S) (hZ : 0 < Z (pinWeight w Λ η)) :
    NonnegDefinite (gibbsPin w hw Λ η hZ) (glauberPin w hw Λ η) :=
  glauber_nonnegDefinite (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ

end Glauber

/-! ### Pinning twice is pinning once -/

/-- The partition functions of a doubly pinned weight and of the corresponding
union pinning agree.  In particular each of the two positivity hypotheses below
implies the other. -/
theorem Z_pinWeight_union (w : (V → S) → ℝ) (Λ Λ' : Finset V) (η : V → S) :
    Z (pinWeight (pinWeight w Λ η) Λ' η) = Z (pinWeight w (Λ ∪ Λ') η) := by
  rw [pinWeight_union]

/-- **Conditioning a conditional measure is conditioning on the union.**
Together with `Pinning.pinWeight_union` this is the statement that the pinnings
form a directed system inside the category of weights, which is what lets the
local-to-global induction add one pinned site at a time. -/
theorem gibbsPin_pinWeight_union (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ Λ' : Finset V)
    (η : V → S) (hZ : 0 < Z (pinWeight (pinWeight w Λ η) Λ' η))
    (hZ' : 0 < Z (pinWeight w (Λ ∪ Λ') η)) :
    gibbsPin (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) Λ' η hZ
      = gibbsPin w hw (Λ ∪ Λ') η hZ' := by
  refine FinDist.ext fun σ => ?_
  rw [gibbsPin_apply, gibbsPin_apply, pinWeight_union]

end Closed

/-! ## One- and two-site masses

The building blocks of every marginal below.  They are *unnormalised*: dividing
by `Z w` turns `siteMass` into a marginal probability and `pairMass` into a
joint probability.  Keeping them unnormalised is what makes the symmetry
`pairMass_comm` — and hence detailed balance for the local walk — trivial. -/

section Mass

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The **one-site mass** `∑_{σ : σ v = s} w σ`: the total weight of the
configurations whose spin at `v` is `s`. -/
def siteMass (w : (V → S) → ℝ) (v : V) (s : S) : ℝ := ∑ σ, if σ v = s then w σ else 0

theorem siteMass_apply (w : (V → S) → ℝ) (v : V) (s : S) :
    siteMass w v s = ∑ σ, if σ v = s then w σ else 0 := rfl

theorem siteMass_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (v : V) (s : S) :
    0 ≤ siteMass w v s :=
  Finset.sum_nonneg fun σ _ => by split; exacts [hw σ, le_rfl]

/-- The one-site masses at `v` partition the total weight: `∑_s siteMass = Z`. -/
theorem sum_siteMass (w : (V → S) → ℝ) (v : V) : ∑ s, siteMass w v s = Z w := by
  simp only [siteMass_apply]
  rw [Finset.sum_comm, Z_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_ite_eq univ (σ v) fun _ => w σ, if_pos (Finset.mem_univ _)]

/-- The **two-site mass** `∑_{σ : σ u = a, σ v = b} w σ`. -/
def pairMass (w : (V → S) → ℝ) (u v : V) (a b : S) : ℝ :=
  ∑ σ, if σ u = a ∧ σ v = b then w σ else 0

theorem pairMass_apply (w : (V → S) → ℝ) (u v : V) (a b : S) :
    pairMass w u v a b = ∑ σ, if σ u = a ∧ σ v = b then w σ else 0 := rfl

theorem pairMass_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (u v : V) (a b : S) :
    0 ≤ pairMass w u v a b :=
  Finset.sum_nonneg fun σ _ => by split; exacts [hw σ, le_rfl]

/-- **The two-site mass is symmetric.**  This one line is the whole of detailed
balance for the local walk. -/
theorem pairMass_comm (w : (V → S) → ℝ) (u v : V) (a b : S) :
    pairMass w u v a b = pairMass w v u b a := by
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : σ u = a <;> by_cases h2 : σ v = b <;> simp [h1, h2]

/-- Summing a two-site mass over the second spin recovers the one-site mass. -/
theorem sum_pairMass (w : (V → S) → ℝ) (u v : V) (a : S) :
    ∑ b, pairMass w u v a b = siteMass w u a := by
  simp only [pairMass_apply, siteMass_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ u = a
  · simp [h]
  · simp [h]

/-- A two-site mass is dominated by the corresponding one-site mass. -/
theorem pairMass_le_siteMass {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (u v : V) (a b : S) :
    pairMass w u v a b ≤ siteMass w u a := by
  rw [← sum_pairMass w u v a]
  exact Finset.single_le_sum (fun b' _ => pairMass_nonneg hw u v a b') (Finset.mem_univ b)

/-- Two incompatible constraints at the *same* site carry no mass. -/
theorem pairMass_self_of_ne (w : (V → S) → ℝ) (u : V) {a b : S} (h : a ≠ b) :
    pairMass w u u a b = 0 :=
  Finset.sum_eq_zero fun _ _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

/-- A null one-site mass forces the two-site masses above it to vanish.  This is
the branch on which every degenerate row of the local walk collapses. -/
theorem pairMass_eq_zero_of_siteMass_eq_zero {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (u v : V)
    (a b : S) (h : siteMass w u a = 0) : pairMass w u v a b = 0 :=
  le_antisymm (h ▸ pairMass_le_siteMass hw u v a b) (pairMass_nonneg hw u v a b)

end Mass

/-! ## Extending a pinning by one site

The combinatorial step underlying `π_{η,1}`: one-site extensions of a pinning
are pinnings of the one-larger set. -/

section AgreesInsert

variable {V : Type*} [DecidableEq V] {S : Type*}

/-- Pinning one further site: agreeing with the extended pinning is agreeing
with the old one and having the prescribed spin at the new site. -/
theorem agreesOn_insert_update {Λ : Finset V} {η : V → S} {v : V} (hv : v ∉ Λ) (s : S)
    (σ : V → S) :
    AgreesOn (insert v Λ) (update η v s) σ ↔ σ v = s ∧ AgreesOn Λ η σ := by
  constructor
  · intro h
    refine ⟨by simpa using h v (Finset.mem_insert_self v Λ), fun u hu => ?_⟩
    have hne : u ≠ v := fun hc => hv (hc ▸ hu)
    have := h u (Finset.mem_insert_of_mem hu)
    rwa [update_of_ne hne] at this
  · rintro ⟨hs, hΛ⟩ u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · simpa using hs
    · rw [update_of_ne (fun hc : u = v => hv (hc ▸ hu))]
      exact hΛ u hu

end AgreesInsert

/-! ## Single-site marginals

`siteMarginal w hw hZ v` is the law of `σ v` when `σ ~ gibbs w`.  Applied to a
pinned weight it is the conditional marginal `μ_η(σ(v) = ·)`, which is the
quantity the influence matrix and the local walk are built from. -/

section Marginal

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The **single-site marginal** of a Gibbs measure at the site `v`, as a
distribution on spins: `s ↦ siteMass w v s / Z w`. -/
noncomputable def siteMarginal (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) :
    FinDist S where
  p s := siteMass w v s / Z w
  p_nonneg s := div_nonneg (siteMass_nonneg hw v s) hZ.le
  p_sum := by rw [← Finset.sum_div, sum_siteMass, div_self hZ.ne']

theorem siteMarginal_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) (s : S) :
    siteMarginal w hw hZ v s = siteMass w v s / Z w := rfl

/-- **The marginal really is a marginal**: it is the Gibbs probability of the
event `{σ | σ v = s}`. -/
theorem siteMarginal_eq_Pr (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) (s : S) :
    siteMarginal w hw hZ v s = Pr (gibbs w hw hZ) (univ.filter fun σ => σ v = s) := by
  rw [siteMarginal_apply, Pr_apply, Finset.sum_filter, siteMass_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ v = s
  · rw [if_pos h, if_pos h, gibbs_apply]
  · rw [if_neg h, if_neg h, zero_div]

/-- At an already-pinned site the pinned weight only charges the spin `η v`. -/
theorem siteMass_pinWeight_of_mem (w : (V → S) → ℝ) {Λ : Finset V} {η : V → S} {v : V}
    (hv : v ∈ Λ) {s : S} (hs : s ≠ η v) : siteMass (pinWeight w Λ η) v s = 0 := by
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : σ v = s
  · rw [if_pos h]
    refine pinWeight_of_not_agreesOn fun hA => hs ?_
    rw [← h]
    exact hA v hv
  · rw [if_neg h]

/-- **The marginal at an already-pinned site is the point mass at `η v`**, on the
nose: `siteMarginal … v = δ_{η v}` as distributions.  Conditioning has already
decided the spin there, so there is nothing left to resample.  This is the
compatibility the local walk needs in order to ignore the pinned sites. -/
theorem siteMarginal_pinWeight_of_mem (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {Λ : Finset V}
    {η : V → S} (hZ : 0 < Z (pinWeight w Λ η)) {v : V} (hv : v ∈ Λ) :
    siteMarginal (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ v = FinDist.dirac (η v) := by
  have key : ∀ t : S, t ≠ η v →
      siteMarginal (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ v t = 0 := by
    intro t ht
    rw [siteMarginal_apply, siteMass_pinWeight_of_mem w hv ht, zero_div]
  refine FinDist.ext fun s => ?_
  rw [FinDist.dirac_apply]
  by_cases hs : s = η v
  · subst hs
    rw [if_pos rfl]
    have hsum : ∑ t, siteMarginal (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ v t = 1 :=
      FinDist.sum_coe _
    rwa [Finset.sum_eq_single (η v) (fun t _ ht => key t ht)
      (fun hc => absurd (Finset.mem_univ (η v)) hc)] at hsum
  · rw [if_neg hs, key s hs]

/-- **The one-site marginal is the mass of the one-site-larger pinning.**  This
is the spin-system form of `LocalWalk.mu_starWeight` at a single extra element:
extending the pinning `η` on `Λ` by `v ↦ s` has partition function
`siteMass (pinWeight w Λ η) v s`.  It is what identifies `π_{η,1}` below with
the monograph's distribution "one level above `η`". -/
theorem Z_pinWeight_insert (w : (V → S) → ℝ) {Λ : Finset V} {η : V → S} {v : V} (hv : v ∉ Λ)
    (s : S) :
    Z (pinWeight w (insert v Λ) (update η v s)) = siteMass (pinWeight w Λ η) v s := by
  rw [Z_apply, siteMass_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pinWeight_apply]
  by_cases h : σ v = s
  · rw [if_pos h, pinWeight_apply]
    by_cases hA : AgreesOn Λ η σ
    · rw [if_pos hA, if_pos ((agreesOn_insert_update hv s σ).mpr ⟨h, hA⟩)]
    · rw [if_neg hA, if_neg fun hc => hA ((agreesOn_insert_update hv s σ).mp hc).2]
  · rw [if_neg h, if_neg fun hc => h ((agreesOn_insert_update hv s σ).mp hc).1]

/-- **Pinning `v` to `s` makes the marginal at `v` the point mass at `s`.**  The
`insert` form of `siteMarginal_pinWeight_of_mem`, and the shape in which the
one-site extensions of a pinning are consumed downstream. -/
theorem siteMarginal_pinWeight_insert (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) {Λ : Finset V}
    {η : V → S} {v : V} (s : S)
    (hZ : 0 < Z (pinWeight w (insert v Λ) (update η v s))) (t : S) :
    siteMarginal (pinWeight w (insert v Λ) (update η v s))
        (pinWeight_nonneg hw (insert v Λ) (update η v s)) hZ v t
      = if t = s then 1 else 0 := by
  have h := congrFun (congrArg FinDist.p (siteMarginal_pinWeight_of_mem w hw
    (Λ := insert v Λ) (η := update η v s) hZ (Finset.mem_insert_self v Λ))) t
  rwa [FinDist.dirac_apply, update_self] at h

end Marginal

/-! ## The distribution one site above a pinning

This is the monograph's `π_{η,1}` ([CSV23]): from the pinning `η`
on `Λ`, choose a free site `v ∉ Λ` uniformly at random and then a spin `s` from
the conditional marginal at `v`.  Only `j = 1` is ever used in the monograph and
only `j = 1` is built here.

The hypothesis `Λ.card < Fintype.card V` — at least one free site — sits in the
*data* rather than on the lemmas, because without it `p_sum` is false: this is
the same judgement call as `LocalWalk.linkDist`, and per the conventions of the
development a hypothesis genuinely needed for well-formedness belongs in the
definition. -/

section OneSiteAbove

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The **one-site-above distribution** `π_{η,1}` on (site, spin) pairs:

`π_{η,1}(v, s) = μ_η(σ(v) = s) / (n - |Λ|)` for `v ∉ Λ`, and `0` for `v ∈ Λ`.

The weight `w` is the already-pinned weight `pinWeight w₀ Λ η`; the set `Λ`
enters only through the uniform choice of a free site. -/
noncomputable def pinDist (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) : FinDist (V × S) where
  p x := if x.1 ∈ Λ then 0
    else siteMass w x.1 x.2 / (((Fintype.card V - Λ.card : ℕ) : ℝ) * Z w)
  p_nonneg x := by
    dsimp only
    split
    · exact le_rfl
    · exact div_nonneg (siteMass_nonneg hw _ _) (mul_nonneg (Nat.cast_nonneg _) hZ.le)
  p_sum := by
    have hD : ((Fintype.card V - Λ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hZ' : Z w ≠ 0 := hZ.ne'
    rw [Fintype.sum_prod_type]
    have hstep : ∀ v : V,
        (∑ s : S, if v ∈ Λ then (0 : ℝ)
            else siteMass w v s / (((Fintype.card V - Λ.card : ℕ) : ℝ) * Z w))
          = if v ∈ Λᶜ then (((Fintype.card V - Λ.card : ℕ) : ℝ))⁻¹ else 0 := by
      intro v
      by_cases h : v ∈ Λ
      · rw [if_neg (Finset.not_mem_compl.mpr h)]
        exact Finset.sum_eq_zero fun s _ => if_pos h
      · rw [if_pos (Finset.mem_compl.mpr h),
          Finset.sum_congr rfl fun s _ => if_neg h, ← Finset.sum_div, sum_siteMass,
          mul_comm, ← div_div, div_self hZ', one_div]
    rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, Finset.card_compl, mul_inv_cancel₀ hD]

theorem pinDist_apply (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) (x : V × S) :
    pinDist w Λ hw hZ hΛ x = if x.1 ∈ Λ then 0
      else siteMass w x.1 x.2 / (((Fintype.card V - Λ.card : ℕ) : ℝ) * Z w) := rfl

/-- `pinDist_apply` on an explicit (site, spin) pair. -/
theorem pinDist_mk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) (v : V) (s : S) :
    pinDist w Λ hw hZ hΛ (v, s) = if v ∈ Λ then 0
      else siteMass w v s / (((Fintype.card V - Λ.card : ℕ) : ℝ) * Z w) := rfl

/-- `π_{η,1}` ignores the pinned sites. -/
theorem pinDist_of_mem (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) {x : V × S} (hx : x.1 ∈ Λ) :
    pinDist w Λ hw hZ hΛ x = 0 := by
  rw [pinDist_apply, if_pos hx]

/-- **`π_{η,1}` is "uniform site, then marginal spin".**  At a free site the mass
is the conditional marginal divided by the number of free sites. -/
theorem pinDist_eq_siteMarginal (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card < Fintype.card V) {v : V} (hv : v ∉ Λ) (s : S) :
    pinDist w Λ hw hZ hΛ (v, s)
      = (1 / ((Fintype.card V - Λ.card : ℕ) : ℝ)) * siteMarginal w hw hZ v s := by
  rw [pinDist_mk, if_neg hv, siteMarginal_apply, one_div, div_eq_mul_inv, div_eq_mul_inv,
    mul_inv]
  ring

end OneSiteAbove

/-! ## The local walk `Q_η`

The monograph's local walk ([CSV23]) at the pinning `η` on `Λ`:
from a free (site, spin) pair `(i, a)` it jumps to a *different* free site `j`
with a spin `b` drawn from the conditional law of `σ(j)` given `σ(i) = a`,
divided by the number `n - |Λ| - 1` of admissible sites.  It is
**non-backtracking**: the whole block `j = i` is zeroed, which is why the walk
is not positive semidefinite and why no such claim is made.

The guard structure mirrors `Techniques.LocalWalk.localWalk` exactly, and for
the same reason: the two degenerate rows (a pinned site, a null marginal) hold
in place purely so that the matrix is stochastic on all of `V × S`.  Note in
particular that `Q_η` is *not* the down-up walk of the pinned complex at the
bottom level — that walk is the independent sampler, as `Techniques.LocalWalk`
records. -/

section LocalWalk

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The **local walk** `Q_η` on (site, spin) pairs, for a pinning of `Λ` with at
least two free sites:

`Q_η((i,a), (j,b)) = pairMass w i j a b / ((n - |Λ| - 1) · siteMass w i a)`

for `i, j ∉ Λ` with `j ≠ i` and `siteMass w i a > 0`, and `0` when `j ∈ Λ` or
`j = i`.  The weight `w` is the already-pinned weight `pinWeight w₀ Λ η`, so the
quotient is `μ_η(σ(j) = b | σ(i) = a) / (n - |Λ| - 1)`, which is the monograph's
formula. -/
noncomputable def pinLocalWalk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hΛ : Λ.card + 1 < Fintype.card V) : FinChain (V × S) where
  P x y :=
    if x.1 ∉ Λ ∧ 0 < siteMass w x.1 x.2 then
      (if y.1 ∉ Λ ∧ y.1 ≠ x.1 then
        pairMass w x.1 y.1 x.2 y.2
          / (((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) * siteMass w x.1 x.2)
      else 0)
    else (if y = x then 1 else 0)
  P_nonneg x y := by
    dsimp only
    split
    · split
      · exact div_nonneg (pairMass_nonneg hw _ _ _ _)
          (mul_nonneg (Nat.cast_nonneg _) (siteMass_nonneg hw _ _))
      · exact le_rfl
    · split
      · exact zero_le_one
      · exact le_rfl
  P_sum x := by
    by_cases h : x.1 ∉ Λ ∧ 0 < siteMass w x.1 x.2
    · simp only [if_pos h]
      have hD : ((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm : siteMass w x.1 x.2 ≠ 0 := h.2.ne'
      rw [Fintype.sum_prod_type]
      have hstep : ∀ j : V,
          (∑ b : S, if j ∉ Λ ∧ j ≠ x.1 then
              pairMass w x.1 j x.2 b
                / (((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) * siteMass w x.1 x.2)
            else 0)
            = if j ∈ Λᶜ.erase x.1 then (((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ))⁻¹ else 0 := by
        intro j
        by_cases hj : j ∉ Λ ∧ j ≠ x.1
        · rw [if_pos (Finset.mem_erase.mpr ⟨hj.2, Finset.mem_compl.mpr hj.1⟩),
            Finset.sum_congr rfl fun b _ => if_pos hj, ← Finset.sum_div, sum_pairMass,
            mul_comm, ← div_div, div_self hm, one_div]
        · rw [if_neg fun hc => hj ⟨Finset.mem_compl.mp (Finset.mem_of_mem_erase hc),
            (Finset.mem_erase.mp hc).1⟩]
          exact Finset.sum_eq_zero fun b _ => if_neg hj
      have hcard : ((Λᶜ.erase x.1).card : ℝ) = ((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) := by
        rw [Finset.card_erase_of_mem (Finset.mem_compl.mpr h.1), Finset.card_compl, Nat.sub_sub]
      rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, hcard, mul_inv_cancel₀ hD]
    · simp only [if_neg h]
      simp

theorem pinLocalWalk_apply (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hΛ : Λ.card + 1 < Fintype.card V) (x y : V × S) :
    pinLocalWalk w Λ hw hΛ x y =
      if x.1 ∉ Λ ∧ 0 < siteMass w x.1 x.2 then
        (if y.1 ∉ Λ ∧ y.1 ≠ x.1 then
          pairMass w x.1 y.1 x.2 y.2
            / (((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) * siteMass w x.1 x.2)
        else 0)
      else (if y = x then 1 else 0) := rfl

/-- `pinLocalWalk_apply` on explicit (site, spin) pairs. -/
theorem pinLocalWalk_mk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hΛ : Λ.card + 1 < Fintype.card V) (i : V) (a : S) (j : V) (b : S) :
    pinLocalWalk w Λ hw hΛ (i, a) (j, b) =
      if i ∉ Λ ∧ 0 < siteMass w i a then
        (if j ∉ Λ ∧ j ≠ i then
          pairMass w i j a b / (((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) * siteMass w i a)
        else 0)
      else (if (j, b) = (i, a) then 1 else 0) := rfl

/-- **The local walk is non-backtracking**: on the rows that matter it never
stays where it is, not even by changing the spin at the current site. -/
theorem pinLocalWalk_diag (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hΛ : Λ.card + 1 < Fintype.card V) {x : V × S} (hx : x.1 ∉ Λ)
    (hm : 0 < siteMass w x.1 x.2) (b : S) :
    pinLocalWalk w Λ hw hΛ x (x.1, b) = 0 := by
  rw [pinLocalWalk_apply, if_pos ⟨hx, hm⟩, if_neg fun hc => hc.2 rfl]

/-- **The detailed-balance cell of the local walk.**  For all `x = (i,a)` and
`y = (j,b)`,

`π_{η,1}(x) · Q_η(x, y) = pairMass w i j a b / ((n-k)(n-k-1) · Z w)`

when `i, j ∉ Λ` are distinct, and `0` otherwise.  Every degenerate branch
collapses: `π_{η,1}` vanishes at a pinned site and at a null marginal (in which
case `pairMass_eq_zero_of_siteMass_eq_zero` kills the right-hand side too), and
`Q_η` vanishes whenever `j ∈ Λ` or `j = i`.

Reversibility is read off from this by swapping `x` and `y`: the denominator
mentions neither, and the numerator is symmetric by `pairMass_comm`. -/
theorem pinDist_mul_pinLocalWalk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) (x y : V × S) :
    pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ) x * pinLocalWalk w Λ hw hΛ x y
      = if x.1 ∉ Λ ∧ y.1 ∉ Λ ∧ x.1 ≠ y.1 then
          pairMass w x.1 y.1 x.2 y.2
            / (((Fintype.card V - Λ.card : ℕ) : ℝ)
              * ((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) * Z w)
        else 0 := by
  have hD1 : ((Fintype.card V - Λ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD2 : ((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hZ' : Z w ≠ 0 := hZ.ne'
  have hnull : ¬ (0 < siteMass w x.1 x.2) → pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ) x = 0 := by
    intro hA
    have h0 : siteMass w x.1 x.2 = 0 := le_antisymm (not_lt.mp hA) (siteMass_nonneg hw _ _)
    rw [pinDist_apply]
    split
    · rfl
    · rw [h0, zero_div]
  by_cases hi : x.1 ∈ Λ
  · rw [pinDist_apply, if_pos hi, zero_mul, if_neg fun h => h.1 hi]
  · by_cases hj : y.1 ∈ Λ
    · rw [if_neg fun h => h.2.1 hj]
      by_cases hA : 0 < siteMass w x.1 x.2
      · have hz : pinLocalWalk w Λ hw hΛ x y = 0 := by
          rw [pinLocalWalk_apply, if_pos ⟨hi, hA⟩, if_neg fun hc => hc.1 hj]
        rw [hz, mul_zero]
      · rw [hnull hA, zero_mul]
    · by_cases hij : x.1 = y.1
      · rw [if_neg fun h => h.2.2 hij]
        by_cases hA : 0 < siteMass w x.1 x.2
        · have hz : pinLocalWalk w Λ hw hΛ x y = 0 := by
            rw [pinLocalWalk_apply, if_pos ⟨hi, hA⟩, if_neg fun hc => hc.2 hij.symm]
          rw [hz, mul_zero]
        · rw [hnull hA, zero_mul]
      · rw [if_pos ⟨hi, hj, hij⟩]
        by_cases hA : 0 < siteMass w x.1 x.2
        · have hA' : siteMass w x.1 x.2 ≠ 0 := hA.ne'
          rw [pinDist_apply, if_neg hi, pinLocalWalk_apply, if_pos ⟨hi, hA⟩,
            if_pos ⟨hj, fun hc => hij hc.symm⟩]
          field_simp
          ring
        · have h0 : siteMass w x.1 x.2 = 0 := le_antisymm (not_lt.mp hA) (siteMass_nonneg hw _ _)
          rw [hnull hA, zero_mul,
            pairMass_eq_zero_of_siteMass_eq_zero hw x.1 y.1 x.2 y.2 h0, zero_div]

/-- **The local walk is reversible with respect to `π_{η,1}`.**

The detailed-balance cell is symmetric under `x ↔ y`, because the denominator
does not mention either and `pairMass w i j a b = pairMass w j i b a`. -/
theorem pinLocalWalk_reversible (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) :
    Reversible (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) (pinLocalWalk w Λ hw hΛ) := by
  intro x y
  rw [pinDist_mul_pinLocalWalk w Λ hw hZ hΛ x y, pinDist_mul_pinLocalWalk w Λ hw hZ hΛ y x]
  by_cases h : x.1 ∉ Λ ∧ y.1 ∉ Λ ∧ x.1 ≠ y.1
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, pairMass_comm]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩]

/-- `π_{η,1}` is stationary for the local walk — the monograph's `rem:second`. -/
theorem pinLocalWalk_stationary (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) :
    Stationary (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) (pinLocalWalk w Λ hw hΛ) :=
  (pinLocalWalk_reversible w Λ hw hZ hΛ).stationary

end LocalWalk

/-! ## The bridge to the simplicial-complex side

`Techniques.LocalWalk` builds the local walk on the ground set of a weighted
complex, and `Chains.LevelEncoding` encodes a spin system as such a complex on
the ground set `V × S`.  So `Q_η` has been built twice, once on each side, and
the two constructions must agree.  They do — **on the nose**, not merely on the
support — and this section proves it.

The translation is `pinGraph Λ η = {(v, η v) : v ∈ Λ}`, the face encoding the
pinning.  Under it the three dictionary lemmas
`mu_graphWeight_pinGraph`, `mu_graphWeight_insert_pinGraph` and
`mu_graphWeight_insert_two_pinGraph` turn every `mu` occurring in `linkDist` and
`localWalk` into a `Z`, a `siteMass` or a `pairMass`.

The guards of the two definitions are *not* literally the same — `localWalk`
excludes `e' ∈ insert e τ` while `pinLocalWalk` excludes `j ∈ Λ` and `j = i` —
and the discrepancy is real: the pair `(j, b)` with `j ∈ Λ` and `b ≠ η j` is
outside the face but inside the pinned set.  It is harmless because such a pair
carries no mass at all, which is the content of the two zero lemmas
`pairMass_self_of_ne` and `siteMass_pinWeight_of_mem`. -/

section PinGraph

variable {V : Type*} [DecidableEq V] {S : Type*} [DecidableEq S]

/-- The **graph of a pinning**: `η` on `Λ` viewed as the face
`{(v, η v) : v ∈ Λ}` of the ground set `V × S`.  This is the object
`Techniques.LocalWalk` calls `τ`. -/
def pinGraph (Λ : Finset V) (η : V → S) : Finset (V × S) := Λ.image fun v => (v, η v)

@[simp] theorem mem_pinGraph_iff (Λ : Finset V) (η : V → S) (v : V) (s : S) :
    (v, s) ∈ pinGraph Λ η ↔ v ∈ Λ ∧ η v = s := by
  simp only [pinGraph, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, huv⟩
    have h1 : u = v := congrArg Prod.fst huv
    subst h1
    exact ⟨hu, congrArg Prod.snd huv⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- The pinning face has the cardinality of the pinned set: the level of the
complex is the number of pinned sites. -/
@[simp] theorem pinGraph_card (Λ : Finset V) (η : V → S) : (pinGraph Λ η).card = Λ.card :=
  Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h

end PinGraph

section PinGraphSubset

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [DecidableEq S]

/-- **Containing the pinning face is agreeing with the pinning.**  This is the
dictionary entry that makes everything else a rewrite. -/
theorem pinGraph_subset_graph_iff (Λ : Finset V) (η σ : V → S) :
    pinGraph Λ η ⊆ graph σ ↔ AgreesOn Λ η σ := by
  constructor
  · intro h v hv
    exact (mem_graph_iff σ v (η v)).mp (h ((mem_pinGraph_iff Λ η v (η v)).mpr ⟨hv, rfl⟩))
  · intro h p hp
    obtain ⟨v, s⟩ := p
    obtain ⟨hv, hs⟩ := (mem_pinGraph_iff Λ η v s).mp hp
    exact (mem_graph_iff σ v s).mpr (hs ▸ h v hv)

end PinGraphSubset

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The derived weight of the pinning face is the pinned partition function. -/
theorem mu_graphWeight_pinGraph (w : (V → S) → ℝ) (Λ : Finset V) (η : V → S) :
    mu (graphWeight w) (pinGraph Λ η) = Z (pinWeight w Λ η) := by
  rw [mu_graphWeight, Z_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pinWeight_apply]
  by_cases h : AgreesOn Λ η σ
  · rw [if_pos ((pinGraph_subset_graph_iff Λ η σ).mpr h), if_pos h]
  · rw [if_neg fun hc => h ((pinGraph_subset_graph_iff Λ η σ).mp hc), if_neg h]

/-- The derived weight one level above the pinning face is the one-site mass.
Compare `Z_pinWeight_insert`: the same statement in the language of pinnings. -/
theorem mu_graphWeight_insert_pinGraph (w : (V → S) → ℝ) (Λ : Finset V) (η : V → S)
    (v : V) (s : S) :
    mu (graphWeight w) (insert (v, s) (pinGraph Λ η)) = siteMass (pinWeight w Λ η) v s := by
  rw [mu_graphWeight, siteMass_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pinWeight_apply]
  by_cases h1 : σ v = s <;> by_cases h2 : AgreesOn Λ η σ <;>
    simp [h1, h2, Finset.insert_subset_iff, pinGraph_subset_graph_iff]

/-- The derived weight two levels above the pinning face is the two-site mass. -/
theorem mu_graphWeight_insert_two_pinGraph (w : (V → S) → ℝ) (Λ : Finset V) (η : V → S)
    (i j : V) (a b : S) :
    mu (graphWeight w) (insert (j, b) (insert (i, a) (pinGraph Λ η)))
      = pairMass (pinWeight w Λ η) i j a b := by
  rw [mu_graphWeight, pairMass_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pinWeight_apply]
  by_cases h1 : σ i = a <;> by_cases h2 : σ j = b <;> by_cases h3 : AgreesOn Λ η σ <;>
    simp [h1, h2, h3, Finset.insert_subset_iff, pinGraph_subset_graph_iff]

/-- **`π_{η,1}` is `LocalWalk.linkDist` of the encoded complex.**  Every entry
agrees, including the ones the two definitions guard differently: a pair
`(v, s)` with `v ∈ Λ` but `s ≠ η v` lies outside the pinning face, so
`linkDist` reaches for its formula rather than returning `0` — but the mass it
finds there is `0` anyway. -/
theorem pinDist_eq_linkDist (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η : V → S)
    (hZ : 0 < Z (pinWeight w Λ η)) (hΛ : Λ.card < Fintype.card V) (x : V × S) :
    pinDist (pinWeight w Λ η) Λ (pinWeight_nonneg hw Λ η) hZ hΛ x
      = linkDist (graphWeight w) (Fintype.card V) (pinGraph Λ η) (graphWeight_nonneg hw)
          (fun _ hT => graphWeight_supp w hT)
          (by rw [mu_graphWeight_pinGraph]; exact hZ)
          (by rw [pinGraph_card]; exact hΛ) x := by
  obtain ⟨v, s⟩ := x
  rw [pinDist_mk, linkDist_apply, pinGraph_card, mu_graphWeight_pinGraph,
    mu_graphWeight_insert_pinGraph]
  by_cases hv : v ∈ Λ
  · rw [if_pos hv]
    by_cases hs : η v = s
    · rw [if_pos ((mem_pinGraph_iff Λ η v s).mpr ⟨hv, hs⟩)]
    · rw [if_neg fun hc => hs ((mem_pinGraph_iff Λ η v s).mp hc).2,
        siteMass_pinWeight_of_mem w hv fun hc => hs hc.symm, zero_div]
  · rw [if_neg hv, if_neg fun hc => hv ((mem_pinGraph_iff Λ η v s).mp hc).1]

/-- **`Q_η` is `LocalWalk.localWalk` of the encoded complex.**  The local walk of
the spin system at a pinning and the local walk of the induced weighted complex
at the corresponding face are the *same matrix*, entry by entry.

This is the spin-system counterpart of `LevelEncoding.spinDownUp_apply_graph`,
and unlike that result it needs no "on the support" caveat: the degenerate rows
of the two constructions coincide as well, because the pairs on which the guards
disagree carry no mass. -/
theorem pinLocalWalk_eq_localWalk (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V)
    (η : V → S) (hΛ : Λ.card + 1 < Fintype.card V) (x y : V × S) :
    pinLocalWalk (pinWeight w Λ η) Λ (pinWeight_nonneg hw Λ η) hΛ x y
      = localWalk (graphWeight w) (Fintype.card V) (pinGraph Λ η) (graphWeight_nonneg hw)
          (fun _ hT => graphWeight_supp w hT) (by rw [pinGraph_card]; exact hΛ) x y := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  rw [pinLocalWalk_mk, localWalk_apply, pinGraph_card, mu_graphWeight_insert_pinGraph,
    mu_graphWeight_insert_two_pinGraph]
  by_cases hi : i ∈ Λ
  · -- a pinned site: both walks hold still
    have hg1 : ¬ (i ∉ Λ ∧ 0 < siteMass (pinWeight w Λ η) i a) := fun h => h.1 hi
    have hg2 : ¬ ((i, a) ∉ pinGraph Λ η ∧ 0 < siteMass (pinWeight w Λ η) i a) := by
      rintro ⟨hx, hpos⟩
      by_cases hs : η i = a
      · exact hx ((mem_pinGraph_iff Λ η i a).mpr ⟨hi, hs⟩)
      · rw [siteMass_pinWeight_of_mem w hi fun hc => hs hc.symm] at hpos
        exact lt_irrefl 0 hpos
    rw [if_neg hg1, if_neg hg2]
  · have hx : (i, a) ∉ pinGraph Λ η := fun hc => hi ((mem_pinGraph_iff Λ η i a).mp hc).1
    by_cases hm : 0 < siteMass (pinWeight w Λ η) i a
    · have hg1 : i ∉ Λ ∧ 0 < siteMass (pinWeight w Λ η) i a := ⟨hi, hm⟩
      have hg2 : (i, a) ∉ pinGraph Λ η ∧ 0 < siteMass (pinWeight w Λ η) i a := ⟨hx, hm⟩
      rw [if_pos hg1, if_pos hg2]
      by_cases hj : j ∉ Λ ∧ j ≠ i
      · have hy : (j, b) ∉ insert (i, a) (pinGraph Λ η) := by
          intro hc
          rcases Finset.mem_insert.mp hc with hc | hc
          · exact hj.2 (congrArg Prod.fst hc)
          · exact hj.1 ((mem_pinGraph_iff Λ η j b).mp hc).1
        rw [if_pos hj, if_pos hy]
      · rw [if_neg hj]
        by_cases hy : (j, b) ∉ insert (i, a) (pinGraph Λ η)
        · rw [if_pos hy]
          have hzero : pairMass (pinWeight w Λ η) i j a b = 0 := by
            by_cases hji : j = i
            · subst hji
              refine pairMass_self_of_ne _ _ fun hab => hy ?_
              rw [hab]
              exact Finset.mem_insert_self _ _
            · have hjΛ : j ∈ Λ := by
                by_contra hc
                exact hj ⟨hc, hji⟩
              have hb : b ≠ η j := fun hc =>
                hy (Finset.mem_insert_of_mem ((mem_pinGraph_iff Λ η j b).mpr ⟨hjΛ, hc.symm⟩))
              rw [pairMass_comm]
              exact pairMass_eq_zero_of_siteMass_eq_zero (pinWeight_nonneg hw Λ η) j i b a
                (siteMass_pinWeight_of_mem w hjΛ hb)
          rw [hzero, zero_div]
        · rw [if_neg hy]
    · have hg1 : ¬ (i ∉ Λ ∧ 0 < siteMass (pinWeight w Λ η) i a) := fun h => hm h.2
      have hg2 : ¬ ((i, a) ∉ pinGraph Λ η ∧ 0 < siteMass (pinWeight w Λ η) i a) :=
        fun h => hm h.2
      rw [if_neg hg1, if_neg hg2]

end Bridge

end Arlib.MarkovChains
