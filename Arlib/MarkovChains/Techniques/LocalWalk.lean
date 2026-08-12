/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Stars of faces, and the local walk

The local-to-global technique (§5.1 of the monograph) is an induction on the
levels of a weighted complex in which the inductive step is applied not to the
complex itself but to the *link* of a face: the complex obtained by conditioning
on containing a fixed face `τ`.  This module makes that step available, and it is
where the standing caveat of the area lives, so it is stated first.

**What is built here is the star of `τ`, not its link.**  `starWeight w τ` is `w`
restricted to the faces *containing* `τ`, on the same ground set and at the same
dimension `n`.  Its faces at level `j` are all `j`-subsets of the top faces
through `τ` — **including subsets that meet `τ`** — so `starPi w n j τ` charges
faces `ρ ⊆ τ`, which the monograph's `π_{τ,j}` must not
(`LinkRestriction.starPi_apply_of_subset`).  The link proper has dimension
`n − |τ|` and its faces are disjoint from `τ`; that is
`Techniques.LinkRestriction.linkShift`, and `linkShiftPi` is `π_{τ,j}`.

**The two agree at level one, and level one is all this module's downstream
consumers use.**  `linkDist` below is the honest `π_{τ,1}` — it is defined
directly, gives mass `0` to elements of `τ`, and is audited against the link's
own level-one distribution by `LinkRestriction.linkShiftPi_one_singleton`.  So
`localWalk`, its reversibility, and the `Q_η` bridge in `Chains.PinnedGlauber`
are unaffected by the star/link distinction.  It is `starPi` at `j ≥ 2` that is
not a link distribution, and nothing in the development consumes it there.

With that said, the star is a genuinely useful object, and the reason is a
triviality worth stating precisely: the star of `τ` is *again a weighted complex
on the same ground set and of the same dimension*.  This is exactly what
`Chains.Pinning` found for conditional Gibbs measures — **conditioning does not
leave the category** — so no new theory is needed and every result of
`Techniques.Levels` applies to it verbatim.  The only bookkeeping is a
normalisation: `starWeight w τ` sums to `mu w τ` rather than to `1`, so the
distributions are built from the normalised weight
`starWeightNorm w τ = starWeight w τ / mu w τ`.  The operators `up`, `down`,
`upDown`, `downUp` need no normalisation at all, since `Levels` never asks them
for `hsum`.

The workhorse is `mu_starWeight`: the derived weights of the star are the derived
weights of the original complex, shifted by `τ`.  Together with
`starWeight_union` — stars compose — it is what lets the local-to-global
induction descend one level at a time.

* `starWeight`, `starWeight_nonneg`, `starWeight_supp`, `starWeight_empty`,
  `starWeight_top`, `sum_starWeight` — the star weight and its elementary
  properties.  `sum_starWeight` is its partition function:
  `∑ σ, starWeight w τ σ = mu w τ`.
* `mu_starWeight` — **the workhorse**: `mu (starWeight w τ) ρ = mu w (τ ∪ ρ)`.
  Both sides are `∑ σ, if τ ∪ ρ ⊆ σ then w σ else 0` by `Finset.union_subset_iff`.
* `starWeight_union` — **stars compose**:
  `starWeight (starWeight w τ) ρ = starWeight w (τ ∪ ρ)`.
* `starWeightNorm` and `starWeightNorm_nonneg`, `starWeightNorm_supp`,
  `sum_starWeightNorm`, `mu_starWeightNorm` — the normalised star weight
  satisfies *all three* hypotheses of `Levels`.
* `starPi`, `starUp`, `starDown`, `starUpDown`, `starDownUp` — the level
  distributions and the four operators of the star complex, together with
  `star_up_down_adjoint`, `starUpDown_reversible`, `starUpDown_nonnegDefinite`,
  `starDownUp_reversible`, `starDownUp_nonnegDefinite`, … .  Each is one line:
  "apply `Levels` to the star".  Read `starPi w n j τ` as the level-`j`
  distribution of the *star*, and use `LinkRestriction.linkShiftPi` when the
  monograph's `π_{τ,j}` is wanted.
* `linkDist` — the paper's `π_{τ,1}`, the distribution one level above `τ` on
  ground-set elements: mass `mu w (insert e τ) / ((n - k) · mu w τ)` at `e ∉ τ`,
  and `0` at `e ∈ τ`.  This *is* the link's level-one distribution, transported
  along `e ↦ {e}`; it is not built from `starWeight`.  It is a distribution by
  `Levels.sum_insert_mu`, which exists for exactly this purpose.  The monograph
  only ever uses `j = 1`, so no general `π_{τ,j}` is built here.
* `linkDistOf` — the **guarded** variant of `linkDist`, added beside it rather
  than in place of it: total in `τ`, so that it can appear inside an average over
  a whole level, at the price of a `[Nonempty E]` instance for its junk value.
  The instance is unavoidable — `FinDist E` is an empty type when `E` is — and
  free, by `Levels.nonempty_of_weight`.
* `localWalk` — the local walk `Q_τ` on ground-set elements, which from `e`
  jumps to `e' ∉ τ ∪ {e}` with probability proportional to
  `mu w (τ ∪ {e, e'})`, with `linkDist_mul_localWalk` and
  **`localWalk_reversible`**, `localWalk_stationary`.

**Two deliberate choices.**  First, `localWalk` is defined directly rather than
as a walk of the star complex.  The tempting route — "`Q_τ` is `downUp` at the
bottom level" — is not available: `downUp _ n 0` first steps deterministically
down to `∅` and then goes up, so it is the *independent sampler* for the level-`1`
distribution and does not depend on its current state, whereas `Q_τ` does.  The
walk that is genuinely built from the operators is `upDown` at level `1`, and the
monograph's own computation (`rem:local-downup`) shows that this is
`(Q_τ + I)/(k+1)`-shaped, not `Q_τ`.  `Techniques.LocalWalkBridge` carries that
computation out, for the *link* rather than the star.  Second, `Q_τ` is *not*
asserted to be positive semidefinite, and indeed it is not: it is the
non-backtracking walk, and the monograph records `-1/(n-k-1)` in its spectrum.
Positive semidefiniteness in this development belongs to the up-down and down-up
walks, where `Techniques.Adjoint` supplies it for free.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Levels

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [DecidableEq E]

/-! ## The star weight

Conditioning a weighted complex on containing a face `τ` restricts the top-level
weight to the **star** of `τ` — the faces containing `τ`.  The result is a weight
on the same ground set, supported on the same level `n`; only the normalisation
changes.  It is *not* the link, whose dimension is `n − |τ|`; see
`Techniques.LinkRestriction` and the module docstring. -/

/-- The **star weight** of a face `τ`: the top-level weight `w` restricted to the
faces containing `τ`.  This is the top-level weight of the star complex, which
lives on the same ground set and has the same dimension as the original.

This is **not** the link of `τ`, which lives one dimension lower and whose faces
are disjoint from `τ`; that is `LinkRestriction.linkShift`. -/
def starWeight (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => if τ ⊆ σ then w σ else 0

/-- The defining formula for `starWeight`. -/
theorem starWeight_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    starWeight w τ σ = if τ ⊆ σ then w σ else 0 := rfl

/-- The star weight is nonnegative: hypothesis `hw` of `Levels` survives. -/
theorem starWeight_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    ∀ σ : Finset E, 0 ≤ starWeight w τ σ := by
  intro σ
  rw [starWeight_apply]
  split
  exacts [hw σ, le_rfl]

/-- The star weight is still supported on the top level: hypothesis `hsupp` of
`Levels` survives, with the *same* dimension `n`. -/
theorem starWeight_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) :
    ∀ σ : Finset E, σ.card ≠ n → starWeight w τ σ = 0 := by
  intro σ hσ
  rw [starWeight_apply]
  split
  exacts [hsupp σ hσ, rfl]

/-- The star of the empty face is the complex itself. -/
theorem starWeight_empty (w : Finset E → ℝ) : starWeight w ∅ = w := by
  funext σ
  rw [starWeight_apply, if_pos (Finset.empty_subset σ)]

/-- **Stars compose**: the star of `ρ` inside the star of `τ` is the star of
`τ ∪ ρ`.  This is what lets the local-to-global induction descend one level at a
time without ever leaving the category of weighted complexes. -/
theorem starWeight_union (w : Finset E → ℝ) (τ ρ : Finset E) :
    starWeight (starWeight w τ) ρ = starWeight w (τ ∪ ρ) := by
  funext σ
  simp only [starWeight_apply, Finset.union_subset_iff]
  by_cases hτ : τ ⊆ σ <;> by_cases hρ : ρ ⊆ σ <;> simp [hτ, hρ]

/-- The star of a *top-level* face is a point mass at that face: conditioning on
a full assignment leaves nothing to be random. -/
theorem starWeight_top {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτ : τ.card = n)
    (σ : Finset E) : starWeight w τ σ = if σ = τ then w τ else 0 := by
  rw [starWeight_apply]
  by_cases h : σ = τ
  · subst h
    rw [if_pos Finset.Subset.rfl, if_pos rfl]
  · rw [if_neg h]
    by_cases hsub : τ ⊆ σ
    · rw [if_pos hsub]
      refine hsupp σ fun hcard => h ?_
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · rw [if_neg hsub]

section Fintype

variable [Fintype E]

/-- **The derived weights of a star are the derived weights of the complex,
shifted by `τ`**: `mu (starWeight w τ) ρ = mu w (τ ∪ ρ)`.

Both sides are `∑ σ, if τ ∪ ρ ⊆ σ then w σ else 0`, by `Finset.union_subset_iff`.
Every quantitative statement about the star is obtained from this one identity. -/
theorem mu_starWeight (w : Finset E → ℝ) (τ ρ : Finset E) :
    mu (starWeight w τ) ρ = mu w (τ ∪ ρ) := by
  simp only [mu_apply, starWeight_apply, Finset.union_subset_iff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hτ : τ ⊆ σ <;> by_cases hρ : ρ ⊆ σ <;> simp [hτ, hρ]

/-- The partition function of the star is the derived weight of `τ`:
`∑ σ, starWeight w τ σ = mu w τ`.  This is the only thing that stops
`starWeight` from being a weight in the sense of `Levels`, and the reason for
`starWeightNorm` below. -/
theorem sum_starWeight (w : Finset E → ℝ) (τ : Finset E) :
    ∑ σ : Finset E, starWeight w τ σ = mu w τ := rfl

/-! ## The normalised star weight

`Levels.pi` needs a weight of total mass `1`; dividing by `mu w τ` supplies it.
The operators `up`, `down`, `upDown`, `downUp` do not need the normalisation,
but it costs nothing to use the same weight throughout. -/

/-- The **normalised star weight**, `starWeight w τ / mu w τ`.  This is the
top-level weight of the star as a *probability*-weighted complex: it satisfies
all three hypotheses `hw`, `hsupp`, `hsum` of `Techniques.Levels`. -/
noncomputable def starWeightNorm (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => starWeight w τ σ / mu w τ

/-- The defining formula for `starWeightNorm`. -/
theorem starWeightNorm_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    starWeightNorm w τ σ = starWeight w τ σ / mu w τ := rfl

/-- Hypothesis `hw` for the star. -/
theorem starWeightNorm_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    ∀ σ : Finset E, 0 ≤ starWeightNorm w τ σ :=
  fun σ => div_nonneg (starWeight_nonneg hw τ σ) (mu_nonneg hw τ)

/-- Hypothesis `hsupp` for the star: the star has the same dimension `n`. -/
theorem starWeightNorm_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) :
    ∀ σ : Finset E, σ.card ≠ n → starWeightNorm w τ σ = 0 := by
  intro σ hσ
  rw [starWeightNorm_apply, starWeight_supp hsupp τ σ hσ, zero_div]

/-- Hypothesis `hsum` for the star: the normalised star weight is a probability
weight, provided `τ` is not a null face. -/
theorem sum_starWeightNorm (w : Finset E → ℝ) (τ : Finset E) (hpos : 0 < mu w τ) :
    ∑ σ : Finset E, starWeightNorm w τ σ = 1 := by
  have h : ∀ σ : Finset E, starWeightNorm w τ σ = starWeight w τ σ / mu w τ :=
    fun σ => rfl
  rw [Finset.sum_congr rfl fun σ _ => h σ, ← Finset.sum_div, sum_starWeight,
    div_self hpos.ne']

/-- `mu_starWeight` in normalised form: `mu (starWeightNorm w τ) ρ` is the
conditional derived weight `mu w (τ ∪ ρ) / mu w τ`. -/
theorem mu_starWeightNorm (w : Finset E → ℝ) (τ ρ : Finset E) :
    mu (starWeightNorm w τ) ρ = mu w (τ ∪ ρ) / mu w τ := by
  have hstep : ∀ σ : Finset E,
      (if ρ ⊆ σ then starWeightNorm w τ σ else 0)
        = (if ρ ⊆ σ then starWeight w τ σ else 0) / mu w τ := by
    intro σ
    rw [starWeightNorm_apply]
    split
    · rfl
    · rw [zero_div]
  rw [mu_apply, Finset.sum_congr rfl fun σ _ => hstep σ, ← Finset.sum_div,
    show (∑ σ : Finset E, if ρ ⊆ σ then starWeight w τ σ else 0) = mu w (τ ∪ ρ) from
      mu_starWeight w τ ρ]

/-! ## The star is a weighted complex

Every definition of `Techniques.Levels` instantiates at the star with no work at
all.  The definitions below are named purely for readability downstream: each is
the corresponding `Levels` notion applied to `starWeightNorm w τ`, and each
theorem is the corresponding `Levels` theorem, verbatim. -/

/-- The **level-`k` distribution of the star of `τ`**: `Levels.pi` applied to the
normalised star weight.

For `k ≥ 2` this is **not** the monograph's `π_{τ,k}`: it charges the `k`-subsets
of `τ` itself (`LinkRestriction.starPi_apply_of_subset`).  The monograph's
distribution is `LinkRestriction.linkShiftPi`. -/
noncomputable def starPi (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k ≤ n) : FinDist (Finset E) :=
  pi (starWeightNorm w τ) n k (starWeightNorm_nonneg hw τ) (starWeightNorm_supp hsupp τ)
    (sum_starWeightNorm w τ hpos) hk

/-- The level distributions of the star in closed form: mass
`mu w (τ ∪ ρ) / (mu w τ · binom n k)` on the faces of cardinality `k`. -/
theorem starPi_apply (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k ≤ n) (ρ : Finset E) :
    starPi w n k τ hw hsupp hpos hk ρ =
      if ρ.card = k then mu w (τ ∪ ρ) / (mu w τ * (n.choose k : ℝ)) else 0 := by
  rw [starPi, pi_apply]
  split
  · rw [mu_starWeightNorm, div_div]
  · rfl

/-- The **up operator of the star**. -/
noncomputable def starUp (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  up (starWeightNorm w τ) n k (starWeightNorm_nonneg hw τ) (starWeightNorm_supp hsupp τ) hk

/-- The **down operator of the star**.  It is literally `Levels.down`: the down
operator deletes a uniformly random element and never looks at the weight, so
conditioning cannot change it. -/
noncomputable def starDown (k : ℕ) : FinChain (Finset E) := down k

/-- The **up-down walk of the star** on level `k`. -/
noncomputable def starUpDown (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  upDown (starWeightNorm w τ) n k (starWeightNorm_nonneg hw τ) (starWeightNorm_supp hsupp τ) hk

/-- The **down-up walk of the star** on level `k + 1`. -/
noncomputable def starDownUp (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  downUp (starWeightNorm w τ) n k (starWeightNorm_nonneg hw τ) (starWeightNorm_supp hsupp τ) hk

/-- **The up and down operators of the star are mutually adjoint.**  This is
`Levels.up_down_adjoint` applied to the star, and it is the entire inductive step
of the local-to-global argument: everything below follows from it. -/
theorem star_up_down_adjoint (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Adjoint (starPi w n k τ hw hsupp hpos hk.le) (starPi w n (k + 1) τ hw hsupp hpos hk)
      (starUp w n k τ hw hsupp hk) (starDown k) :=
  up_down_adjoint (starWeightNorm w τ) n k (starWeightNorm_nonneg hw τ)
    (starWeightNorm_supp hsupp τ) (sum_starWeightNorm w τ hpos) hk

/-- The up-down walk of the star is reversible with respect to the star's
level-`k` distribution. -/
theorem starUpDown_reversible (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Reversible (starPi w n k τ hw hsupp hpos hk.le) (starUpDown w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible

/-- The star's level-`k` distribution is stationary for the star's up-down walk. -/
theorem starUpDown_stationary (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Stationary (starPi w n k τ hw hsupp hpos hk.le) (starUpDown w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_stationary

/-- **The up-down walk of the star is positive semidefinite**, for the same
structural reason as in the ambient complex and with no eigenvalue argument. -/
theorem starUpDown_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    NonnegDefinite (starPi w n k τ hw hsupp hpos hk.le) (starUpDown w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_nonnegDefinite

/-- The down-up walk of the star is reversible with respect to the star's
level-`(k+1)` distribution. -/
theorem starDownUp_reversible (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Reversible (starPi w n (k + 1) τ hw hsupp hpos hk) (starDownUp w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible'

/-- The star's level-`(k+1)` distribution is stationary for the star's down-up
walk.  For `k + 1 = n` this is the Glauber dynamics of the conditioned system. -/
theorem starDownUp_stationary (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Stationary (starPi w n (k + 1) τ hw hsupp hpos hk) (starDownUp w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible'.stationary

/-- **The down-up walk of the star is positive semidefinite.** -/
theorem starDownUp_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    NonnegDefinite (starPi w n (k + 1) τ hw hsupp hpos hk) (starDownUp w n k τ hw hsupp hk) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).comp_nonnegDefinite'

/-- The Dirichlet form of the star's up-down walk, in the shape in which it
enters the local-to-global induction. -/
theorem starUpDown_dirichlet (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) (f : Finset E → ℝ) :
    dirichlet (starPi w n k τ hw hsupp hpos hk.le) (starUpDown w n k τ hw hsupp hk) f f
      = ip (starPi w n k τ hw hsupp hpos hk.le) f f
        - ip (starPi w n (k + 1) τ hw hsupp hpos hk) ((starDown k).act f) ((starDown k).act f) :=
  (star_up_down_adjoint w n k τ hw hsupp hpos hk).dirichlet_comp f

/-! ## The distribution one level above a face

This is the monograph's `π_{τ,1}`, carried on ground-set *elements* rather than
on faces: from a face `τ` of cardinality `k < n`, the element `e ∉ τ` is drawn
with probability proportional to `mu w (insert e τ)`.  That this is a
distribution is exactly `Levels.sum_insert_mu`.  Only the case `j = 1` is ever
used in the monograph, and only that case is built here. -/

/-- The **one-level-up distribution** `π_{τ,1}` of a face `τ` of cardinality
`k < n`: mass `mu w (insert e τ) / ((n - k) · mu w τ)` at `e ∉ τ`, and `0` at
`e ∈ τ`.

The hypotheses are carried in the data, as they are for `Levels.up`, whose row
at `τ` this distribution is (transported along `e ↦ insert e τ`). -/
noncomputable def linkDist (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) : FinDist E where
  p e := if e ∈ τ then 0 else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ)
  p_nonneg e := by
    split
    · exact le_rfl
    · exact div_nonneg (mu_nonneg hw _) (mul_nonneg (Nat.cast_nonneg _) (mu_nonneg hw τ))
  p_sum := by
    have hD : ((n - τ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm : mu w τ ≠ 0 := hpos.ne'
    have hstep : ∀ e : E,
        (if e ∈ τ then (0 : ℝ) else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ))
          = (if e ∈ τᶜ then mu w (insert e τ) else 0)
              / (((n - τ.card : ℕ) : ℝ) * mu w τ) := by
      intro e
      by_cases h : e ∈ τ
      · rw [if_pos h, if_neg (Finset.notMem_compl.mpr h), zero_div]
      · rw [if_neg h, if_pos (Finset.mem_compl.mpr h)]
    rw [Finset.sum_congr rfl fun e _ => hstep e, ← Finset.sum_div, Finset.sum_ite_mem,
      Finset.univ_inter, sum_insert_mu w n τ.card hsupp rfl, div_self (mul_ne_zero hD hm)]

/-- The defining formula for `linkDist`. -/
theorem linkDist_apply (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) (e : E) :
    linkDist w n τ hw hsupp hpos hk e =
      if e ∈ τ then 0 else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ) := rfl

/-- The one-level-up distribution ignores the elements of `τ` itself. -/
theorem linkDist_of_mem (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) {e : E} (he : e ∈ τ) :
    linkDist w n τ hw hsupp hpos hk e = 0 := by
  rw [linkDist_apply, if_pos he]

/-- Off `τ`, the one-level-up distribution is proportional to `mu w (insert e τ)`. -/
theorem linkDist_of_not_mem (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) {e : E} (he : e ∉ τ) :
    linkDist w n τ hw hsupp hpos hk e
      = mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ) := by
  rw [linkDist_apply, if_neg he]

/-! ### The guarded one-level-up distribution

`linkDist w n τ hw hsupp hpos hk` requires `hpos : 0 < mu w τ` and
`hk : τ.card < n` *in its data*, so there is literally no term at a null face.
That is fine for statements about a single face, but it blocks any statement
that *averages over faces*, even though the null faces carry no `π_k`-mass.
`linkDistOf` removes the obstruction by guarding both hypotheses and falling
back on a point mass.

This is added *beside* `linkDist`, not in place of it: the hypotheses-in-data
form is what `linkDist_mul_localWalk` and `localWalk_reversible` consume, and
those need no `[Nonempty E]` instance. -/

section Guarded

variable [Nonempty E]

/-- The **guarded one-level-up distribution** `π_{τ,1}`: `linkDist` where that is
defined, and a point mass at an arbitrary element of `E` elsewhere.

Unlike `linkDist` this is a total function of the face `τ`, so it can appear
inside a `π_k`-average.  The junk value is invisible to every statement using
it, because a face at which either guard fails has `π_k`-mass `0`.

The `[Nonempty E]` hypothesis is what makes the junk value exist at all — the
type `FinDist E` is empty when `E` is — and `Levels.nonempty_of_weight` shows it
is implied by the standing hypotheses of a complex of positive dimension. -/
noncomputable def linkDistOf (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) : FinDist E where
  p e :=
    if h : 0 < mu w τ ∧ τ.card < n then linkDist w n τ hw hsupp h.1 h.2 e
    else (if e = Classical.arbitrary E then 1 else 0)
  p_nonneg e := by
    by_cases h : 0 < mu w τ ∧ τ.card < n
    · rw [dif_pos h]
      exact (linkDist w n τ hw hsupp h.1 h.2).p_nonneg e
    · rw [dif_neg h]
      split
      · exact zero_le_one
      · exact le_rfl
  p_sum := by
    by_cases h : 0 < mu w τ ∧ τ.card < n
    · simp only [dif_pos h]
      exact (linkDist w n τ hw hsupp h.1 h.2).p_sum
    · simp only [dif_neg h]
      simp

/-- The defining formula for `linkDistOf`. -/
theorem linkDistOf_apply (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) (e : E) :
    linkDistOf w n hw hsupp τ e =
      if h : 0 < mu w τ ∧ τ.card < n then linkDist w n τ hw hsupp h.1 h.2 e
      else (if e = Classical.arbitrary E then 1 else 0) := rfl

/-- **The guard is invisible where `linkDist` is defined.**  At a face of
positive derived weight and cardinality below `n`, the guarded distribution *is*
the monograph's `π_{τ,1}`. -/
theorem linkDistOf_eq_linkDist (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E}
    (hpos : 0 < mu w τ) (hk : τ.card < n) :
    linkDistOf w n hw hsupp τ = linkDist w n τ hw hsupp hpos hk :=
  FinDist.ext fun e => by rw [linkDistOf_apply, dif_pos ⟨hpos, hk⟩]

end Guarded

/-! ## The local walk

The local walk `Q_τ` is the non-backtracking walk one level above `τ`: from
`e ∉ τ` it jumps to `e' ∉ τ ∪ {e}` with probability proportional to
`mu w (τ ∪ {e, e'})`.  Its guard structure mirrors `Levels.up` exactly: the two
degenerate branches (a null face, or an element of `τ`) hold in place, purely so
that the matrix is stochastic on all of `E`. -/

/-- The **local walk** `Q_τ` at a face `τ` with `τ.card + 1 < n`:

`Q_τ(e, e') = mu w (τ ∪ {e, e'}) / ((n - k - 1) · mu w (τ ∪ {e}))`

for `e ∉ τ` with `mu w (insert e τ) > 0` and `e' ∉ τ ∪ {e}`, and `0` for
`e' ∈ τ ∪ {e}` — in particular the diagonal vanishes, which is what
"non-backtracking" means.  The row sum is `Levels.sum_insert_mu` applied to the
face `insert e τ`, of cardinality `k + 1`. -/
noncomputable def localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) : FinChain E where
  P e e' :=
    if e ∉ τ ∧ 0 < mu w (insert e τ) then
      (if e' ∉ insert e τ then
        mu w (insert e' (insert e τ))
          / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
      else 0)
    else (if e' = e then 1 else 0)
  P_nonneg e e' := by
    split
    · split
      · exact div_nonneg (mu_nonneg hw _) (mul_nonneg (Nat.cast_nonneg _) (mu_nonneg hw _))
      · exact le_rfl
    · split
      · exact zero_le_one
      · exact le_rfl
  P_sum e := by
    by_cases h : e ∉ τ ∧ 0 < mu w (insert e τ)
    · simp only [if_pos h]
      have hcard : (insert e τ).card = τ.card + 1 := Finset.card_insert_of_notMem h.1
      have hD : ((n - (τ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm : mu w (insert e τ) ≠ 0 := h.2.ne'
      have hstep : ∀ e' : E,
          (if e' ∉ insert e τ then
              mu w (insert e' (insert e τ))
                / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
            else 0)
            = (if e' ∈ (insert e τ)ᶜ then mu w (insert e' (insert e τ)) else 0)
                / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ)) := by
        intro e'
        by_cases h' : e' ∈ insert e τ
        · rw [if_neg (not_not_intro h'), if_neg (Finset.notMem_compl.mpr h'), zero_div]
        · rw [if_pos h', if_pos (Finset.mem_compl.mpr h')]
      rw [Finset.sum_congr rfl fun e' _ => hstep e', ← Finset.sum_div, Finset.sum_ite_mem,
        Finset.univ_inter, sum_insert_mu w n (τ.card + 1) hsupp hcard,
        div_self (mul_ne_zero hD hm)]
    · simp only [if_neg h]
      simp

/-- The defining formula for `localWalk`. -/
theorem localWalk_apply (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) (e e' : E) :
    localWalk w n τ hw hsupp hk e e' =
      if e ∉ τ ∧ 0 < mu w (insert e τ) then
        (if e' ∉ insert e τ then
          mu w (insert e' (insert e τ))
            / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
        else 0)
      else (if e' = e then 1 else 0) := rfl

/-- **The detailed-balance cell of the local walk.**  For all `e, e'`,

`π_{τ,1}(e) · Q_τ(e, e') = mu w (τ ∪ {e, e'}) / ((n-k)(n-k-1) · mu w τ)`

when `e, e' ∉ τ` are distinct, and `0` otherwise.  Every degenerate branch
collapses: if `e ∈ τ` or `mu w (insert e τ) = 0` then `π_{τ,1}(e) = 0`; if
`e' ∈ insert e τ` — in particular on the diagonal — then `Q_τ(e, e') = 0`; and
if the guard is off because `mu w (insert e τ) = 0`, the numerator on the right
vanishes too, by `Levels.mu_eq_zero_of_subset`.

Reversibility is read off from this by swapping `e` and `e'`. -/
theorem linkDist_mul_localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) (e e' : E) :
    linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk) e * localWalk w n τ hw hsupp hk e e'
      = if e ∉ τ ∧ e' ∉ τ ∧ e ≠ e' then
          mu w (insert e' (insert e τ))
            / (((n - τ.card : ℕ) : ℝ) * ((n - (τ.card + 1) : ℕ) : ℝ) * mu w τ)
        else 0 := by
  have hD1 : ((n - τ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD2 : ((n - (τ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM : mu w τ ≠ 0 := hpos.ne'
  -- the two ways in which the left-hand side degenerates
  have hnull : ¬ (0 < mu w (insert e τ)) →
      linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk) e = 0 := by
    intro hA
    have hA0 : mu w (insert e τ) = 0 := le_antisymm (not_lt.mp hA) (mu_nonneg hw _)
    rw [linkDist_apply]
    split
    · rfl
    · rw [hA0, zero_div]
  by_cases he : e ∈ τ
  · rw [linkDist_apply, if_pos he, zero_mul, if_neg fun h => h.1 he]
  · by_cases he' : e' ∈ τ
    · rw [if_neg fun h => h.2.1 he']
      by_cases hA : 0 < mu w (insert e τ)
      · have hz : localWalk w n τ hw hsupp hk e e' = 0 := by
          rw [localWalk_apply, if_pos ⟨he, hA⟩,
            if_neg (fun hc => hc (Finset.mem_insert_of_mem he'))]
        rw [hz, mul_zero]
      · rw [hnull hA, zero_mul]
    · by_cases hee : e = e'
      · subst hee
        rw [if_neg fun h => h.2.2 rfl]
        by_cases hA : 0 < mu w (insert e τ)
        · have hz : localWalk w n τ hw hsupp hk e e = 0 := by
            rw [localWalk_apply, if_pos ⟨he, hA⟩,
              if_neg (fun hc => hc (Finset.mem_insert_self e τ))]
          rw [hz, mul_zero]
        · rw [hnull hA, zero_mul]
      · rw [if_pos ⟨he, he', hee⟩]
        have hnm : e' ∉ insert e τ :=
          fun hc => (Finset.mem_insert.mp hc).elim (fun h => hee h.symm) he'
        by_cases hA : 0 < mu w (insert e τ)
        · have hA' : mu w (insert e τ) ≠ 0 := hA.ne'
          rw [linkDist_apply, if_neg he, localWalk_apply, if_pos ⟨he, hA⟩, if_pos hnm]
          field_simp
        · have hA0 : mu w (insert e τ) = 0 := le_antisymm (not_lt.mp hA) (mu_nonneg hw _)
          have hX : mu w (insert e' (insert e τ)) = 0 :=
            mu_eq_zero_of_subset hw (Finset.subset_insert e' (insert e τ)) hA0
          rw [hnull hA, zero_mul, hX, zero_div]

/-- **The local walk is reversible with respect to `π_{τ,1}`.**

The detailed-balance cell computed above is symmetric under `e ↔ e'`: the
denominator does not mention `e` or `e'` at all, and the numerator is symmetric
because `insert e' (insert e τ) = insert e (insert e' τ)`. -/
theorem localWalk_reversible (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) :
    Reversible (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
      (localWalk w n τ hw hsupp hk) := by
  intro e e'
  rw [linkDist_mul_localWalk w n τ hw hsupp hpos hk e e',
    linkDist_mul_localWalk w n τ hw hsupp hpos hk e' e]
  by_cases h : e ∉ τ ∧ e' ∉ τ ∧ e ≠ e'
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, Finset.insert_comm]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩]

/-- `π_{τ,1}` is stationary for the local walk. -/
theorem localWalk_stationary (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) :
    Stationary (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
      (localWalk w n τ hw hsupp hk) :=
  (localWalk_reversible w n τ hw hsupp hpos hk).stationary

/-- The local walk is non-backtracking: it never stays where it is, unless the
row is one of the two degenerate ones. -/
theorem localWalk_diag (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) {e : E} (he : e ∉ τ) (hA : 0 < mu w (insert e τ)) :
    localWalk w n τ hw hsupp hk e e = 0 := by
  rw [localWalk_apply, if_pos ⟨he, hA⟩, if_neg (fun hc => hc (Finset.mem_insert_self e τ))]

/-- The star of the empty face changes nothing at the level of derived weights:
`starWeight w ∅ = w`, so no conditioning has taken place.  Recorded here because
it is the base case of the local-to-global induction. -/
theorem mu_starWeight_empty (w : Finset E → ℝ) (ρ : Finset E) :
    mu (starWeight w ∅) ρ = mu w ρ := by
  rw [mu_starWeight, Finset.empty_union]

end Fintype

end Arlib.MarkovChains
