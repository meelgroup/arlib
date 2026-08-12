/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `P^∧∨_{τ,1} = (Q_τ + I)/2`: the local walk is the lazy level-one up-down walk

`Techniques.ImprovedRandomWalk` proves the Improved Random Walk Theorem, but its
local hypothesis is a Poincaré inequality for the **level-one up-down walk of the
link** of a face, `upDown (linkShiftNorm w τ) (n - |τ|) 1`.  That is not the
object the rest of this development ever bounds: `Techniques.LocalWalk.localWalk`
— the monograph's `Q_τ` — is, and it is what
`Techniques.LocalSpectralIndependence.spectralGapAtLeast_pinLocalWalk` produces
out of spectral independence.  This module supplies the missing translation, and
with it the chain

  spectral independence ⟹ `γ(Q_τ) ≥ γ` ⟹ `γ(P^∧∨_{τ,1}) ≥ γ/2` ⟹ Improved Random Walk

closes inside the library.

**The identity.**  The monograph's `rem:local-downup` records
`P^∧∨_{τ,1} = (Q_τ + I)/2`, and that is literally true here: `(Q_τ + I)/2` *is*
`FinChain.lazy` of `Q_τ`, entry by entry, so the calculus of `Techniques.Lazy`
applies and the gap is exactly halved — the halving is an equivalence, not a
one-way loss.  The computation behind it is two lines of counting.  From the
singleton `{e}` the up walk of the link moves to a two-element face `{e, e'}`
with probability proportional to `mu`, and the down walk then discards one of the
two elements uniformly; so the walk holds at `e` with probability exactly `1/2`
whatever the weight is, and otherwise performs one step of the non-backtracking
walk.  Every degenerate branch matches too: when `mu w (insert e τ)` vanishes the
up walk's guard turns its row into the identity row, `Q_τ`'s guard does the same,
and the lazy version of an identity row is that identity row.

**The star/link mismatch does not bite.**  `LocalWalk.starWeight` is the *star* of
`τ`, and `LocalWalk.starPi w n j τ` is not the monograph's `π_{τ,j}` for `j ≥ 2`
(ROADMAP §3.3, `LinkRestriction.starPi_apply_of_subset`).  Nothing here touches
either.  The ambient side of the bridge is the *honest* link
`LinkRestriction.linkShiftNorm`, and the only distribution used is at level one,
where `LinkRestriction.linkShiftPi_one_singleton` audits `π_{τ,1}` against
`LocalWalk.linkDist`.  The two objects being related therefore live on different
state spaces — faces of the link versus ground-set elements — so the bridge is a
`Techniques.Transport` along `e ↦ {e}`, not an equality of matrices.

**Main declarations.**

* `upDown_one_singleton_self`, `upDown_one_singleton_ne`,
  `upDown_one_singleton_of_not_pos` — the level-one up-down walk of an
  *arbitrary* weighted complex, evaluated between singletons.  The first is the
  holding probability `1/2`, and it holds for every weight.
* `mu_linkShiftNorm_singleton_pos_iff` — the guard of the link's up walk at `{e}`
  is the guard of the local walk at `e`.
* **`upDown_linkShiftNorm_eq_lazy_localWalk`** — `rem:local-downup`:
  `P^∧∨_{τ,1}({e}, {e'}) = Q_τ.lazy(e, e')` for *all* `e, e'`, degenerate rows
  included.
* `transport_singleton_linkShiftPi`, `encodes_singleton_lazy_localWalk` — the
  transport data along `e ↦ {e}`.
* **`spectralGapAtLeast_upDown_linkShiftNorm_iff`** — the payoff:
  `γ(P^∧∨_{τ,1}) ≥ γ/2 ↔ γ(Q_τ) ≥ γ`, an equivalence.
* **`levelEnergy_ge_of_localWalk_gap`** and
  **`downUp_top_spectralGapAtLeast_of_localWalk_gap`** —
  `Techniques.ImprovedRandomWalk`'s `lem:improved-technical` and its headline
  theorem, restated with the local hypothesis phrased in terms of `Q_τ`.  Neither
  reproves anything: both are the imported statements with the hypothesis pushed
  through the equivalence above.

**Four general lemmas this file runs on live upstream**, where they belong:
`Levels.upDown_apply` (the composite `upDown` entrywise),
`LinkRestriction.mu_linkShiftNorm_eq_zero_of_not_disjoint` and the two `Finset`
rewrites `LinkRestriction.union_singleton_eq_insert`,
`LinkRestriction.union_pair_eq_insert_insert`, and
`Lazy.lazy_spectralGapAtLeast_iff` (the two-directional form of
`lazy_spectralGapAtLeast`, which is what makes the halving here an equivalence).

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.ImprovedRandomWalk
import Arlib.MarkovChains.Techniques.Lazy
import Arlib.MarkovChains.Techniques.Transport

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## The level-one up-down walk between singletons

Nothing in this section is about links: it is the evaluation of `P^∧∨_1` of an
arbitrary weighted complex at a pair of singleton faces.  The three lemmas cover
the three shapes the definition produces — the diagonal, an off-diagonal entry,
and the degenerate row at a null face. -/

/-- **The level-one up-down walk holds with probability exactly `1/2`.**

From `{e}` the up walk moves to a two-element face containing `e`, and the down
walk then discards one of the two elements uniformly; the discarded element is
the *new* one with probability `1/2`, regardless of the weight.  This is the
`I/2` in `P^∧∨_{τ,1} = (Q_τ + I)/2`, and the reason `Q_τ` — which never holds —
has to be made lazy before the two can be compared.

The proof needs no counting: the summand equals `U_1({e}, η)/2` in every branch,
and the row sum of `U_1` is `1`. -/
theorem upDown_one_singleton_self (v : Finset E → ℝ) (m : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ) (hvs : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (h1m : 1 < m) {e : E} (hpos : 0 < mu v {e}) :
    upDown v m 1 hv hvs h1m {e} {e} = 1 / 2 := by
  have hterm : ∀ η : Finset E,
      up v m 1 hv hvs h1m {e} η * down 1 η ({e} : Finset E)
        = up v m 1 hv hvs h1m {e} η / 2 := by
    intro η
    rw [up_apply, if_pos ⟨Finset.card_singleton e, hpos⟩, down_apply]
    by_cases hc : η.card = 1 + 1
    · rw [if_pos hc]
      by_cases hs : ({e} : Finset E) ⊆ η
      · rw [if_pos ⟨hc, hs⟩, if_pos ⟨Finset.card_singleton e, hs⟩]
        push_cast
        ring
      · have hup : ¬ (η.card = 1 + 1 ∧ ({e} : Finset E) ⊆ η) := fun hcc => hs hcc.2
        have hdn : ¬ (({e} : Finset E).card = 1 ∧ ({e} : Finset E) ⊆ η) := fun hcc => hs hcc.2
        rw [if_neg hup, if_neg hdn, zero_mul, zero_div]
    · have hup : ¬ (η.card = 1 + 1 ∧ ({e} : Finset E) ⊆ η) := fun hcc => hc hcc.1
      rw [if_neg hup, if_neg hc, zero_mul, zero_div]
  calc upDown v m 1 hv hvs h1m {e} {e}
      = ∑ η : Finset E, up v m 1 hv hvs h1m {e} η * down 1 η ({e} : Finset E) :=
        upDown_apply v m 1 hv hvs h1m {e} {e}
    _ = ∑ η : Finset E, up v m 1 hv hvs h1m {e} η / 2 :=
        Finset.sum_congr rfl fun η _ => hterm η
    _ = 1 / 2 := by rw [← Finset.sum_div, (up v m 1 hv hvs h1m).sum_coe {e}]

/-- **The off-diagonal entries of the level-one up-down walk.**  For `e' ≠ e`,

  `P^∧∨_1({e}, {e'}) = mu v {e, e'} / ((m - 1)·mu v {e}) / 2`.

Only one term of the composite survives: the sole two-element face containing
both `e` and `e'` is `{e, e'}`, and the down step keeps `e'` with probability
`1/2`.  The factor multiplying that `1/2` is exactly one step of the
non-backtracking walk. -/
theorem upDown_one_singleton_ne (v : Finset E → ℝ) (m : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ) (hvs : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (h1m : 1 < m) {e e' : E} (hpos : 0 < mu v {e}) (hne : e' ≠ e) :
    upDown v m 1 hv hvs h1m {e} {e'}
      = mu v (insert e' {e}) / (((m - 1 : ℕ) : ℝ) * mu v {e}) / 2 := by
  have hne' : e' ∉ ({e} : Finset E) := by
    rw [Finset.mem_singleton]
    exact hne
  have hcardρ : (insert e' ({e} : Finset E)).card = 1 + 1 := by
    rw [Finset.card_insert_of_notMem hne', Finset.card_singleton]
  have hesub : ({e} : Finset E) ⊆ insert e' {e} := Finset.subset_insert e' {e}
  have he'sub : ({e'} : Finset E) ⊆ insert e' {e} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e' {e})
  have hterm : ∀ η : Finset E,
      up v m 1 hv hvs h1m {e} η * down 1 η ({e'} : Finset E)
        = if η = insert e' {e} then
            mu v (insert e' {e}) / (((m - 1 : ℕ) : ℝ) * mu v {e}) / 2 else 0 := by
    intro η
    rw [up_apply, if_pos ⟨Finset.card_singleton e, hpos⟩, down_apply]
    by_cases hη : η = insert e' ({e} : Finset E)
    · subst hη
      rw [if_pos hcardρ, if_pos ⟨hcardρ, hesub⟩,
        if_pos ⟨Finset.card_singleton e', he'sub⟩, if_pos rfl]
      push_cast
      ring
    · rw [if_neg hη]
      by_cases hc : η.card = 1 + 1
      · rw [if_pos hc]
        by_cases hs : ({e} : Finset E) ⊆ η
        · by_cases hs' : ({e'} : Finset E) ⊆ η
          · exfalso
            have hsub : insert e' ({e} : Finset E) ⊆ η :=
              Finset.insert_subset_iff.mpr ⟨Finset.singleton_subset_iff.mp hs', hs⟩
            exact hη
              (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hc, hcardρ]))).symm
          · have hdn : ¬ (({e'} : Finset E).card = 1 ∧ ({e'} : Finset E) ⊆ η) :=
              fun hcc => hs' hcc.2
            rw [if_neg hdn, mul_zero]
        · have hup : ¬ (η.card = 1 + 1 ∧ ({e} : Finset E) ⊆ η) := fun hcc => hs hcc.2
          rw [if_neg hup, zero_mul]
      · have hup : ¬ (η.card = 1 + 1 ∧ ({e} : Finset E) ⊆ η) := fun hcc => hc hcc.1
        rw [if_neg hup, if_neg hc, zero_mul]
  calc upDown v m 1 hv hvs h1m {e} {e'}
      = ∑ η : Finset E, up v m 1 hv hvs h1m {e} η * down 1 η ({e'} : Finset E) :=
        upDown_apply v m 1 hv hvs h1m {e} {e'}
    _ = ∑ η : Finset E, if η = insert e' ({e} : Finset E) then
          mu v (insert e' {e}) / (((m - 1 : ℕ) : ℝ) * mu v {e}) / 2 else 0 :=
        Finset.sum_congr rfl fun η _ => hterm η
    _ = mu v (insert e' {e}) / (((m - 1 : ℕ) : ℝ) * mu v {e}) / 2 := by simp

/-- **The degenerate row.**  At a null singleton the up walk's guard is off, so
its row is the identity row; composing with the down walk — whose row at a face
of the wrong size is also the identity row — leaves the identity row.

This is the branch that makes `rem:local-downup` a statement about *all* rows,
and not only about the rows the level-one distribution charges. -/
theorem upDown_one_singleton_of_not_pos (v : Finset E → ℝ) (m : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ) (hvs : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (h1m : 1 < m) {e : E} (hzero : ¬ 0 < mu v {e}) (e' : E) :
    upDown v m 1 hv hvs h1m {e} {e'} = if e' = e then 1 else 0 := by
  have hguard : ¬ (({e} : Finset E).card = 1 ∧ 0 < mu v {e}) := fun hcc => hzero hcc.2
  have hcard : ¬ (({e} : Finset E).card = 1 + 1) := by
    rw [Finset.card_singleton]
    omega
  have hterm : ∀ η : Finset E,
      up v m 1 hv hvs h1m {e} η * down 1 η ({e'} : Finset E)
        = if η = {e} then (if e' = e then (1 : ℝ) else 0) else 0 := by
    intro η
    rw [up_apply, if_neg hguard]
    by_cases hη : η = ({e} : Finset E)
    · subst hη
      rw [if_pos rfl, if_pos rfl, one_mul, down_apply, if_neg hcard]
      by_cases h : e' = e
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg fun hc => h (Finset.singleton_injective hc), if_neg h]
    · rw [if_neg hη, if_neg hη, zero_mul]
  calc upDown v m 1 hv hvs h1m {e} {e'}
      = ∑ η : Finset E, up v m 1 hv hvs h1m {e} η * down 1 η ({e'} : Finset E) :=
        upDown_apply v m 1 hv hvs h1m {e} {e'}
    _ = ∑ η : Finset E, if η = ({e} : Finset E) then (if e' = e then (1 : ℝ) else 0) else 0 :=
        Finset.sum_congr rfl fun η _ => hterm η
    _ = if e' = e then 1 else 0 := by simp

/-! ## The derived weights of the honest link at small faces

The bridge is the previous section read through
`mu (linkShiftNorm w τ) ρ = mu w (τ ∪ ρ) / mu w τ`.  Two instances are needed,
`ρ = {e}` and `ρ = {e, e'}`, together with the observation that a face meeting
`τ` is null in the link — which is what makes the guard of the link's up walk
agree with the guard of the local walk. -/

/-- The derived weight of the link at a singleton disjoint from `τ`: the
conditional weight `mu w (insert e τ) / mu w τ`. -/
theorem mu_linkShiftNorm_singleton (w : Finset E → ℝ) {τ : Finset E} {e : E} (he : e ∉ τ) :
    mu (linkShiftNorm w τ) {e} = mu w (insert e τ) / mu w τ := by
  rw [mu_linkShiftNorm w (Finset.disjoint_singleton_right.mpr he), union_singleton_eq_insert]

/-- The derived weight of the link at a two-element face disjoint from `τ`. -/
theorem mu_linkShiftNorm_pair (w : Finset E → ℝ) {τ : Finset E} {e e' : E}
    (he : e ∉ τ) (he' : e' ∉ τ) :
    mu (linkShiftNorm w τ) (insert e' {e}) = mu w (insert e' (insert e τ)) / mu w τ := by
  have hd : Disjoint τ (insert e' ({e} : Finset E)) := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨he', he⟩
  rw [mu_linkShiftNorm w hd, union_pair_eq_insert_insert]

/-- **The guard of the link's up walk is the guard of the local walk.**  The
level-one face `{e}` is non-null in the link of `τ` exactly when `e ∉ τ` and
`mu w (insert e τ) > 0`, which is precisely the condition
`LocalWalk.localWalk` tests before it moves at all.

This is why the identity `P^∧∨_{τ,1} = (Q_τ + I)/2` needs no support hypothesis:
the two chains degenerate on exactly the same rows. -/
theorem mu_linkShiftNorm_singleton_pos_iff (w : Finset E → ℝ) {τ : Finset E}
    (hpos : 0 < mu w τ) (e : E) :
    0 < mu (linkShiftNorm w τ) {e} ↔ (e ∉ τ ∧ 0 < mu w (insert e τ)) := by
  constructor
  · intro h
    have he : e ∉ τ := by
      intro hc
      exact h.ne' (mu_linkShiftNorm_eq_zero_of_not_disjoint w
        (fun hd => (Finset.disjoint_singleton_right.mp hd) hc))
    refine ⟨he, ?_⟩
    rw [mu_linkShiftNorm_singleton w he] at h
    rcases div_pos_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hpos.le)
  · rintro ⟨he, hpe⟩
    rw [mu_linkShiftNorm_singleton w he]
    exact div_pos hpe hpos

/-! ## `rem:local-downup`

The identity itself.  It is stated between *all* pairs of ground-set elements,
including the pairs at which both sides degenerate, because that is what
`Techniques.Transport` consumes and because the degenerate rows are the only part
of the statement that is not in the monograph. -/

/-- **`rem:local-downup`: `P^∧∨_{τ,1} = (Q_τ + I)/2`.**  For every pair of
ground-set elements,

  **`P^∧∨_{τ,1}({e}, {e'}) = Q_τ.lazy(e, e')`,**

where `P^∧∨_{τ,1}` is the level-one up-down walk of the *honest* link
`LinkRestriction.linkShiftNorm w τ` (a complex of dimension `n - |τ|`) and
`Q_τ` is `LocalWalk.localWalk`.

There are four cases and they line up exactly.  On the diagonal both sides are
`1/2` — the up-down walk because the down step discards the new element half the
time (`upDown_one_singleton_self`), the lazy walk because `Q_τ` is
non-backtracking (`localWalk_diag`).  Off the diagonal, at `e' ∉ τ`, both sides
are `mu w (τ ∪ {e, e'}) / ((n - |τ| - 1)·mu w (τ ∪ {e}))` halved; the ambient
normalisations `mu w τ` cancel, and `n - |τ| - 1 = n - (|τ| + 1)`.  At `e' ∈ τ`
both sides vanish, the link because `{e, e'}` meets `τ` and `Q_τ` because it
refuses to step into `τ`.  And on a degenerate row — `e ∈ τ`, or
`mu w (insert e τ) = 0` — both chains are the identity there, and the lazy
version of an identity row is that identity row.

The two chains live on different state spaces, so this is an identity between
*entries*, not between kernels; `transport_singleton_linkShiftPi` and
`encodes_singleton_lazy_localWalk` turn it into a statement about the `L²`
theory. -/
theorem upDown_linkShiftNorm_eq_lazy_localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) (hτn : τ.card ≤ n) (h1m : 1 < n - τ.card)
    (e e' : E) :
    upDown (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp hτn) h1m {e} {e'}
      = (localWalk w n τ hw hsupp hk).lazy e e' := by
  have hDcast : ((n - τ.card - 1 : ℕ) : ℝ) = ((n - (τ.card + 1) : ℕ) : ℝ) := by
    rw [Nat.sub_sub]
  by_cases hg : 0 < mu (linkShiftNorm w τ) {e}
  · obtain ⟨he, hpe⟩ := (mu_linkShiftNorm_singleton_pos_iff w hpos e).mp hg
    rcases eq_or_ne e' e with rfl | hne
    · rw [upDown_one_singleton_self (linkShiftNorm w τ) (n - τ.card)
        (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp hτn) h1m hg,
        FinChain.lazy_apply, if_pos rfl, localWalk_diag w n τ hw hsupp hk he hpe]
      norm_num
    · rw [upDown_one_singleton_ne (linkShiftNorm w τ) (n - τ.card)
        (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp hτn) h1m hg hne,
        FinChain.lazy_apply, if_neg hne.symm, mu_linkShiftNorm_singleton w he, hDcast]
      by_cases he' : e' ∈ τ
      · have hzero : mu (linkShiftNorm w τ) (insert e' {e}) = 0 := by
          refine mu_linkShiftNorm_eq_zero_of_not_disjoint w ?_
          rw [Finset.disjoint_insert_right]
          exact fun hc => hc.1 he'
        have hQ : localWalk w n τ hw hsupp hk e e' = 0 := by
          rw [localWalk_apply, if_pos ⟨he, hpe⟩,
            if_neg (fun hc => hc (Finset.mem_insert_of_mem he'))]
        rw [hzero, hQ]
        norm_num
      · have hnotmem : e' ∉ insert e τ := by
          rw [Finset.mem_insert]
          exact fun hc => hc.elim hne he'
        have hQ : localWalk w n τ hw hsupp hk e e'
            = mu w (insert e' (insert e τ))
              / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ)) := by
          rw [localWalk_apply, if_pos ⟨he, hpe⟩, if_pos hnotmem]
        have hM : mu w τ ≠ 0 := hpos.ne'
        have hB : mu w (insert e τ) ≠ 0 := hpe.ne'
        have hDne : ((n - (τ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [mu_linkShiftNorm_pair w he he', hQ]
        field_simp
        ring
  · have hoff : ¬ (e ∉ τ ∧ 0 < mu w (insert e τ)) := fun hc =>
      hg ((mu_linkShiftNorm_singleton_pos_iff w hpos e).mpr hc)
    rw [upDown_one_singleton_of_not_pos (linkShiftNorm w τ) (n - τ.card)
      (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp hτn) h1m hg e',
      FinChain.lazy_apply, localWalk_apply, if_neg hoff]
    by_cases h : e' = e
    · subst h
      norm_num
    · rw [if_neg h, if_neg (show ¬ (e = e') from fun hc => h hc.symm)]
      norm_num

/-! ## Transport along `e ↦ {e}`

`Q_τ` lives on the ground set and `P^∧∨_{τ,1}` on the faces of the link, so the
identity above is turned into a statement about variances and Dirichlet forms by
`Techniques.Transport`, whose hypotheses are exactly the two lemmas below. -/

/-- **The level-one distribution of the link transports `π_{τ,1}`.**  The map
`e ↦ {e}` is injective and carries `LocalWalk.linkDist` to
`LinkRestriction.linkShiftPi w n 1 τ`: on `e ∉ τ` this is
`linkShiftPi_one_singleton`, and on `e ∈ τ` both sides are `0`.

`Techniques.Transport` needs nothing more — that `π_{τ,1}` vanishes off the
singletons is a *theorem* there, not a hypothesis. -/
theorem transport_singleton_linkShiftPi (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) (hτn : τ.card ≤ n) (hj : 1 ≤ n - τ.card) :
    Transport (fun e : E => ({e} : Finset E)) (linkDist w n τ hw hsupp hpos hk)
      (linkShiftPi w n 1 τ hw hsupp hτn hpos hj) where
  inj := Finset.singleton_injective
  dist_apply x := by
    by_cases hx : x ∈ τ
    · rw [linkShiftPi_eq_zero_of_not_disjoint w n 1 τ hw hsupp hτn hpos hj
        (fun hd => (Finset.disjoint_singleton_right.mp hd) hx),
        linkDist_of_mem w n τ hw hsupp hpos hk hx]
    · exact linkShiftPi_one_singleton w n τ hw hsupp hpos hk hx

/-- **The link's up-down walk encodes the lazy local walk.**  Immediate from
`upDown_linkShiftNorm_eq_lazy_localWalk`, which holds on every row and so does
not need the almost-everywhere slack that `Encodes` allows. -/
theorem encodes_singleton_lazy_localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) (hτn : τ.card ≤ n) (h1m : 1 < n - τ.card) :
    Encodes (fun e : E => ({e} : Finset E))
      (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
      (upDown (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp hτn) h1m)
      (localWalk w n τ hw hsupp hk).lazy :=
  fun x _ x' => upDown_linkShiftNorm_eq_lazy_localWalk w n τ hw hsupp hpos hk hτn h1m x x'

/-! ## The payoff

The shape `Techniques.ImprovedRandomWalk` asks for, and the shape the rest of the
development produces, are the same hypothesis. -/

/-- **The bridge, as an equivalence of Poincaré inequalities:**

  **`γ(P^∧∨_{τ,1}) ≥ γ/2  ↔  γ(Q_τ) ≥ γ`.**

The left-hand side is the local hypothesis of
`ImprovedRandomWalk.levelEnergy_ge_of_upDown_gap` and
`ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap`; the right-hand
side is the monograph's `γ_k = min_τ γ(Q_τ)` and the conclusion of
`LocalSpectralIndependence.spectralGapAtLeast_pinLocalWalk`.

Both halves are exact: `Transport.spectralGapAtLeast_iff` loses nothing because
`e ↦ {e}` carries all of `π_{τ,1}`, and `lazy_spectralGapAtLeast_iff` loses
nothing because laziness halves the Dirichlet form identically.  So the factor
`1/2` here is not slack — it is the whole content of `rem:local-downup`. -/
theorem spectralGapAtLeast_upDown_linkShiftNorm_iff (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) (hτn : τ.card ≤ n) (hj : 1 ≤ n - τ.card)
    (h1m : 1 < n - τ.card) (γ : ℝ) :
    SpectralGapAtLeast (linkShiftPi w n 1 τ hw hsupp hτn hpos hj)
        (upDown (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp hτn) h1m) (γ / 2)
      ↔ SpectralGapAtLeast (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
          (localWalk w n τ hw hsupp hk) γ := by
  rw [(transport_singleton_linkShiftPi w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk) hτn
      hj).spectralGapAtLeast_iff
      (encodes_singleton_lazy_localWalk w n τ hw hsupp hpos hk hτn h1m) (γ / 2)]
  exact lazy_spectralGapAtLeast_iff

/-! ## `lem:improved-technical` and the Improved Random Walk Theorem, in terms of `Q_τ`

Neither statement below reproves anything from
`Techniques.ImprovedRandomWalk`: each is the imported theorem with its local
hypothesis pushed through `spectralGapAtLeast_upDown_linkShiftNorm_iff`.

Only the *up-down* forms are restated.  The down-up forms
(`levelEnergy_ge_of_downUp_gap`, `downUp_top_spectralGapAtLeast`) are the
primitives, and the route from `γ(Q_τ)` to them runs through the up-down form by
`lem:updown-downup`; so a `Q_τ`-phrased down-up statement would be word for word
the statement below, side condition included.  That side condition, `γ ≤ 2`, is
inherited from `Techniques.UpDownDownUp` and is not an artefact — but it is
harmless for a genuine local walk, whose Poincaré constant is at most `1`. -/

/-- **`lem:improved-technical` with the local hypothesis on `Q_τ`.**  If every
face `τ` of size `k` and positive derived weight has `γ(Q_τ) ≥ γ`, then for every
`f` on the top level

  **`(2γ - 1)·ℰ_{P^∨∧_k}(f^{(k+1)}) ≤ ℰ_{P^∨∧_{k+1}}(f^{(k+2)})`.**

This is `ImprovedRandomWalk.levelEnergy_ge_of_upDown_gap` composed with
`spectralGapAtLeast_upDown_linkShiftNorm_iff`; it is the first form of
`lem:improved-technical` in this development whose hypothesis mentions an object
the monograph actually bounds. -/
theorem levelEnergy_ge_of_localWalk_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkDist w n τ hw hsupp hpos (by omega))
        (localWalk w n τ hw hsupp (by omega)) γ)
    (f : Finset E → ℝ) :
    (2 * γ - 1) * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  refine levelEnergy_ge_of_upDown_gap w n k hw hsupp hsum hγ hγ2 hk2 ?_ f
  intro τ hcard hpos
  exact (spectralGapAtLeast_upDown_linkShiftNorm_iff w n τ hw hsupp hpos (by omega)
    (by omega) (by omega) (by omega) γ).mpr (hgap τ hcard hpos)

/-- **The Improved Random Walk Theorem with the local hypothesis on `Q_τ`.**  For
a weighted complex of dimension `m + 1` all of whose local walks satisfy
`γ(Q_τ) ≥ γ_j` at level `j`,

  **`γ(P^∨∧_{m+1}) ≥ Γ_m / ∑_{i≤m} Γ_i`,  `Γ_i = ∏_{j<i}(2γ_j - 1)`.**

This is `ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap` with the
hypothesis translated by `spectralGapAtLeast_upDown_linkShiftNorm_iff`.  It is
the statement `thm:impr-RW-thm` of the monograph: its `γ_i` is
`min_{τ ∈ Pinning_i} γ(Q_τ)`, which is exactly what `hgap` asserts here, face by
face rather than as a minimum.

The three hypotheses on `γ` are the ones the underlying theorem needs.  `hγ`
(`γ_j ≥ 1/2`) is the regime in which the improved bound says anything and is not
stated in the monograph; `hγ2` (`γ_j ≤ 2`) comes from `lem:updown-downup` and is
weaker than the `γ_j ≤ 1` that any local walk satisfies. -/
theorem downUp_top_spectralGapAtLeast_of_localWalk_gap (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkDist w (m + 1) τ hw hsupp hpos (by omega))
        (localWalk w (m + 1) τ hw hsupp (by omega)) (γ j)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (improvedFactor γ m / ∑ i ∈ Finset.range (m + 1), improvedFactor γ i) := by
  refine downUp_top_spectralGapAtLeast_of_upDown_gap w m hw hsupp hsum γ hγ hγ2 ?_
  intro j hj τ hcard hpos
  exact (spectralGapAtLeast_upDown_linkShiftNorm_iff w (m + 1) τ hw hsupp hpos (by omega)
    (by omega) (by omega) (by omega) (γ j)).mpr (hgap j hj τ hcard hpos)

end Arlib.MarkovChains

