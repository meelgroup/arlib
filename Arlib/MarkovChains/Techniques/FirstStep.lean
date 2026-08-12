/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `claim:first-step`: the two-level variance drop is an average of link variances

`Techniques.LocalToGlobal` telescopes the top-level variance one level at a time,
and `Techniques.LinkRestriction` builds the honest link `linkShift` of a face
together with its level distributions `linkShiftPi` (`π_{τ,j}`) and the
restriction theorem `levelFun_linkShiftNorm` (`f_τ^{(j)}(ρ) = f^{(|τ|+j)}(τ ∪ ρ)`).
This module proves the identity that joins them, `claim:first-step` of the
monograph ([CSV23, §6.6] — Chen–Štefankovič–Vigoda, *Spectral Independence and
Local-to-Global Techniques for Optimal Mixing of Markov Chains*,
arXiv:2307.13826, 2023):

  **`Var_{π_{k+1}}(f^{(k+1)}) − Var_{π_{k−1}}(f^{(k−1)})
      = ∑_{τ ∈ 𝒫_{k−1}} π_{k−1}(τ) · Var_{π_{τ,2}}(f_τ^{(2)})`.**

It is the last ingredient of `lem:improved-technical` that does not depend on
`lem:updown-downup`.  With `Techniques.LinkRestriction.levelVar_sub_levelVar_eq_add`
rewriting the left-hand side as `ℰ_{P^{∨∧}_{k}}(f^{(k+1)}) + ℰ_{P^{∨∧}_{k−1}}(f^{(k)})`,
the corollary `Ex_Var_linkShiftPiOf_eq_levelEnergy_add` below is exactly the
first display of the monograph's proof of `lem:improved-technical`.

Indices here are shifted so that `k` names the level of the face `τ` that is
averaged over: the monograph's `k − 1` is our `k`, and the three levels involved
are `k`, `k + 1`, `k + 2`.

**Two obstructions, and how they are resolved.**

*The averaging is over faces at which the local objects are undefined.*
`linkShiftPi` carries `0 < mu w τ` and `τ.card + j ≤ n` in its data, so at a null
face there is no term at all and `𝔼_{τ ∼ π_k}[Var_{π_{τ,2}}(…)]` does not even
typecheck.  `LinkRestriction.linkShiftPiOf` and `LinkRestriction.linkLevelFun`
are the guarded-total variants, in the style of `LocalWalk.linkDistOf`: total in
`τ`, junk off the good set, with agreement lemmas.  Note that — unlike
`linkDistOf` — **no `[Nonempty …]` hypothesis is needed**, because the state
space here is `Finset E`, which has the point `∅` whatever `E` is.

*The identity is a two-step marginal computation.*  The monograph's `eqn:step111`
and `eqn:step222` are both instances of one pointwise statement,
`Ex_linkShiftPi_two_eq_act_up_act_up`: averaging over `π_{τ,2}` **is** applying
the up operator twice,

  `𝔼_{ρ ∼ π_{τ,2}}[G (τ ∪ ρ)] = (U_k (U_{k+1} G))(τ)`,

after which the average over `π_k` collapses by `Adjoint.push_left` alone.  Both
sides are `(∑_{σ ⊇ τ, |σ| = k+2} mu w σ · G σ)` divided by a normalising factor,
and the two factors agree by `Nat.choose_succ_right_eq`: the binomial
`(n−k).choose 2` on the link side against the ordered count `(n−k)(n−k−1)` on the
two-step side.  That factor of two is the combinatorial content of the claim, and
`sum_ite_card_between` is where it comes from — a level-`(k+1)` face between `τ`
and `σ` is the omission of one of the two elements of `σ ∖ τ`.

Main declarations:

* `sum_ite_card_between` — the counting lemma: there are exactly `|σ| − |τ|`
  faces strictly between `τ` and `σ` one level up.  Its companion
  `LinkRestriction.sum_ite_disjoint_union`, and the guarded-total `π_{τ,j}` and
  `f_τ^{(j)}` (`linkShiftPiOf`, `linkLevelFun`) that every statement below is
  phrased with, live in `Techniques.LinkRestriction`.
* `Ex_linkShiftPi_eq_div`, `act_up_act_up_eq_div` — the two closed forms.
* **`Ex_linkShiftPi_two_eq_act_up_act_up`** — averaging over `π_{τ,2}` is two
  applications of the up operator.
* `Ex_pi_Ex_linkShiftPiOf_eq` — the monograph's `eqn:step222`: the `π_k`-average
  of the `π_{τ,2}`-averages is the `π_{k+2}`-average.
* `Ex_linkShiftPi_levelFun_eq` — the monograph's `eqn:step111`:
  `f^{(k)}(τ) = 𝔼_{ρ ∼ π_{τ,2}}[f^{(k+2)}(τ ∪ ρ)]`.
* **`Ex_Var_linkShiftPiOf_eq_levelVar_sub`** — `claim:first-step`.
* **`Ex_Var_linkShiftPiOf_eq_levelEnergy_add`** — the same with the left-hand
  side expanded into the two level energies, which is the form
  `lem:improved-technical` consumes.
* `Ex_linkShiftPi_one_eq_Ex_linkDist`,
  `Var_linkShiftPi_one_eq_Var_linkDist` and
  **`Ex_pi_Var_linkShiftPiOf_one_eq_levelEnergy`** — the companion identity
  `claim:DDD` at level one, transported from `LocalWalk.linkDist` (a distribution
  on elements) to `π_{τ,1}` (a distribution on faces), so that the two averaged
  identities `lem:improved-technical` compares are averages of the *same* shape,
  `Var (linkShiftPiOf … j τ …) (linkLevelFun … j τ …)` at `j = 1` and `j = 2`.

What is **not** here is `lem:improved-technical` itself: the inequality between
the two averages is the per-face bound `Var_{π_{τ,2}} ≥ 2γ_{k−1} Var_{π_{τ,1}}`,
which the monograph derives from `lem:updown-downup` — a statement this
development does not yet have.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LinkRestriction

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A counting lemma

The same argument as `Levels.sum_insert_mu`: an indicator sum over a family of
faces, reindexed by an explicit bijection and evaluated by `Finset.card_sdiff`.
It mentions no weight.  Its companion, the reindexing
`LinkRestriction.sum_ite_disjoint_union`, is stated beside `mu_linkShift`, which
performs the same reindexing. -/

/-- **The faces one level above `τ` and below `σ`.**  For `|τ| = k`, the number
of `η` with `τ ⊆ η ⊆ σ` and `|η| = k + 1` is `|σ| − k` when `τ ⊆ σ`, and `0`
otherwise: such an `η` is `insert e τ` for one of the `|σ ∖ τ|` elements
`e ∈ σ ∖ τ`.

At `|σ| = k + 2` — the only case used below — the count is `2`, and that is
exactly the factor by which the two-step up operator and the level-`2` link
distribution differ before normalisation. -/
theorem sum_ite_card_between {k : ℕ} {τ : Finset E} (hτ : τ.card = k) (σ : Finset E)
    (c : ℝ) :
    ∑ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η ∧ η ⊆ σ then c else 0)
      = if τ ⊆ σ then ((σ.card - k : ℕ) : ℝ) * c else 0 := by
  have hstep : ∀ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η ∧ η ⊆ σ then c else 0)
      = (if η.card = k + 1 ∧ τ ⊆ η then (if η ⊆ σ then c else 0) else 0) := by
    intro η
    by_cases h1 : η.card = k + 1 ∧ τ ⊆ η
    · rw [if_pos h1]
      by_cases h2 : η ⊆ σ
      · rw [if_pos h2, if_pos ⟨h1.1, h1.2, h2⟩]
      · rw [if_neg h2, if_neg fun hc => h2 hc.2.2]
    · rw [if_neg h1, if_neg fun hc => h1 ⟨hc.1, hc.2.1⟩]
  rw [Finset.sum_congr rfl fun η _ => hstep η,
    sum_ite_insert hτ (fun η => if η ⊆ σ then c else 0)]
  by_cases hts : τ ⊆ σ
  · rw [if_pos hts]
    have hcond : ∑ e ∈ τᶜ, (if insert e τ ⊆ σ then c else 0)
        = ∑ e ∈ τᶜ, (if e ∈ σ then c else 0) :=
      Finset.sum_congr rfl fun e _ =>
        if_congr (by rw [Finset.insert_subset_iff]; exact and_iff_left hts) rfl rfl
    have hint : τᶜ ∩ σ = σ \ τ := by
      rw [Finset.inter_comm, Finset.sdiff_eq_inter_compl]
    rw [hcond, Finset.sum_ite_mem, hint, Finset.sum_const, Finset.card_sdiff_of_subset hts, hτ,
      nsmul_eq_mul]
  · rw [if_neg hts]
    refine Finset.sum_eq_zero fun e _ => if_neg fun hc => hts ?_
    exact (Finset.subset_insert e τ).trans hc

/-! ## Two closed forms, and the bridge between them

Both the level-`j` link average and the `j`-fold application of the up operator
are `(∑_{σ ⊇ τ, |σ| = |τ| + j} mu w σ · G σ)` divided by a normalising factor.
Writing both out and comparing the factors is the whole proof of
`claim:first-step`; at `j = 2` the factors are `mu w τ · (n−|τ|).choose 2` and
`(n−|τ|)(n−|τ|−1) · mu w τ / 2`. -/

/-- **The level-`j` link average in closed form.**

  `𝔼_{ρ ∼ π_{τ,j}}[G (τ ∪ ρ)]
      = (∑_{σ ⊇ τ, |σ| = |τ| + j} mu w σ · G σ) / (mu w τ · (n − |τ|).choose j)`.

Immediate from `LinkRestriction.linkShiftPi_apply_of_disjoint` and the
reindexing `sum_ite_disjoint_union`; the faces of the link that meet `τ` and the
faces of the wrong size contribute nothing. -/
theorem Ex_linkShiftPi_eq_div (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) (G : Finset E → ℝ) :
    Ex (linkShiftPi w n j τ hw hsupp hτn hpos hj) (fun ρ => G (τ ∪ ρ))
      = (∑ σ : Finset E, if σ.card = τ.card + j ∧ τ ⊆ σ then mu w σ * G σ else 0)
          / (mu w τ * (((n - τ.card).choose j : ℕ) : ℝ)) := by
  rw [← sum_ite_disjoint_union τ j (fun σ => mu w σ * G σ), Finset.sum_div]
  simp only [Ex_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  by_cases hc : ρ.card = j
  · by_cases hd : Disjoint τ ρ
    · rw [linkShiftPi_apply_of_disjoint w n j τ hw hsupp hτn hpos hj hd, if_pos hc,
        if_pos ⟨hc, hd⟩, div_mul_eq_mul_div]
    · rw [linkShiftPi_eq_zero_of_not_disjoint w n j τ hw hsupp hτn hpos hj hd,
        if_neg fun hcon => hd hcon.2, zero_mul, zero_div]
  · rw [linkShiftPi_eq_zero_of_card_ne w n j τ hw hsupp hτn hpos hj hc,
      if_neg fun hcon => hc hcon.1, zero_mul, zero_div]

/-- The swap of the two sums in the two-step up operator, with the count of the
intermediate faces performed by `sum_ite_card_between`.  The factor `2` is the
number of level-`(k+1)` faces between a level-`k` face `τ` and a level-`(k+2)`
face `σ ⊇ τ`. -/
theorem sum_sum_ite_two {k : ℕ} {τ : Finset E} (hcard : τ.card = k) (c : Finset E → ℝ) :
    ∑ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η then
        (∑ σ : Finset E, if σ.card = k + 2 ∧ η ⊆ σ then c σ else 0) else 0)
      = 2 * ∑ σ : Finset E, (if σ.card = k + 2 ∧ τ ⊆ σ then c σ else 0) := by
  have h1 : ∀ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η then
        (∑ σ : Finset E, if σ.card = k + 2 ∧ η ⊆ σ then c σ else 0) else 0)
      = ∑ σ : Finset E,
          (if η.card = k + 1 ∧ τ ⊆ η ∧ σ.card = k + 2 ∧ η ⊆ σ then c σ else 0) := by
    intro η
    by_cases h : η.card = k + 1 ∧ τ ⊆ η
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h2 : σ.card = k + 2 ∧ η ⊆ σ
      · rw [if_pos h2, if_pos ⟨h.1, h.2, h2.1, h2.2⟩]
      · rw [if_neg h2, if_neg fun hc => h2 ⟨hc.2.2.1, hc.2.2.2⟩]
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun σ _ => if_neg fun hc => h ⟨hc.1, hc.2.1⟩).symm
  rw [Finset.sum_congr rfl fun η _ => h1 η, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ.card = k + 2
  · have h2 : ∀ η : Finset E,
        (if η.card = k + 1 ∧ τ ⊆ η ∧ σ.card = k + 2 ∧ η ⊆ σ then c σ else 0)
        = (if η.card = k + 1 ∧ τ ⊆ η ∧ η ⊆ σ then c σ else 0) := by
      intro η
      refine if_congr ?_ rfl rfl
      constructor
      · rintro ⟨ha, hb, _, hd⟩
        exact ⟨ha, hb, hd⟩
      · rintro ⟨ha, hb, hd⟩
        exact ⟨ha, hb, hσ, hd⟩
    rw [Finset.sum_congr rfl fun η _ => h2 η, sum_ite_card_between hcard σ (c σ)]
    by_cases hts : τ ⊆ σ
    · rw [if_pos hts, if_pos ⟨hσ, hts⟩, hσ]
      have h3 : k + 2 - k = 2 := by omega
      rw [h3]
      norm_num
    · rw [if_neg hts, if_neg fun hc => hts hc.2, mul_zero]
  · rw [if_neg fun hc => hσ hc.1, mul_zero]
    exact Finset.sum_eq_zero fun η _ => if_neg fun hc => hσ hc.2.2.1

/-- **The two-step up operator in closed form.**  For a face `τ` of cardinality
`k` and positive derived weight,

  `(U_k (U_{k+1} G))(τ)
      = 2 · (∑_{σ ⊇ τ, |σ| = k + 2} mu w σ · G σ) / ((n−k)(n−k−1) · mu w τ)`.

The two `mu w η` at the intermediate level cancel — including at the null
intermediate faces, where the numerator vanishes because every face above a null
face is null (`Levels.mu_eq_zero_of_subset`) and the denominator never appears.
The factor `2` is `sum_sum_ite_two`. -/
theorem act_up_act_up_eq_div (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk1 : k < n) (hk2 : k + 1 < n) {τ : Finset E} (hcard : τ.card = k)
    (hpos : 0 < mu w τ) (G : Finset E → ℝ) :
    (up w n k hw hsupp hk1).act ((up w n (k + 1) hw hsupp hk2).act G) τ
      = 2 * (∑ σ : Finset E, if σ.card = k + 2 ∧ τ ⊆ σ then mu w σ * G σ else 0)
          / (((n - k : ℕ) : ℝ) * ((n - (k + 1) : ℕ) : ℝ) * mu w τ) := by
  have hD2 : ((n - (k + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinner : ∀ η : Finset E, η.card = k + 1 →
      mu w η * (up w n (k + 1) hw hsupp hk2).act G η
        = (∑ σ : Finset E, if σ.card = k + 2 ∧ η ⊆ σ then mu w σ * G σ else 0)
            / ((n - (k + 1) : ℕ) : ℝ) := by
    intro η hη
    by_cases hmη : 0 < mu w η
    · rw [FinKernel.act_apply, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [up_apply, if_pos ⟨hη, hmη⟩]
      simp only [show k + 1 + 1 = k + 2 from rfl]
      by_cases hc : σ.card = k + 2 ∧ η ⊆ σ
      · rw [if_pos hc, if_pos hc]
        field_simp
      · rw [if_neg hc, if_neg hc, zero_mul, mul_zero, zero_div]
    · have h0 : mu w η = 0 := le_antisymm (not_lt.mp hmη) (mu_nonneg hw η)
      rw [h0, zero_mul]
      refine (div_eq_zero_iff.mpr (Or.inl ?_)).symm
      refine Finset.sum_eq_zero fun σ _ => ?_
      by_cases hc : σ.card = k + 2 ∧ η ⊆ σ
      · rw [if_pos hc, mu_eq_zero_of_subset hw hc.2 h0, zero_mul]
      · rw [if_neg hc]
  have hterm : ∀ η : Finset E,
      up w n k hw hsupp hk1 τ η * (up w n (k + 1) hw hsupp hk2).act G η
        = (if η.card = k + 1 ∧ τ ⊆ η then
             (∑ σ : Finset E, if σ.card = k + 2 ∧ η ⊆ σ then mu w σ * G σ else 0)
           else 0) / (((n - k : ℕ) : ℝ) * ((n - (k + 1) : ℕ) : ℝ) * mu w τ) := by
    intro η
    rw [up_apply, if_pos ⟨hcard, hpos⟩]
    by_cases hc : η.card = k + 1 ∧ τ ⊆ η
    · have hswap : ((n - (k + 1) : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) * mu w τ)
          = ((n - k : ℕ) : ℝ) * ((n - (k + 1) : ℕ) : ℝ) * mu w τ := by ring
      rw [if_pos hc, if_pos hc, div_mul_eq_mul_div, hinner η hc.1, div_div, hswap]
    · rw [if_neg hc, if_neg hc, zero_mul, zero_div]
  rw [FinKernel.act_apply, Finset.sum_congr rfl fun η _ => hterm η, ← Finset.sum_div,
    sum_sum_ite_two hcard (fun σ => mu w σ * G σ)]

/-- **Averaging over `π_{τ,2}` is applying the up operator twice.**  For a face
`τ` of cardinality `k` and positive derived weight, and every `G` on level
`k + 2`,

  **`𝔼_{ρ ∼ π_{τ,2}}[G (τ ∪ ρ)] = (U_k (U_{k+1} G))(τ)`.**

This is the bridge of the module: it turns a *local* average, taken in the link
of `τ`, into an *ambient* one, after which the outer `π_k`-average collapses by
adjointness alone.  Both the monograph's `eqn:step111` and its `eqn:step222` are
instances.

The two sides are the same sum over the faces `σ ⊇ τ` of size `k + 2` up to a
constant, and the constants agree because `2 · (n−k).choose 2 = (n−k)(n−k−1)`,
which is `Nat.choose_succ_right_eq` at `1`.  Combinatorially: the link counts
each `σ` once, the two-step up operator counts it once for each of the two
intermediate faces. -/
theorem Ex_linkShiftPi_two_eq_act_up_act_up (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk1 : k < n) (hk2 : k + 1 < n) {τ : Finset E} (hcard : τ.card = k)
    (hpos : 0 < mu w τ) (hτn : τ.card ≤ n) (hj : 2 ≤ n - τ.card) (G : Finset E → ℝ) :
    Ex (linkShiftPi w n 2 τ hw hsupp hτn hpos hj) (fun ρ => G (τ ∪ ρ))
      = (up w n k hw hsupp hk1).act ((up w n (k + 1) hw hsupp hk2).act G) τ := by
  have hchoose : 2 * (((n - k).choose 2 : ℕ) : ℝ)
      = ((n - k : ℕ) : ℝ) * ((n - (k + 1) : ℕ) : ℝ) := by
    have hnat : 2 * ((n - k).choose 2) = (n - k) * (n - (k + 1)) := by
      have hm : n - (k + 1) = (n - k) - 1 := by omega
      rw [hm]
      have h := Nat.choose_succ_right_eq (n - k) 1
      rw [Nat.choose_one_right] at h
      rw [← h]
      ring
    exact_mod_cast hnat
  have hC : (((n - k).choose 2 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hmu : mu w τ ≠ 0 := hpos.ne'
  rw [Ex_linkShiftPi_eq_div w n 2 τ hw hsupp hτn hpos hj G,
    act_up_act_up_eq_div w n k hw hsupp hk1 hk2 hcard hpos G, hcard, ← hchoose]
  field_simp

/-! ## The monograph's two identities

`eqn:step111` and `eqn:step222` are now both one line from the bridge: the first
is the bridge at `G = f^{(k+2)}`, where two applications of the up operator are
two steps of the defining recursion for `levelFun`; the second is the bridge
followed by `Adjoint.push_left` twice. -/

/-- **`eqn:step222`.**  The `π_k`-average of the local averages is the
`π_{k+2}`-average:

  `𝔼_{τ ∼ π_k}[𝔼_{ρ ∼ π_{τ,2}}[G (τ ∪ ρ)]] = 𝔼_{π_{k+2}}[G]`.

Once the inner average is recognised as `U_k (U_{k+1} G)`, this is only the fact
that `π_{k+1}` is the pushforward of `π_k` along `U_k`, which is part of
`Levels.up_down_adjoint`.  The guarded distribution is what makes the left-hand
side well formed at the null faces, which contribute nothing. -/
theorem Ex_pi_Ex_linkShiftPiOf_eq (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk1 : k < n) (hk2 : k + 1 < n)
    (hk3 : k + 2 ≤ n) (G : Finset E → ℝ) :
    Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => Ex (linkShiftPiOf w n 2 τ hw hsupp) (fun ρ => G (τ ∪ ρ)))
      = Ex (pi w n (k + 2) hw hsupp hsum hk3) G := by
  have hstep : Ex (pi w n k hw hsupp hsum hk1.le)
      (fun τ => Ex (linkShiftPiOf w n 2 τ hw hsupp) (fun ρ => G (τ ∪ ρ)))
      = Ex (pi w n k hw hsupp hsum hk1.le)
          ((up w n k hw hsupp hk1).act ((up w n (k + 1) hw hsupp hk2).act G)) := by
    refine Ex_congr_ae fun τ hz => ?_
    show Ex (linkShiftPiOf w n 2 τ hw hsupp) (fun ρ => G (τ ∪ ρ))
      = (up w n k hw hsupp hk1).act ((up w n (k + 1) hw hsupp hk2).act G) τ
    have hcard : τ.card = k := by
      by_contra hc
      exact hz (by rw [pi_apply, if_neg hc])
    have hmu : 0 < mu w τ := by
      rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
      · exact h
      · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
    have hτn : τ.card ≤ n := by omega
    have hj : 2 ≤ n - τ.card := by omega
    rw [linkShiftPiOf_eq_linkShiftPi w n 2 τ hw hsupp hτn hmu hj,
      Ex_linkShiftPi_two_eq_act_up_act_up w n k hw hsupp hk1 hk2 hcard hmu hτn hj G]
  rw [hstep, ← Ex_push_eq (up w n k hw hsupp hk1) (pi w n k hw hsupp hsum hk1.le)
      ((up w n (k + 1) hw hsupp hk2).act G),
    (up_down_adjoint w n k hw hsupp hsum hk1).push_left,
    ← Ex_push_eq (up w n (k + 1) hw hsupp hk2) (pi w n (k + 1) hw hsupp hsum hk2.le) G,
    (up_down_adjoint w n (k + 1) hw hsupp hsum hk2).push_left]

/-- **`eqn:step111`.**  For every face `τ` of cardinality `k` and positive
derived weight,

  `f^{(k)}(τ) = 𝔼_{ρ ∼ π_{τ,2}}[f^{(k+2)}(τ ∪ ρ)]`.

The bridge at `G = f^{(k+2)}`, followed by two steps of the defining recursion
`f^{(j)} = U_j f^{(j+1)}`.  In the monograph this is stated with the link
projection `f_τ^{(2)}` on the right, which is the same function on the support of
`π_{τ,2}` by `linkLevelFun_eq_levelFun`. -/
theorem Ex_linkShiftPi_levelFun_eq (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk1 : k < n) (hk2 : k + 1 < n) {τ : Finset E} (hcard : τ.card = k)
    (hpos : 0 < mu w τ) (hτn : τ.card ≤ n) (hj : 2 ≤ n - τ.card) (f : Finset E → ℝ) :
    Ex (linkShiftPi w n 2 τ hw hsupp hτn hpos hj)
        (fun ρ => levelFun w n hw hsupp f (k + 2) (τ ∪ ρ))
      = levelFun w n hw hsupp f k τ := by
  have h2 : levelFun w n hw hsupp f (k + 1)
      = (up w n (k + 1) hw hsupp hk2).act (levelFun w n hw hsupp f (k + 2)) :=
    levelFun_succ w n (k + 1) hw hsupp f hk2
  rw [Ex_linkShiftPi_two_eq_act_up_act_up w n k hw hsupp hk1 hk2 hcard hpos hτn hj
      (levelFun w n hw hsupp f (k + 2)), ← h2,
    ← levelFun_succ w n k hw hsupp f hk1]

/-! ## `claim:first-step`

The local variance at a good face is now computable: expand
`Var_{π_{τ,2}}(f_τ^{(2)})` as a second moment minus a squared mean, replace the
link projection by the ambient one on the support of `π_{τ,2}`, and identify the
mean with `f^{(k)}(τ)` by `eqn:step111`.  Averaging over `π_k` then turns the
second moment into a `π_{k+2}`-second moment by `eqn:step222`, and the two
squared means cancel because projecting preserves the mean. -/

/-- The local variance at a face of positive derived weight, expanded:

  `Var_{π_{τ,2}}(f_τ^{(2)}) = 𝔼_{ρ ∼ π_{τ,2}}[f^{(k+2)}(τ ∪ ρ)²] − f^{(k)}(τ)²`.

The link projection is replaced by the ambient one via `linkLevelFun_eq_levelFun`
(legitimate inside the average by `Var_linkShiftPi_congr`), and the mean is
`eqn:step111`. -/
theorem Var_linkShiftPiOf_linkLevelFun_eq (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk1 : k < n) (hk2 : k + 1 < n) (f : Finset E → ℝ) {τ : Finset E}
    (hcard : τ.card = k) (hpos : 0 < mu w τ) :
    Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f)
      = Ex (linkShiftPiOf w n 2 τ hw hsupp)
          (fun ρ => (levelFun w n hw hsupp f (k + 2) (τ ∪ ρ)) ^ 2)
        - (levelFun w n hw hsupp f k τ) ^ 2 := by
  have hτn : τ.card ≤ n := by omega
  have hj : 2 ≤ n - τ.card := by omega
  have hagree : ∀ ρ : Finset E, ρ.card = 2 → Disjoint τ ρ → 0 < mu w (τ ∪ ρ) →
      linkLevelFun w n 2 τ hw hsupp f ρ = levelFun w n hw hsupp f (k + 2) (τ ∪ ρ) := by
    intro ρ hc hd hm
    rw [linkLevelFun_eq_levelFun w n 2 τ hw hsupp f hτn hd hc hm, hcard]
  rw [linkShiftPiOf_eq_linkShiftPi w n 2 τ hw hsupp hτn hpos hj,
    Var_linkShiftPi_congr w n 2 τ hw hsupp hτn hpos hj hagree,
    Var_eq_ip_sub_sq, ip_self_eq_Ex_sq,
    Ex_linkShiftPi_levelFun_eq w n k hw hsupp hk1 hk2 hcard hpos hτn hj f]

/-- **`claim:first-step`** (§6.6, `eqn:first-step`).  For every `k` with
`k + 1 < n` and every `f` on the top level,

  **`Var_{π_{k+2}}(f^{(k+2)}) − Var_{π_k}(f^{(k)})
      = 𝔼_{τ ∼ π_k}[Var_{π_{τ,2}}(f_τ^{(2)})]`.**

The monograph writes this with `k + 1` and `k − 1` where we write `k + 2` and
`k`; the face averaged over is the one two levels below the top of the three
involved.

Both variances are second moments minus squared means.  The second moments match
by `eqn:step222` (`Ex_pi_Ex_linkShiftPiOf_eq`) after the local variance has been
expanded by `Var_linkShiftPiOf_linkLevelFun_eq`, and the squared means cancel
because `𝔼_{π_{k+2}}[f^{(k+2)}] = 𝔼_{π_k}[f^{(k)}]` — projecting down the levels
is a pushforward and so preserves the mean.  Note that, unlike the monograph, we
need no reduction to mean-zero functions. -/
theorem Ex_Var_linkShiftPiOf_eq_levelVar_sub (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk2 : k + 1 < n) :
    Ex (pi w n k hw hsupp hsum (by omega : k ≤ n))
        (fun τ => Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f))
      = levelVar w n hw hsupp hsum f (k + 2) - levelVar w n hw hsupp hsum f k := by
  have hk1 : k < n := by omega
  have hk3 : k + 2 ≤ n := by omega
  -- expand the integrand at every face carrying `π_k`-mass
  have step1 : Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f))
      = Ex (pi w n k hw hsupp hsum hk1.le)
          (fun τ => Ex (linkShiftPiOf w n 2 τ hw hsupp)
              (fun ρ => (levelFun w n hw hsupp f (k + 2) (τ ∪ ρ)) ^ 2)
            - (levelFun w n hw hsupp f k τ) ^ 2) := by
    refine Ex_congr_ae fun τ hz => ?_
    show Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f)
      = Ex (linkShiftPiOf w n 2 τ hw hsupp)
          (fun ρ => (levelFun w n hw hsupp f (k + 2) (τ ∪ ρ)) ^ 2)
        - (levelFun w n hw hsupp f k τ) ^ 2
    have hcard : τ.card = k := by
      by_contra hc
      exact hz (by rw [pi_apply, if_neg hc])
    have hmu : 0 < mu w τ := by
      rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
      · exact h
      · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
    exact Var_linkShiftPiOf_linkLevelFun_eq w n k hw hsupp hk1 hk2 f hcard hmu
  -- the second moment collapses to a second moment two levels up
  have step2 : Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => Ex (linkShiftPiOf w n 2 τ hw hsupp)
          (fun ρ => (levelFun w n hw hsupp f (k + 2) (τ ∪ ρ)) ^ 2))
      = Ex (pi w n (k + 2) hw hsupp hsum hk3)
          (fun σ => (levelFun w n hw hsupp f (k + 2) σ) ^ 2) :=
    Ex_pi_Ex_linkShiftPiOf_eq w n k hw hsupp hsum hk1 hk2 hk3
      (fun σ => (levelFun w n hw hsupp f (k + 2) σ) ^ 2)
  -- projecting down the levels preserves the mean
  have hmean : Ex (pi w n (k + 2) hw hsupp hsum hk3) (levelFun w n hw hsupp f (k + 2))
      = Ex (pi w n k hw hsupp hsum hk1.le) (levelFun w n hw hsupp f k) := by
    have e1 : Ex (pi w n (k + 1 + 1) hw hsupp hsum hk2) (levelFun w n hw hsupp f (k + 1 + 1))
        = Ex (pi w n (k + 1) hw hsupp hsum hk2.le) (levelFun w n hw hsupp f (k + 1)) := by
      rw [levelFun_succ w n (k + 1) hw hsupp f hk2,
        ← Ex_push_eq (up w n (k + 1) hw hsupp hk2) (pi w n (k + 1) hw hsupp hsum hk2.le)
          (levelFun w n hw hsupp f (k + 1 + 1)),
        (up_down_adjoint w n (k + 1) hw hsupp hsum hk2).push_left]
    have e2 : Ex (pi w n (k + 1) hw hsupp hsum hk1) (levelFun w n hw hsupp f (k + 1))
        = Ex (pi w n k hw hsupp hsum hk1.le) (levelFun w n hw hsupp f k) := by
      rw [levelFun_succ w n k hw hsupp f hk1,
        ← Ex_push_eq (up w n k hw hsupp hk1) (pi w n k hw hsupp hsum hk1.le)
          (levelFun w n hw hsupp f (k + 1)),
        (up_down_adjoint w n k hw hsupp hsum hk1).push_left]
    exact e1.trans e2
  have hA := Var_eq_ip_sub_sq (pi w n (k + 2) hw hsupp hsum hk3)
    (levelFun w n hw hsupp f (k + 2))
  have hB := Var_eq_ip_sub_sq (pi w n k hw hsupp hsum hk1.le) (levelFun w n hw hsupp f k)
  rw [ip_self_eq_Ex_sq] at hA hB
  rw [hmean] at hA
  rw [step1, Ex_sub, step2, levelVar_apply w n (k + 2) hw hsupp hsum f hk3,
    levelVar_apply w n k hw hsupp hsum f hk1.le]
  linarith [hA, hB]

/-- **`claim:first-step`, with the left-hand side expanded.**

  `𝔼_{τ ∼ π_k}[Var_{π_{τ,2}}(f_τ^{(2)})]
      = ℰ_{P^{∨∧}_{k+1}}(f^{(k+2)}) + ℰ_{P^{∨∧}_k}(f^{(k+1)})`.

This is the form the monograph's proof of `lem:improved-technical` uses: its
first display rewrites the sum of the two down-up Dirichlet forms as the variance
drop by `lem:diff-var` and then as this average by `claim:first-step`.  The
rewriting of the left-hand side is
`LinkRestriction.levelVar_sub_levelVar_eq_add`. -/
theorem Ex_Var_linkShiftPiOf_eq_levelEnergy_add (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk2 : k + 1 < n) :
    Ex (pi w n k hw hsupp hsum (by omega : k ≤ n))
        (fun τ => Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f))
      = levelEnergy w n hw hsupp hsum f (k + 1) + levelEnergy w n hw hsupp hsum f k := by
  rw [Ex_Var_linkShiftPiOf_eq_levelVar_sub w n k hw hsupp hsum f hk2,
    levelVar_sub_levelVar_eq_add w n k hw hsupp hsum f hk2]

/-! ## The companion identity one level up

`claim:first-step` is one of the two averaged identities the monograph's proof of
`lem:improved-technical` uses; the other is `claim:DDD`,

  `ℰ_{P^{∨∧}_k}(f^{(k+1)}) = 𝔼_{τ ∼ π_k}[Var_{π_{τ,1}}(f_τ^{(1)})]`,

which `LocalToGlobal.dirichlet_downUp_eq_Ex_Var_linkDistOf` already proves —
but in the language of `LocalWalk.linkDist`, a distribution on *elements* of `E`,
whereas `lem:improved-technical` compares it term by term with
`claim:first-step`, whose local variances are taken against `π_{τ,2}`, a
distribution on *faces*.  This section transports the identity along `e ↦ {e}`,
so that both averages are `Var (linkShiftPiOf w n j τ …) (linkLevelFun w n j τ …)`
at `j = 1` and `j = 2` and can be compared face by face.

Nothing here depends on `lem:updown-downup`; the inequality between the two
averages does, and is deliberately left out. -/

/-- **`π_{τ,1}` and `LocalWalk.linkDist` compute the same averages.**  The former
lives on the singleton faces, the latter on the elements of `E`; they agree along
`e ↦ {e}` by `LinkRestriction.linkShiftPi_one_singleton`, and both give mass `0`
to everything else. -/
theorem Ex_linkShiftPi_one_eq_Ex_linkDist (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) (hj : 1 ≤ n - τ.card) (h : Finset E → ℝ) :
    Ex (linkShiftPi w n 1 τ hw hsupp hk.le hpos hj) h
      = Ex (linkDist w n τ hw hsupp hpos hk) (fun e => h {e}) := by
  have h1 : ∀ ρ : Finset E, linkShiftPi w n 1 τ hw hsupp hk.le hpos hj ρ * h ρ
      = if ρ.card = 1 then linkShiftPi w n 1 τ hw hsupp hk.le hpos hj ρ * h ρ else 0 := by
    intro ρ
    by_cases hc : ρ.card = 1
    · rw [if_pos hc]
    · rw [if_neg hc,
        linkShiftPi_eq_zero_of_card_ne w n 1 τ hw hsupp hk.le hpos hj hc, zero_mul]
  have h2 : ∀ e : E, linkShiftPi w n 1 τ hw hsupp hk.le hpos hj {e} * h {e}
      = linkDist w n τ hw hsupp hpos hk e * h {e} := by
    intro e
    by_cases he : e ∈ τ
    · rw [linkShiftPi_eq_zero_of_not_disjoint w n 1 τ hw hsupp hk.le hpos hj
        (fun hd => (Finset.disjoint_singleton_right.mp hd) he),
        linkDist_of_mem w n τ hw hsupp hpos hk he]
    · rw [linkShiftPi_one_singleton w n τ hw hsupp hpos hk he]
  simp only [Ex_apply]
  rw [Finset.sum_congr rfl fun ρ _ => h1 ρ, sum_ite_card_one,
    Finset.sum_congr rfl fun e _ => h2 e]

/-- The variance form of `Ex_linkShiftPi_one_eq_Ex_linkDist`. -/
theorem Var_linkShiftPi_one_eq_Var_linkDist (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) (hj : 1 ≤ n - τ.card) (h : Finset E → ℝ) :
    Var (linkShiftPi w n 1 τ hw hsupp hk.le hpos hj) h
      = Var (linkDist w n τ hw hsupp hpos hk) (fun e => h {e}) := by
  rw [Var_eq_ip_sub_sq, Var_eq_ip_sub_sq, ip_eq_Ex_mul, ip_eq_Ex_mul,
    Ex_linkShiftPi_one_eq_Ex_linkDist w n τ hw hsupp hpos hk hj (fun ρ => h ρ * h ρ),
    Ex_linkShiftPi_one_eq_Ex_linkDist w n τ hw hsupp hpos hk hj h]

/-- **`claim:DDD` in the language of the honest link.**

  `𝔼_{τ ∼ π_k}[Var_{π_{τ,1}}(f_τ^{(1)})] = ℰ_{P^{∨∧}_k}(f^{(k+1)})`.

This is `LocalToGlobal.dirichlet_downUp_eq_Ex_Var_linkDistOf` with both the
distribution and the function transported to the honest link: `π_{τ,1}` in place
of `linkDist`, and the link projection `f_τ^{(1)}` in place of
`e ↦ f^{(k+1)}(τ ∪ {e})`.  Stated because `lem:improved-technical` compares it
term by term with `claim:first-step`, whose local variances live on faces.

The `[Nonempty E]` instance that `linkDistOf` needs is supplied inside the proof
by `LocalToGlobal.nonempty_of_weight`; it does not appear in the statement. -/
theorem Ex_pi_Var_linkShiftPiOf_one_eq_levelEnergy (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) :
    Ex (pi w n k hw hsupp hsum hk.le)
        (fun τ => Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f))
      = levelEnergy w n hw hsupp hsum f k := by
  haveI : Nonempty E := nonempty_of_weight hsupp hsum (by omega)
  rw [levelEnergy_apply w n k hw hsupp hsum f hk,
    dirichlet_downUp_eq_Ex_Var_linkDistOf w n k hw hsupp hsum hk
      (levelFun w n hw hsupp f (k + 1))]
  refine Ex_congr_ae fun τ hz => ?_
  show Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f)
    = Var (linkDistOf w n hw hsupp τ)
        (fun e => levelFun w n hw hsupp f (k + 1) (insert e τ))
  have hcard : τ.card = k := by
    by_contra hc
    exact hz (by rw [pi_apply, if_neg hc])
  have hmu : 0 < mu w τ := by
    rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
    · exact h
    · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
  have hkτ : τ.card < n := by omega
  have hj : 1 ≤ n - τ.card := by omega
  have hagree : ∀ ρ : Finset E, ρ.card = 1 → Disjoint τ ρ → 0 < mu w (τ ∪ ρ) →
      linkLevelFun w n 1 τ hw hsupp f ρ = levelFun w n hw hsupp f (k + 1) (τ ∪ ρ) := by
    intro ρ hc hd hm
    rw [linkLevelFun_eq_levelFun w n 1 τ hw hsupp f hkτ.le hd hc hm, hcard]
  have hfun : (fun e : E => levelFun w n hw hsupp f (k + 1) (τ ∪ {e}))
      = fun e : E => levelFun w n hw hsupp f (k + 1) (insert e τ) := by
    funext e
    rw [Finset.union_comm, ← Finset.insert_eq]
  rw [linkShiftPiOf_eq_linkShiftPi w n 1 τ hw hsupp hkτ.le hmu hj,
    linkDistOf_eq_linkDist w n hw hsupp hmu hkτ,
    Var_linkShiftPi_congr w n 1 τ hw hsupp hkτ.le hmu hj hagree,
    Var_linkShiftPi_one_eq_Var_linkDist w n τ hw hsupp hmu hkτ hj
      (fun ρ => levelFun w n hw hsupp f (k + 1) (τ ∪ ρ)), hfun]

end Arlib.MarkovChains


