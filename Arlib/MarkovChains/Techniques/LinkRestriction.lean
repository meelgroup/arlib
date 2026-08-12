/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Restriction to a link: the projections `f^{(k)}` commute with conditioning

`Techniques.LocalToGlobal` decomposes the top-level variance into the Dirichlet
forms of the down-up walks, using the projected family `f^{(k)}` defined by the
downward recursion `f^{(n)} = f`, `f^{(k)} = U_k f^{(k+1)}`.  Every remaining
step of §6.6 of the monograph is *local*: it works inside the link of a face `τ`
and uses, without proof, that the projections computed there are the ambient ones
with all the levels shifted by `|τ|` ("for `η ∈ Pinning_{k-1}` and `τ` on two
further vertices, `f_η^{(2)}(τ) = f^{(k+1)}(η ∪ τ)`").  This module proves that.

**The mechanism is a closed form for `f^{(k)}`.**  The recursion is opaque to
comparison, but what it computes is not: for a face `τ` of positive derived
weight,

  **`f^{(k)}(τ) = mu (w · f) τ / mu w τ = (∑_{σ ⊇ τ} w σ f σ) / (∑_{σ ⊇ τ} w σ)`,**

the conditional expectation of `f` given that the top face contains `τ`
(`levelFun_eq_div`).  Once both projections are ratios of derived weights, any
statement comparing a link projection with an ambient one reduces to
`LocalWalk.mu_starWeight`-style bookkeeping, and the numerator is handled by the
*same* lemma applied to the weight `w · f` — which satisfies the same support
hypothesis as `w`.  This is why the module needs no new counting.

**A star and a link, and only one of them is the monograph's.**  `LocalWalk.starWeight`
keeps the ambient dimension `n`; its faces of size `j` are all the `j`-subsets of
the top faces containing `τ`, *including subsets that meet `τ`*.  That is the
**star** of `τ`, and it is a perfectly good weighted complex — the restriction
theorem holds for it (`levelFun_starWeightNorm`).  But its level-`j`
distribution `LocalWalk.starPi w n j τ` is **not** the monograph's `π_{τ,j}`: it
gives every `j`-subface of `τ` itself the mass `1 / n.choose j`
(`starPi_apply_of_subset`).  The monograph's link has dimension `n - |τ|` and
lives on the faces disjoint from `τ`; it is built here as `linkShift` /
`linkShiftNorm`, and its level-`j` distribution `linkShiftPi` is `π_{τ,j}`,
audited at `j = 1` against `LocalWalk.linkDist` (`linkShiftPi_one_singleton`).
Both restriction theorems are proved, because both complexes occur.

Main declarations:

* `linkShift`, `linkShiftNorm` and `linkShift_nonneg`, `linkShift_supp`,
  `sum_linkShiftNorm` — the **honest link**: a weighted complex of dimension
  `n - |τ|` on the faces disjoint from `τ`, satisfying all three hypotheses of
  `Techniques.Levels`.
* **`mu_linkShift`** — `mu (linkShift v τ) ρ = mu v (τ ∪ ρ)`: the derived weights
  of the honest link are the ambient ones shifted by `τ`.  The one genuine
  reindexing of the module, along `σ ↦ σ \ τ` and `ρ ↦ τ ∪ ρ`.
* **`levelFun_eq_div`** — the closed form of the projection as a ratio of derived
  weights, with `mu_mul_levelFun` for the version valid at null faces.
* **`levelFun_starWeightNorm`** and `levelFun_starWeightNorm_disjoint` — the
  restriction theorem for the star: `(f_τ)^{(j)}(ρ) = f^{(|τ ∪ ρ|)}(τ ∪ ρ)`, and
  for `ρ` disjoint from `τ`, `= f^{(|τ| + j)}(τ ∪ ρ)`.
* **`levelFun_linkShiftNorm`** — the same for the honest link, where the shift
  `j ↦ j + |τ|` is literal and the restricted function is `σ ↦ f (τ ∪ σ)`.
* `linkShiftPi`, `linkShiftPi_apply_of_disjoint`, **`linkShiftPi_one_singleton`**
  — the monograph's `π_{τ,j}`, and the check that at `j = 1` it agrees with the
  independently built `LocalWalk.linkDist`.
* `linkShiftPi_eq_zero_of_not_disjoint`, `starPi_apply_of_subset` — the two
  lemmas that separate `π_{τ,j}` from `LocalWalk.starPi w n j τ`.
* `sum_ite_disjoint_union` — the reindexing of `mu_linkShift`, isolated so that
  it applies to a summand other than a derived weight.
* `linkShiftPiOf`, `linkShiftPiOf_eq_linkShiftPi` — the **guarded-total**
  `π_{τ,j}`, total in `τ` so that it can appear inside a `π_k`-average, with
  `Ex_linkShiftPi_congr` and `Var_linkShiftPi_congr` for the partial agreement on
  the support.  Unlike `LocalWalk.linkDistOf` it needs no `[Nonempty E]`: its
  state space is `Finset E`, which always contains `∅`.
* `linkLevelFun`, `linkLevelFun_eq_levelFun` — the guarded-total `f_τ^{(j)}`,
  together with the restriction theorem in guarded form.
* `Var_linkShiftPi_succ_eq` and **`Var_linkShiftPi_two_eq`** — the one-step
  variance identity of `Techniques.LevelVariance` inside the link, at the level
  pair `(1, 2)` that `claim:first-step` uses.
* `levelVar_sub_levelVar_eq_add` — the left-hand side of `claim:first-step`,
  `Var_{π_{k+2}}(f^{(k+2)}) − Var_{π_k}(f^{(k)})`, as the sum of two level
  energies of `Techniques.LocalToGlobal`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LocalToGlobal

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [DecidableEq E]

/-! ## Attaching a face to a small face of its link

Every face of the link of `τ` is read in the ambient complex as `τ ∪ ρ`, so the
level-one and level-two computations keep meeting `τ ∪ {e}` and
`τ ∪ {e, e'}`; these are the two rewrites that put them in `insert` form. -/

/-- Attaching `τ` to a singleton: `τ ∪ {e} = insert e τ`. -/
theorem union_singleton_eq_insert (τ : Finset E) (e : E) :
    τ ∪ ({e} : Finset E) = insert e τ := by
  rw [Finset.union_comm, ← Finset.insert_eq]

/-- Attaching `τ` to a two-element face. -/
theorem union_pair_eq_insert_insert (τ : Finset E) (e e' : E) :
    τ ∪ insert e' ({e} : Finset E) = insert e' (insert e τ) := by
  rw [Finset.union_comm, Finset.insert_union, ← Finset.insert_eq]

/-! ## The shifted link weight

The one definition of this module that does not mention the ambient `Fintype`
structure, placed first for the same reason `LocalWalk.starWeight` is: it is a
pointwise formula, and every quantitative statement about it needs sums. -/

/-- The **shifted link weight** of a face `τ`: `linkShift w τ σ = w (τ ∪ σ)` for
`σ` disjoint from `τ`, and `0` otherwise.

Unlike `LocalWalk.starWeight`, which keeps the ambient dimension `n` and whose
faces are all the subfaces of the top faces containing `τ`, this is the *link* in
the simplicial sense: a weighted complex of dimension `n - |τ|` whose faces are
the faces of the ambient complex disjoint from `τ`.  It is the complex the
monograph's `π_{τ,j}` lives on, and it is the construction in which the level
shift `j ↦ j + |τ|` is literal rather than implicit. -/
def linkShift (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => if Disjoint τ σ then w (τ ∪ σ) else 0

/-- The defining formula for `linkShift`. -/
theorem linkShift_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    linkShift w τ σ = if Disjoint τ σ then w (τ ∪ σ) else 0 := rfl

/-- Hypothesis `hw` for the shifted link. -/
theorem linkShift_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    ∀ σ : Finset E, 0 ≤ linkShift w τ σ := by
  intro σ
  rw [linkShift_apply]
  split
  exacts [hw _, le_rfl]

/-- Hypothesis `hsupp` for the shifted link, **at the shifted dimension**
`n - |τ|`: a face of the link of the wrong size completes to an ambient face of
the wrong size. -/
theorem linkShift_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτn : τ.card ≤ n) :
    ∀ σ : Finset E, σ.card ≠ n - τ.card → linkShift w τ σ = 0 := by
  intro σ hσ
  rw [linkShift_apply]
  by_cases hd : Disjoint τ σ
  · rw [if_pos hd]
    exact hsupp _ (by rw [Finset.card_union_of_disjoint hd]; omega)
  · rw [if_neg hd]

section Fintype

variable [Fintype E]

/-! ## The projection is a ratio of derived weights -/

/-- If a face is null then it is null for the weight `w · f` as well. -/
theorem mu_mul_eq_zero_of_mu_eq_zero {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (f : Finset E → ℝ) {τ : Finset E} (hτ : mu w τ = 0) :
    mu (fun σ => w σ * f σ) τ = 0 := by
  have hnn : ∀ σ ∈ (Finset.univ : Finset (Finset E)), 0 ≤ (if τ ⊆ σ then w σ else 0) := by
    intro σ _
    split
    exacts [hw σ, le_rfl]
  have hz : ∀ σ : Finset E, τ ⊆ σ → w σ = 0 := by
    intro σ hσ
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hτ σ (Finset.mem_univ σ)
    rwa [if_pos hσ] at h0
  rw [mu_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : τ ⊆ σ
  · rw [if_pos h, hz σ h, zero_mul]
  · rw [if_neg h]

/-- A face of positive derived weight has at most `n` elements. -/
theorem card_le_of_mu_pos {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hpos : 0 < mu w τ) :
    τ.card ≤ n := by
  by_contra hc
  refine hpos.ne' ?_
  rw [mu_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : τ ⊆ σ
  · rw [if_pos h, hsupp σ (by have := Finset.card_le_card h; omega)]
  · rw [if_neg h]

/-- The induction-ready form of `levelFun_eq_div`: the statement with the
recursion depth `n - k` exposed, so that the downward recursion of `levelFun`
becomes an ordinary induction on `ℕ`. -/
theorem levelFun_eq_div_of_sub (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) :
    ∀ (d k : ℕ) (τ : Finset E), n - k = d → τ.card = k → 0 < mu w τ →
      levelFun w n hw hsupp f k τ = mu (fun σ => w σ * f σ) τ / mu w τ := by
  have hsuppf : ∀ σ : Finset E, σ.card ≠ n → w σ * f σ = 0 := by
    intro σ hσ
    rw [hsupp σ hσ, zero_mul]
  intro d
  induction d with
  | zero =>
      intro k τ hd hcard hpos
      have hkn : k ≤ n := hcard ▸ card_le_of_mu_pos hsupp hpos
      have hk : k = n := by omega
      subst hk
      have hcardn : τ.card = k := hcard
      rw [levelFun_top w k hw hsupp f, mu_top hsupp hcardn, mu_top hsuppf hcardn]
      rw [mu_top hsupp hcardn] at hpos
      field_simp
  | succ d ih =>
      intro k τ hd hcard hpos
      have hkn : k ≤ n := hcard ▸ card_le_of_mu_pos hsupp hpos
      have hk : k < n := by omega
      have hD : ((n - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm : mu w τ ≠ 0 := hpos.ne'
      -- the term-by-term evaluation of the up-step
      have hstep : ∀ η : Finset E,
          up w n k hw hsupp hk τ η * levelFun w n hw hsupp f (k + 1) η
            = (if η.card = k + 1 ∧ τ ⊆ η then mu (fun σ => w σ * f σ) η else 0)
                / (((n - k : ℕ) : ℝ) * mu w τ) := by
        intro η
        rw [up_apply, if_pos ⟨hcard, hpos⟩]
        by_cases hc : η.card = k + 1 ∧ τ ⊆ η
        · rw [if_pos hc, if_pos hc]
          by_cases hη : 0 < mu w η
          · rw [ih (k + 1) η (by omega) hc.1 hη, div_mul_div_comm,
              mul_comm (((n - k : ℕ) : ℝ) * mu w τ) (mu w η),
              mul_div_mul_left _ _ hη.ne']
          · have hη0 : mu w η = 0 := le_antisymm (not_lt.mp hη) (mu_nonneg hw η)
            rw [hη0, mu_mul_eq_zero_of_mu_eq_zero hw f hη0, zero_div, zero_mul]
        · rw [if_neg hc, if_neg hc, zero_mul, zero_div]
      rw [levelFun_succ w n k hw hsupp f hk, FinKernel.act_apply,
        Finset.sum_congr rfl fun η _ => hstep η, ← Finset.sum_div,
        sum_ite_mu_level_succ (fun σ => w σ * f σ) n k hsuppf hcard,
        mul_div_mul_left _ _ hD]

/-- **The projection `f^{(k)}` is a ratio of derived weights.**  For a face `τ`
of cardinality `k` and positive derived weight,

  **`f^{(k)}(τ) = (∑_{σ ⊇ τ} w σ · f σ) / (∑_{σ ⊇ τ} w σ)`**,

that is, `f^{(k)}(τ) = mu (w · f) τ / mu w τ`: the conditional expectation of `f`
given that the top face contains `τ`.

The monograph *defines* `f^{(k)}` by the downward recursion `f^{(k)} = U_k f^{(k+1)}`,
and this is the closed form that recursion computes.  Everything in this module
is a corollary: two projections agree exactly when the two ratios do, and ratios
of derived weights are trivial to compare across a link because
`LocalWalk.mu_starWeight` says the star's derived weights are the ambient ones
shifted by `τ`.

Note that the hypothesis `k ≤ n` is *not* needed: `0 < mu w τ` already forces
`τ.card ≤ n` (`card_le_of_mu_pos`).  The proof is an induction on the recursion
depth `n - k`; the inductive step is `Levels.sum_ite_mu_level_succ` applied to the
weight `w · f`, which satisfies the same support hypothesis as `w`.  Null faces
one level up need no separate argument: their up-transition probability and their
`mu (w · f)` both vanish. -/
theorem levelFun_eq_div (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) {τ : Finset E}
    (hcard : τ.card = k) (hpos : 0 < mu w τ) :
    levelFun w n hw hsupp f k τ = mu (fun σ => w σ * f σ) τ / mu w τ :=
  levelFun_eq_div_of_sub w n hw hsupp f (n - k) k τ rfl hcard hpos

/-- The projection at the cardinality of the face itself, which is the form in
which the comparison lemmas below use `levelFun_eq_div`. -/
theorem levelFun_card_eq_div (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) {τ : Finset E}
    (hpos : 0 < mu w τ) :
    levelFun w n hw hsupp f τ.card τ = mu (fun σ => w σ * f σ) τ / mu w τ :=
  levelFun_eq_div w n τ.card hw hsupp f rfl hpos

/-- **The projection is an average of the values of `f`.**  Scaling out the
denominator: `mu w τ · f^{(k)}(τ) = ∑_{σ ⊇ τ} w σ · f σ`.  Stated because it
holds at null faces too, where the ratio form says nothing. -/
theorem mu_mul_levelFun (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) {τ : Finset E}
    (hcard : τ.card = k) :
    mu w τ * levelFun w n hw hsupp f k τ = mu (fun σ => w σ * f σ) τ := by
  by_cases hpos : 0 < mu w τ
  · rw [levelFun_eq_div w n k hw hsupp f hcard hpos, mul_div_cancel₀ _ hpos.ne']
  · have h0 : mu w τ = 0 := le_antisymm (not_lt.mp hpos) (mu_nonneg hw τ)
    rw [h0, zero_mul, mu_mul_eq_zero_of_mu_eq_zero hw f h0]

/-! ## Scaling the weight -/

/-- Derived weights are homogeneous: dividing the weight by a scalar divides all
the derived weights.  This is the only fact needed to pass between `starWeight`
and `starWeightNorm`. -/
theorem mu_div (g : Finset E → ℝ) (c : ℝ) (ρ : Finset E) :
    mu (fun σ => g σ / c) ρ = mu g ρ / c := by
  rw [mu_apply, mu_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split
  · rfl
  · rw [zero_div]

/-! ## Restriction to the link of a face -/

/-- The derived weight of `w · f` in the link of `τ`:

  `mu (starWeightNorm w τ · f) ρ = mu (w · f) (τ ∪ ρ) / mu w τ`.

This is `LocalWalk.mu_starWeightNorm` with the weight `w` replaced by `w · f`,
and it is the only computation the restriction theorem needs. -/
theorem mu_mul_starWeightNorm (w f : Finset E → ℝ) (τ ρ : Finset E) :
    mu (fun σ => starWeightNorm w τ σ * f σ) ρ
      = mu (fun σ => w σ * f σ) (τ ∪ ρ) / mu w τ := by
  have h1 : (fun σ => starWeightNorm w τ σ * f σ)
      = fun σ => starWeight (fun σ' => w σ' * f σ') τ σ / mu w τ := by
    funext σ
    rw [starWeightNorm_apply, starWeight_apply, starWeight_apply]
    by_cases h : τ ⊆ σ
    · rw [if_pos h, if_pos h, div_mul_eq_mul_div]
    · rw [if_neg h, if_neg h, zero_div, zero_mul]
  rw [h1, mu_div, mu_starWeight]

/-- **The projections commute with restriction to a link.**  For every face `τ`,
every `ρ` of cardinality `j`, and every `f` on the top level,

  **`(f_τ)^{(j)}(ρ) = f^{(|τ ∪ ρ|)}(τ ∪ ρ)`**,

where the left side is the level-`j` projection computed *inside the link of `τ`*
— that is, for the weighted complex `starWeightNorm w τ` — and the right side is
the ambient projection.

Both sides are the conditional expectation of `f` given that the top face
contains `τ ∪ ρ`, by `levelFun_eq_div`: the link's derived weights are the
ambient ones shifted by `τ` (`LocalWalk.mu_starWeightNorm`), the same holds for
the weight `w · f` (`mu_mul_starWeightNorm`), and the two normalising factors
`mu w τ` cancel in the ratio.

Note that no restriction operation is applied to `f` itself: the link of `τ` is a
complex on the *same* ground set and of the *same* dimension `n`, so a function
on its top level is literally a function on the top level of the ambient complex.
The only hypothesis is `0 < mu w (τ ∪ ρ)`, which is exactly the condition under
which `f^{(·)}(τ ∪ ρ)` is a genuine conditional expectation rather than the junk
value of a degenerate row. -/
theorem levelFun_starWeightNorm (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) (τ ρ : Finset E)
    (hcard : ρ.card = j) (hpos : 0 < mu w (τ ∪ ρ)) :
    levelFun (starWeightNorm w τ) n (starWeightNorm_nonneg hw τ)
        (starWeightNorm_supp hsupp τ) f j ρ
      = levelFun w n hw hsupp f (τ ∪ ρ).card (τ ∪ ρ) := by
  have hτ : 0 < mu w τ := lt_of_lt_of_le hpos (mu_mono hw Finset.subset_union_left)
  have hτ0 : mu w τ ≠ 0 := hτ.ne'
  have hρ0 : mu w (τ ∪ ρ) ≠ 0 := hpos.ne'
  have hlink : 0 < mu (starWeightNorm w τ) ρ := by
    rw [mu_starWeightNorm]
    exact div_pos hpos hτ
  rw [levelFun_eq_div (starWeightNorm w τ) n j (starWeightNorm_nonneg hw τ)
      (starWeightNorm_supp hsupp τ) f hcard hlink,
    levelFun_card_eq_div w n hw hsupp f hpos, mu_mul_starWeightNorm w f τ ρ,
    mu_starWeightNorm, div_div_div_cancel_right₀]
  exact hτ0

/-- **The index shift.**  For a face `ρ` of the link of `τ` in the honest sense —
`ρ` disjoint from `τ` — the level-`j` projection inside the link of `τ` is the
level-`(|τ| + j)` projection of the ambient complex:

  **`(f_τ)^{(j)}(ρ) = f^{(|τ| + j)}(τ ∪ ρ)`.**

This is the identity the monograph states without proof in the course of
`claim:first-step` (§6.6, "then `f_η^{(2)}(τ) = f^{(k+1)}(η ∪ τ)`", for
`|η| = k - 1`): conditioning on a face of size `|τ|` shifts every level by
`|τ|`.  The disjointness hypothesis is what turns `|τ ∪ ρ|` into `|τ| + j`; it
is *not* needed for `levelFun_starWeightNorm` itself, which is the reason that
theorem is stated first. -/
theorem levelFun_starWeightNorm_disjoint (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) (τ ρ : Finset E)
    (hd : Disjoint τ ρ) (hcard : ρ.card = j) (hpos : 0 < mu w (τ ∪ ρ)) :
    levelFun (starWeightNorm w τ) n (starWeightNorm_nonneg hw τ)
        (starWeightNorm_supp hsupp τ) f j ρ
      = levelFun w n hw hsupp f (τ.card + j) (τ ∪ ρ) := by
  rw [levelFun_starWeightNorm w n j hw hsupp f τ ρ hcard hpos,
    Finset.card_union_of_disjoint hd, hcard]

/-! ## The honest link, with the levels shifted down by `|τ|` -/

/-- **The faces of a link reindex the faces above `τ`.**  For every `Φ`,

  `∑_{ρ : |ρ| = j, ρ ∩ τ = ∅} Φ (τ ∪ ρ) = ∑_{σ : |σ| = |τ| + j, τ ⊆ σ} Φ σ`,

under the mutually inverse maps `ρ ↦ τ ∪ ρ` and `σ ↦ σ ∖ τ`.

This is the reindexing performed inside `mu_linkShift` below, isolated
so that it can be applied to a summand other than a derived weight; here it is
applied to `σ ↦ mu w σ · G σ`. -/
theorem sum_ite_disjoint_union (τ : Finset E) (j : ℕ) (Φ : Finset E → ℝ) :
    ∑ ρ : Finset E, (if ρ.card = j ∧ Disjoint τ ρ then Φ (τ ∪ ρ) else 0)
      = ∑ σ : Finset E, (if σ.card = τ.card + j ∧ τ ⊆ σ then Φ σ else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hset : (Finset.univ.filter fun σ : Finset E => σ.card = τ.card + j ∧ τ ⊆ σ)
      = (Finset.univ.filter fun ρ : Finset E => ρ.card = j ∧ Disjoint τ ρ).image
          (fun ρ => τ ∪ ρ) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hcard, hsub⟩
      refine ⟨σ \ τ, ⟨?_, Finset.disjoint_sdiff⟩, ?_⟩
      · rw [Finset.card_sdiff_of_subset hsub, hcard]
        omega
      · rw [Finset.union_comm, Finset.sdiff_union_of_subset hsub]
    · rintro ⟨ρ, ⟨hc, hd⟩, rfl⟩
      exact ⟨by rw [Finset.card_union_of_disjoint hd, hc], Finset.subset_union_left⟩
  have hinj : ∀ a ∈ (Finset.univ.filter fun ρ : Finset E => ρ.card = j ∧ Disjoint τ ρ),
      ∀ b ∈ (Finset.univ.filter fun ρ : Finset E => ρ.card = j ∧ Disjoint τ ρ),
      τ ∪ a = τ ∪ b → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    rw [← Finset.union_sdiff_cancel_left ha.2.2, hab,
      Finset.union_sdiff_cancel_left hb.2.2]
  rw [hset, Finset.sum_image hinj]

/-- **The derived weights of the shifted link are the ambient ones shifted by
`τ`**: `mu (linkShift v τ) ρ = mu v (τ ∪ ρ)` for `ρ` disjoint from `τ`.

This is the analogue of `LocalWalk.mu_starWeight` for the honest link, and it is
the only combinatorial content of this section.  Where `mu_starWeight` is a
one-line consequence of `Finset.union_subset_iff`, this one is a genuine
reindexing: the faces `σ ⊇ τ ∪ ρ` of the ambient complex correspond to the faces
`σ \ τ ⊇ ρ` of the link, under the mutually inverse maps `σ ↦ σ \ τ` and
`ρ' ↦ τ ∪ ρ'`.

It is stated for an arbitrary weight `v` because it is needed twice: once for
`v = w`, and once for `v = w · f`, which is what carries the *function* across
the link in `levelFun_linkShiftNorm`. -/
theorem mu_linkShift (v : Finset E → ℝ) {τ ρ : Finset E} (hd : Disjoint τ ρ) :
    mu (linkShift v τ) ρ = mu v (τ ∪ ρ) := by
  rw [mu_apply, mu_apply]
  have hL : ∀ σ : Finset E,
      (if ρ ⊆ σ then linkShift v τ σ else 0)
        = if ρ ⊆ σ ∧ Disjoint τ σ then v (τ ∪ σ) else 0 := by
    intro σ
    rw [linkShift_apply]
    by_cases h1 : ρ ⊆ σ
    · by_cases h2 : Disjoint τ σ
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, if_neg fun hc => h2 hc.2]
    · rw [if_neg h1, if_neg fun hc => h1 hc.1]
  rw [Finset.sum_congr rfl fun σ _ => hL σ, ← Finset.sum_filter, ← Finset.sum_filter]
  have hset : (Finset.univ.filter fun σ : Finset E => τ ∪ ρ ⊆ σ)
      = (Finset.univ.filter fun σ : Finset E => ρ ⊆ σ ∧ Disjoint τ σ).image
          (fun σ => τ ∪ σ) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hsub
      have hτσ : τ ⊆ σ := (Finset.union_subset_iff.mp hsub).1
      refine ⟨σ \ τ, ⟨?_, Finset.disjoint_sdiff⟩, ?_⟩
      · intro e he
        rw [Finset.mem_sdiff]
        exact ⟨hsub (Finset.mem_union_right _ he),
          fun hc => (Finset.disjoint_left.mp hd hc) he⟩
      · rw [Finset.union_comm, Finset.sdiff_union_of_subset hτσ]
    · rintro ⟨σ', ⟨h1, _⟩, rfl⟩
      exact Finset.union_subset_union (Finset.Subset.refl τ) h1
  have hinj : ∀ a ∈ (Finset.univ.filter fun σ : Finset E => ρ ⊆ σ ∧ Disjoint τ σ),
      ∀ b ∈ (Finset.univ.filter fun σ : Finset E => ρ ⊆ σ ∧ Disjoint τ σ),
      τ ∪ a = τ ∪ b → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    rw [← Finset.union_sdiff_cancel_left ha.2.2, hab,
      Finset.union_sdiff_cancel_left hb.2.2]
  rw [hset, Finset.sum_image hinj]

/-- The derived weights of the shifted link vanish off the faces disjoint from
`τ`: a face of the link meeting `τ` has no face of the link above it. -/
theorem mu_linkShift_eq_zero_of_not_disjoint (w : Finset E → ℝ) {τ ρ : Finset E}
    (hd : ¬ Disjoint τ ρ) : mu (linkShift w τ) ρ = 0 := by
  rw [mu_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hsub : ρ ⊆ σ
  · rw [if_pos hsub, linkShift_apply, if_neg fun hc => hd (hc.mono_right hsub)]
  · rw [if_neg hsub]

/-- The partition function of the shifted link is the derived weight of `τ`,
exactly as for `LocalWalk.starWeight`. -/
theorem sum_linkShift (w : Finset E → ℝ) (τ : Finset E) :
    ∑ σ : Finset E, linkShift w τ σ = mu w τ := by
  rw [← mu_empty (linkShift w τ), mu_linkShift w (Finset.disjoint_empty_right τ),
    Finset.union_empty]

/-- The **normalised shifted link weight**: the top-level weight of the honest
link as a probability-weighted complex of dimension `n - |τ|`. -/
noncomputable def linkShiftNorm (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => linkShift w τ σ / mu w τ

/-- The defining formula for `linkShiftNorm`. -/
theorem linkShiftNorm_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    linkShiftNorm w τ σ = linkShift w τ σ / mu w τ := rfl

/-- Hypothesis `hw` for the normalised shifted link. -/
theorem linkShiftNorm_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (τ : Finset E) : ∀ σ : Finset E, 0 ≤ linkShiftNorm w τ σ :=
  fun σ => div_nonneg (linkShift_nonneg hw τ σ) (mu_nonneg hw τ)

/-- Hypothesis `hsupp` for the normalised shifted link, at dimension `n - |τ|`. -/
theorem linkShiftNorm_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτn : τ.card ≤ n) :
    ∀ σ : Finset E, σ.card ≠ n - τ.card → linkShiftNorm w τ σ = 0 := by
  intro σ hσ
  rw [linkShiftNorm_apply, linkShift_supp hsupp hτn σ hσ, zero_div]

/-- Hypothesis `hsum` for the normalised shifted link. -/
theorem sum_linkShiftNorm (w : Finset E → ℝ) {τ : Finset E} (hpos : 0 < mu w τ) :
    ∑ σ : Finset E, linkShiftNorm w τ σ = 1 := by
  rw [Finset.sum_congr rfl fun σ _ => linkShiftNorm_apply w τ σ, ← Finset.sum_div,
    sum_linkShift, div_self hpos.ne']

/-- The derived weights of the normalised shifted link: the *conditional* derived
weights `mu w (τ ∪ ρ) / mu w τ`, for `ρ` disjoint from `τ`. -/
theorem mu_linkShiftNorm (w : Finset E → ℝ) {τ ρ : Finset E} (hd : Disjoint τ ρ) :
    mu (linkShiftNorm w τ) ρ = mu w (τ ∪ ρ) / mu w τ := by
  rw [show linkShiftNorm w τ = fun σ => linkShift w τ σ / mu w τ from rfl, mu_div,
    mu_linkShift w hd]

/-- The derived weights of the normalised link vanish off the faces disjoint
from `τ`.  The normalised form is what `Levels.up` reads, so it is recorded
beside the `linkShift` version `mu_linkShift_eq_zero_of_not_disjoint`. -/
theorem mu_linkShiftNorm_eq_zero_of_not_disjoint (w : Finset E → ℝ) {τ ρ : Finset E}
    (hd : ¬ Disjoint τ ρ) : mu (linkShiftNorm w τ) ρ = 0 := by
  rw [show linkShiftNorm w τ = fun σ => linkShift w τ σ / mu w τ from rfl, mu_div,
    mu_linkShift_eq_zero_of_not_disjoint w hd, zero_div]

/-- **The distribution `π_{τ,j}` of the monograph**: the level-`j` distribution
of the honest link of `τ`, a distribution on the faces of size `j` disjoint from
`τ`, with mass proportional to `mu w (τ ∪ ρ)`.

The dimension of the link is `n - |τ|`, so the level index runs `0 ≤ j ≤ n - |τ|`
and the normalising binomial coefficient is `(n - |τ|).choose j`, *not*
`n.choose j`.

Warning, and the reason this section exists: `LocalWalk.starPi w n j τ` is **not**
this distribution.  That one is the level-`j` distribution of `starWeightNorm w τ`,
whose faces are all `j`-subsets of the top faces containing `τ` — including
subsets that meet `τ`.  Its restriction to the faces disjoint from `τ` is
proportional to `π_{τ,j}`, with total mass `(n - |τ|).choose j / n.choose j`,
which is `< 1` whenever `0 < j` and `τ ≠ ∅`.  The two coincide for `τ = ∅`,
where no conditioning has taken place. -/
noncomputable def linkShiftPi (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) : FinDist (Finset E) :=
  pi (linkShiftNorm w τ) (n - τ.card) j (linkShiftNorm_nonneg hw τ)
    (linkShiftNorm_supp hsupp hτn) (sum_linkShiftNorm w hpos) hj

/-- `π_{τ,j}` in closed form on the faces disjoint from `τ`. -/
theorem linkShiftPi_apply_of_disjoint (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) {ρ : Finset E}
    (hd : Disjoint τ ρ) :
    linkShiftPi w n j τ hw hsupp hτn hpos hj ρ =
      if ρ.card = j then mu w (τ ∪ ρ) / (mu w τ * (((n - τ.card).choose j : ℕ) : ℝ))
      else 0 := by
  rw [linkShiftPi, pi_apply]
  split
  · rw [mu_linkShiftNorm w hd, div_div]
  · rfl

/-- `π_{τ,j}` vanishes off level `j`, for the same reason `pi` does. -/
theorem linkShiftPi_eq_zero_of_card_ne (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) {ρ : Finset E}
    (hcard : ρ.card ≠ j) :
    linkShiftPi w n j τ hw hsupp hτn hpos hj ρ = 0 := by
  rw [linkShiftPi, pi_apply, if_neg hcard]

/-- **The one-level-up distribution of `Techniques.LocalWalk` is `π_{τ,1}`.**

`LocalWalk.linkDist` carries the distribution one level above `τ` on ground-set
*elements*; `linkShiftPi w n 1 τ` carries it on singleton *faces*.  This lemma
checks that they agree, which is an audit of the shifted-link construction
against an object that was built independently and from a different formula. -/
theorem linkShiftPi_one_singleton (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) {e : E} (he : e ∉ τ) :
    linkShiftPi w n 1 τ hw hsupp hk.le hpos (by omega) {e}
      = linkDist w n τ hw hsupp hpos hk e := by
  have hd : Disjoint τ ({e} : Finset E) := by
    rw [Finset.disjoint_singleton_right]
    exact he
  rw [linkShiftPi_apply_of_disjoint w n 1 τ hw hsupp hk.le hpos (by omega) hd,
    if_pos (Finset.card_singleton e), linkDist_apply, if_neg he,
    Finset.union_comm, ← Finset.insert_eq, Nat.choose_one_right, mul_comm]

/-- **The index shift, on the honest link.**  For `ρ` disjoint from `τ` of
cardinality `j`,

  **`(f_τ)^{(j)}(ρ) = f^{(|τ| + j)}(τ ∪ ρ)`**,

where the left side is the level-`j` projection computed in the link complex of
dimension `n - |τ|`, applied to the *restricted* function `σ ↦ f (τ ∪ σ)`.

This is `levelFun_starWeightNorm_disjoint` transported to the link in the honest
sense.  The two statements are genuinely different — the left sides are
projections in two different weighted complexes, of dimensions `n` and `n - |τ|`
— and they agree because both are the conditional expectation of `f` given that
the top face contains `τ ∪ ρ`.  It is this version that pairs with `π_{τ,j}`,
and hence this version that the monograph's `claim:first-step` uses at `j = 2`. -/
theorem levelFun_linkShiftNorm (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) {τ : Finset E}
    (hτn : τ.card ≤ n) {ρ : Finset E} (hd : Disjoint τ ρ) (hcard : ρ.card = j)
    (hpos : 0 < mu w (τ ∪ ρ)) :
    levelFun (linkShiftNorm w τ) (n - τ.card) (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp hτn) (fun σ => f (τ ∪ σ)) j ρ
      = levelFun w n hw hsupp f (τ.card + j) (τ ∪ ρ) := by
  have hτ : 0 < mu w τ := lt_of_lt_of_le hpos (mu_mono hw Finset.subset_union_left)
  have hlink : 0 < mu (linkShiftNorm w τ) ρ := by
    rw [mu_linkShiftNorm w hd]
    exact div_pos hpos hτ
  have hnum : mu (fun σ => linkShiftNorm w τ σ * f (τ ∪ σ)) ρ
      = mu (fun σ => w σ * f σ) (τ ∪ ρ) / mu w τ := by
    have h1 : (fun σ => linkShiftNorm w τ σ * f (τ ∪ σ))
        = fun σ => linkShift (fun σ' => w σ' * f σ') τ σ / mu w τ := by
      funext σ
      rw [linkShiftNorm_apply, linkShift_apply, linkShift_apply]
      by_cases h : Disjoint τ σ
      · rw [if_pos h, if_pos h, div_mul_eq_mul_div]
      · rw [if_neg h, if_neg h, zero_div, zero_mul]
    rw [h1, mu_div, mu_linkShift _ hd]
  have hcardu : (τ ∪ ρ).card = τ.card + j := by
    rw [Finset.card_union_of_disjoint hd, hcard]
  rw [levelFun_eq_div (linkShiftNorm w τ) (n - τ.card) j (linkShiftNorm_nonneg hw τ)
      (linkShiftNorm_supp hsupp hτn) (fun σ => f (τ ∪ σ)) hcard hlink,
    levelFun_eq_div w n (τ.card + j) hw hsupp f hcardu hpos, hnum,
    mu_linkShiftNorm w hd, div_div_div_cancel_right₀]
  exact hτ.ne'

/-! ## The two link distributions are different

The two constructions above give two different level-`j` distributions at a face
`τ`, and it matters which one a downstream statement means.  The following two
lemmas make the difference explicit and checkable, on the faces where they
disagree most visibly: the subfaces of `τ` itself. -/

/-- **The honest link ignores the faces meeting `τ`**: `π_{τ,j}(ρ) = 0` unless
`ρ` is disjoint from `τ`. -/
theorem linkShiftPi_eq_zero_of_not_disjoint (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) {ρ : Finset E}
    (hd : ¬ Disjoint τ ρ) :
    linkShiftPi w n j τ hw hsupp hτn hpos hj ρ = 0 := by
  have hmu : mu (linkShiftNorm w τ) ρ = 0 := by
    rw [show linkShiftNorm w τ = fun σ => linkShift w τ σ / mu w τ from rfl, mu_div, mu_apply]
    rw [show (∑ σ : Finset E, if ρ ⊆ σ then linkShift w τ σ else 0) = 0 from
      Finset.sum_eq_zero fun σ _ => ?_, zero_div]
    by_cases hsub : ρ ⊆ σ
    · rw [if_pos hsub, linkShift_apply,
        if_neg fun hc => hd (hc.mono_right hsub)]
    · rw [if_neg hsub]
  rw [linkShiftPi, pi_apply]
  split
  · rw [hmu, zero_div]
  · rfl

/-- **The star distribution does not ignore them.**  `LocalWalk.starPi` — the
level-`j` distribution of `LocalWalk.starWeightNorm w τ` — gives every `j`-subset
of `τ` itself the mass `1 / n.choose j`.

Together with `linkShiftPi_eq_zero_of_not_disjoint` this is a proof that
`starPi w n j τ ≠ linkShiftPi w n j τ` as soon as `τ` has a nonempty subface of
size `j`, i.e. as soon as `0 < j ≤ |τ|`.  It is recorded because the two are
easily confused: `starPi w n 2 τ` looks like the monograph's `π_{τ,2}` and is
not.  The intuitive reason is that `starWeightNorm w τ` is the complex of *all*
subfaces of the top faces containing `τ` — the star of `τ`, of dimension `n` —
whereas the monograph's link has dimension `n - |τ|`. -/
theorem starPi_apply_of_subset (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hj : j ≤ n) {ρ : Finset E} (hsub : ρ ⊆ τ) (hcard : ρ.card = j) :
    starPi w n j τ hw hsupp hpos hj ρ = 1 / ((n.choose j : ℕ) : ℝ) := by
  rw [starPi_apply, if_pos hcard, Finset.union_eq_left.mpr hsub, ← div_div,
    div_self hpos.ne']

/-! ## The guarded-total link distribution and link projection

`linkShiftPi w n j τ …` needs `0 < mu w τ` and `τ.card + j ≤ n` in its data, so
a `π_k`-average over *all* faces `τ` of a quantity built from it does not
typecheck, even though the offending faces carry no `π_k`-mass.  The two
definitions here remove the obstruction exactly as `LocalWalk.linkDistOf`
does: guard both hypotheses, fall back on a junk value, and record that the
junk is invisible where the real object exists.

Unlike `linkDistOf` neither definition needs a nonemptiness hypothesis: the
state space of `π_{τ,j}` is `Finset E`, which contains `∅` however small `E`
is. -/

/-- The **guarded-total level-`j` link distribution**: `linkShiftPi`
where that is defined, and the point mass at `∅` elsewhere.

Unlike `linkShiftPi` this is a total function of the face `τ`, so it can appear
inside a `π_k`-average.  The junk value is invisible to every statement below,
because a face at which either guard fails has `π_k`-mass `0`. -/
noncomputable def linkShiftPiOf (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) : FinDist (Finset E) where
  p ρ :=
    if h : 0 < mu w τ ∧ τ.card + j ≤ n then
      linkShiftPi w n j τ hw hsupp (by omega) h.1 (by omega) ρ
    else (if ρ = ∅ then 1 else 0)
  p_nonneg ρ := by
    by_cases h : 0 < mu w τ ∧ τ.card + j ≤ n
    · rw [dif_pos h]
      exact (linkShiftPi w n j τ hw hsupp (by omega) h.1 (by omega)).p_nonneg ρ
    · rw [dif_neg h]
      split
      · exact zero_le_one
      · exact le_rfl
  p_sum := by
    by_cases h : 0 < mu w τ ∧ τ.card + j ≤ n
    · simp only [dif_pos h]
      exact (linkShiftPi w n j τ hw hsupp (by omega) h.1 (by omega)).p_sum
    · simp only [dif_neg h]
      simp

/-- The defining formula for `linkShiftPiOf`. -/
theorem linkShiftPiOf_apply (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (ρ : Finset E) :
    linkShiftPiOf w n j τ hw hsupp ρ =
      if h : 0 < mu w τ ∧ τ.card + j ≤ n then
        linkShiftPi w n j τ hw hsupp (by omega) h.1 (by omega) ρ
      else (if ρ = ∅ then 1 else 0) := rfl

/-- **The guard is invisible where `linkShiftPi` is defined.**  At a face of
positive derived weight with room for `j` more levels, the guarded distribution
*is* the monograph's `π_{τ,j}`. -/
theorem linkShiftPiOf_eq_linkShiftPi (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card) :
    linkShiftPiOf w n j τ hw hsupp = linkShiftPi w n j τ hw hsupp hτn hpos hj :=
  FinDist.ext fun ρ => by
    rw [linkShiftPiOf_apply, dif_pos ⟨hpos, by omega⟩]

/-- The **guarded-total link projection** `f_τ^{(j)}`: the level-`j` projection
computed inside the honest link of `τ`, junk-valued `0` when `τ` is too big for
the link to exist.

The guard is only `τ.card ≤ n`, which is all that the link complex
`linkShiftNorm w τ` of dimension `n − |τ|` needs in order to be a weighted
complex; positivity of `mu w τ` is not required for the *function* (only for the
distribution). -/
noncomputable def linkLevelFun (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) : Finset E → ℝ :=
  if h : τ.card ≤ n then
    levelFun (linkShiftNorm w τ) (n - τ.card) (linkShiftNorm_nonneg hw τ)
      (linkShiftNorm_supp hsupp h) (fun σ => f (τ ∪ σ)) j
  else fun _ => 0

/-- In range, the guarded link projection is the projection computed in the
link. -/
theorem linkLevelFun_apply (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ)
    (hτn : τ.card ≤ n) :
    linkLevelFun w n j τ hw hsupp f
      = levelFun (linkShiftNorm w τ) (n - τ.card) (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp hτn) (fun σ => f (τ ∪ σ)) j :=
  dif_pos hτn

/-- **The restriction theorem in guarded form**: for `ρ` disjoint from `τ` of
cardinality `j` and of positive derived weight,

  `f_τ^{(j)}(ρ) = f^{(|τ| + j)}(τ ∪ ρ)`.

This is `levelFun_linkShiftNorm` with the guard put on. -/
theorem linkLevelFun_eq_levelFun (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ)
    (hτn : τ.card ≤ n) {ρ : Finset E} (hd : Disjoint τ ρ) (hcard : ρ.card = j)
    (hpos : 0 < mu w (τ ∪ ρ)) :
    linkLevelFun w n j τ hw hsupp f ρ = levelFun w n hw hsupp f (τ.card + j) (τ ∪ ρ) := by
  rw [linkLevelFun_apply w n j τ hw hsupp f hτn]
  exact levelFun_linkShiftNorm w n j hw hsupp f hτn hd hcard hpos

/-! ## Congruence on the support of `π_{τ,j}`

The guarded projection agrees with the ambient one only on the faces `ρ` that are
disjoint from `τ`, of cardinality `j` and of positive derived weight — which is
exactly the support of `π_{τ,j}`.  These two lemmas let that partial agreement be
used inside an expectation and inside a variance. -/

/-- Two functions agreeing on the support of `π_{τ,j}` have the same
`π_{τ,j}`-average. -/
theorem Ex_linkShiftPi_congr (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card)
    {h₁ h₂ : Finset E → ℝ}
    (h : ∀ ρ : Finset E, ρ.card = j → Disjoint τ ρ → 0 < mu w (τ ∪ ρ) → h₁ ρ = h₂ ρ) :
    Ex (linkShiftPi w n j τ hw hsupp hτn hpos hj) h₁
      = Ex (linkShiftPi w n j τ hw hsupp hτn hpos hj) h₂ := by
  simp only [Ex_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  by_cases hc : ρ.card = j
  · by_cases hd : Disjoint τ ρ
    · by_cases hm : 0 < mu w (τ ∪ ρ)
      · rw [h ρ hc hd hm]
      · have h0 : mu w (τ ∪ ρ) = 0 := le_antisymm (not_lt.mp hm) (mu_nonneg hw _)
        rw [linkShiftPi_apply_of_disjoint w n j τ hw hsupp hτn hpos hj hd, if_pos hc, h0,
          zero_div, zero_mul, zero_mul]
    · rw [linkShiftPi_eq_zero_of_not_disjoint w n j τ hw hsupp hτn hpos hj hd,
        zero_mul, zero_mul]
  · rw [linkShiftPi_eq_zero_of_card_ne w n j τ hw hsupp hτn hpos hj hc, zero_mul, zero_mul]

/-- Two functions agreeing on the support of `π_{τ,j}` have the same
`π_{τ,j}`-variance. -/
theorem Var_linkShiftPi_congr (w : Finset E → ℝ) (n j : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hj : j ≤ n - τ.card)
    {h₁ h₂ : Finset E → ℝ}
    (h : ∀ ρ : Finset E, ρ.card = j → Disjoint τ ρ → 0 < mu w (τ ∪ ρ) → h₁ ρ = h₂ ρ) :
    Var (linkShiftPi w n j τ hw hsupp hτn hpos hj) h₁
      = Var (linkShiftPi w n j τ hw hsupp hτn hpos hj) h₂ := by
  rw [Var_eq_ip_sub_sq, Var_eq_ip_sub_sq, ip_eq_Ex_mul, ip_eq_Ex_mul,
    Ex_linkShiftPi_congr w n j τ hw hsupp hτn hpos hj
      (h₁ := fun ρ => h₁ ρ * h₁ ρ) (h₂ := fun ρ => h₂ ρ * h₂ ρ)
      (fun ρ hc hd hm => by
        show h₁ ρ * h₁ ρ = h₂ ρ * h₂ ρ
        rw [h ρ hc hd hm]),
    Ex_linkShiftPi_congr w n j τ hw hsupp hτn hpos hj h]

/-! ## The one-step identity inside the link

With `linkShiftNorm` established as a weighted complex of dimension `n - |τ|`,
every result of `Techniques.Levels`, `Techniques.LevelVariance` and
`Techniques.LocalToGlobal` applies to the link verbatim.  The one the monograph
needs is `LevelVariance.Var_pi_succ_eq`, at `k = 1`: it relates the level-`2`
variance in the link — the `Var_{π_{τ,2}}` of `claim:first-step` — to the
level-`1` variance and the Dirichlet form of the link's own down-up walk. -/

/-- **The one-step variance identity inside the honest link.**  For every
`k < n - |τ|` and every `g`,

  `Var_{π_{τ,k+1}}(g) = Var_{π_{τ,k}}(U^τ_k g) + ℰ_{P^{∨∧,τ}_k}(g)`.

This is `LevelVariance.Var_pi_succ_eq` applied to `linkShiftNorm w τ`, and it
costs one line: the whole point of the shifted link is that it is again a
weighted complex, so it needs no new theory. -/
theorem Var_linkShiftPi_succ_eq (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (τ : Finset E) (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hk : k < n - τ.card)
    (g : Finset E → ℝ) :
    Var (linkShiftPi w n (k + 1) τ hw hsupp hτn hpos hk) g
      = Var (linkShiftPi w n k τ hw hsupp hτn hpos hk.le)
          ((up (linkShiftNorm w τ) (n - τ.card) k (linkShiftNorm_nonneg hw τ)
            (linkShiftNorm_supp hsupp hτn) hk).act g)
        + dirichlet (linkShiftPi w n (k + 1) τ hw hsupp hτn hpos hk)
            (downUp (linkShiftNorm w τ) (n - τ.card) k (linkShiftNorm_nonneg hw τ)
              (linkShiftNorm_supp hsupp hτn) hk) g g :=
  Var_pi_succ_eq (linkShiftNorm w τ) (n - τ.card) k (linkShiftNorm_nonneg hw τ)
    (linkShiftNorm_supp hsupp hτn) (sum_linkShiftNorm w hpos) hk g

/-- **The two-levels-up identity.**  The case `k = 1` of
`Var_linkShiftPi_succ_eq`:

  `Var_{π_{τ,2}}(g) = Var_{π_{τ,1}}(U^τ_1 g) + ℰ_{P^{∨∧,τ}_1}(g)`.

This is the identity `claim:first-step` and `lem:improved-technical` use inside
the link of a face `τ` at level `k - 1`, with `g = f_τ^{(2)}`; by
`levelFun_linkShiftNorm` that `g` is the restriction of the ambient `f^{(k+1)}`,
and by `levelFun_linkShiftNorm` again its projection `U^τ_1 g` is the
restriction of `f^{(k)}`. -/
theorem Var_linkShiftPi_two_eq (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (τ : Finset E) (hτn : τ.card ≤ n) (hpos : 0 < mu w τ) (hk : 1 < n - τ.card)
    (g : Finset E → ℝ) :
    Var (linkShiftPi w n 2 τ hw hsupp hτn hpos hk) g
      = Var (linkShiftPi w n 1 τ hw hsupp hτn hpos hk.le)
          ((up (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
            (linkShiftNorm_supp hsupp hτn) hk).act g)
        + dirichlet (linkShiftPi w n 2 τ hw hsupp hτn hpos hk)
            (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
              (linkShiftNorm_supp hsupp hτn) hk) g g :=
  Var_linkShiftPi_succ_eq w n 1 hw hsupp τ hτn hpos hk g

/-! ## The left-hand side of `claim:first-step`

The telescoping of `Techniques.LocalToGlobal` already computes the two-level
variance drop that the monograph's `claim:first-step` starts from.  Recorded here
because it is the other half of that claim, and because it is one line. -/

/-- **The two-level variance drop is a sum of two level energies**:

  `Var_{π_{k+2}}(f^{(k+2)}) − Var_{π_k}(f^{(k)}) = ℰ_{P^{∨∧}_{k+1}}(f^{(k+2)}) + ℰ_{P^{∨∧}_k}(f^{(k+1)})`.

This is the left-hand side of the monograph's `claim:first-step` (§6.6, there
written with `k + 1` and `k - 1` in place of `k + 2` and `k`), obtained by
applying the one-step identity `LocalToGlobal.levelVar_succ` twice.  What
`claim:first-step` adds is that this quantity is also the `π_k`-average of the
local variances `Var_{π_{τ,2}}(f_τ^{(2)})`. -/
theorem levelVar_sub_levelVar_eq_add (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k + 1 < n) :
    levelVar w n hw hsupp hsum f (k + 2) - levelVar w n hw hsupp hsum f k
      = levelEnergy w n hw hsupp hsum f (k + 1) + levelEnergy w n hw hsupp hsum f k := by
  rw [levelVar_succ w n (k + 1) hw hsupp hsum f hk,
    levelVar_succ w n k hw hsupp hsum f (by omega)]
  ring

end Fintype

end Arlib.MarkovChains
