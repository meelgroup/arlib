/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spin systems: configurations, Gibbs distributions, local partition functions

Every chain the source monograph is about lives on the same state space: the
configurations `V → S` of a *spin system*, a finite set `V` of sites each
carrying a spin from a finite set `S`, weighted by a nonnegative function
`w : (V → S) → ℝ`.  The Gibbs distribution is `w / Z`, and the single-site
heat-bath update at a site `v` resamples the spin at `v` from the conditional
Gibbs distribution given the rest of the configuration.  This module builds the
combinatorial and arithmetic scaffolding that update needs, so that
`Arlib.MarkovChains.Chains.Glauber` can be about the chain and nothing else.

The one non-obvious ingredient is `Zloc`, the *local* partition function
`∑ s, w (σ with the spin at v set to s)`.  It is the normalising constant of the
conditional distribution at `v`, and the reason detailed balance holds for the
heat-bath update is precisely that `Zloc` depends only on the configuration
*off* `v` (`Zloc_congr_of_agreeOff`): two configurations differing only at `v`
see the same normaliser, so the two sides of the detailed-balance identity
acquire the same denominator and reduce to the symmetric numerator `w σ · w τ`.

* `update` — `Function.update`, with the wrappers this development uses.
* `AgreeOff v σ τ` — `σ` and `τ` agree away from the site `v`; an equivalence
  relation, with **`agreeOff_iff_update`** (`AgreeOff v σ τ ↔ τ = update σ v (τ v)`)
  turning quantification over the neighbours of `σ` into quantification over
  spins.
* `sum_ite_agreeOff` — the resulting reindexing of a sum, which is what makes
  the heat-bath row sum computable.
* `Z`, `gibbs` — the partition function and the Gibbs distribution `w / Z`,
  with `gibbs_apply`, `gibbs_pos_iff`, `gibbs_eq_zero_iff`.
* `Zloc` — the local partition function, with `Zloc_nonneg`,
  **`Zloc_congr_of_agreeOff`**, `w_le_Zloc`, `Zloc_pos_of_w_pos` and the
  contrapositive `w_eq_zero_of_Zloc_eq_zero`.
* `hardCoreWeight` — the hard-core model of the monograph's §1.2 as a weight
  function, together with `Z_hardCoreWeight_pos`, to exhibit the interface in
  use.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDist

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Configurations and single-site updates

A configuration is a function `V → S`.  Changing the spin at one site is
`Function.update`; we give it a name matching the vocabulary of the monograph
and record the rewriting facts used below. -/

section Update

variable {V : Type*} [DecidableEq V] {S : Type*}

/-- The configuration `σ` with the spin at the site `v` replaced by `s`. -/
def update (σ : V → S) (v : V) (s : S) : V → S := Function.update σ v s

@[simp] theorem update_self (σ : V → S) (v : V) (s : S) : update σ v s v = s := by
  simp [update]

theorem update_of_ne {u v : V} (h : u ≠ v) (σ : V → S) (s : S) : update σ v s u = σ u := by
  simp [update, Function.update_of_ne h]

@[simp] theorem update_eq_self (σ : V → S) (v : V) : update σ v (σ v) = σ := by
  simp [update]

@[simp] theorem update_idem (σ : V → S) (v : V) (s t : S) :
    update (update σ v s) v t = update σ v t := by
  simp [update]

/-- Resetting the spin at `v` is injective in the spin: two updates that differ
in the spin already differ at `v`. -/
theorem update_injective (σ : V → S) (v : V) {s t : S} (h : update σ v s = update σ v t) :
    s = t := by
  have := congrFun h v
  simpa using this

end Update

/-! ## Agreement off a site -/

section Agree

variable {V : Type*} {S : Type*}

/-- `σ` and `τ` agree off the site `v`: they may differ at `v` and nowhere else.
This is the relation "`τ` is reachable from `σ` by a single-site update at
`v`". -/
def AgreeOff (v : V) (σ τ : V → S) : Prop := ∀ u, u ≠ v → σ u = τ u

/-- Agreement off a site is reflexive. -/
theorem agreeOff_rfl (v : V) (σ : V → S) : AgreeOff v σ σ := fun _ _ => rfl

/-- Agreement off a site is symmetric. -/
theorem AgreeOff.symm {v : V} {σ τ : V → S} (h : AgreeOff v σ τ) : AgreeOff v τ σ :=
  fun u hu => (h u hu).symm

/-- Agreement off a site is transitive. -/
theorem AgreeOff.trans {v : V} {σ τ ρ : V → S} (h : AgreeOff v σ τ) (h' : AgreeOff v τ ρ) :
    AgreeOff v σ ρ := fun u hu => (h u hu).trans (h' u hu)

/-- Agreement off a site is a symmetric relation. -/
theorem agreeOff_comm {v : V} {σ τ : V → S} : AgreeOff v σ τ ↔ AgreeOff v τ σ :=
  ⟨AgreeOff.symm, AgreeOff.symm⟩

end Agree

section AgreeUpdate

variable {V : Type*} [DecidableEq V] {S : Type*}

/-- A single-site update agrees with the original configuration off that site. -/
theorem agreeOff_update (σ : V → S) (v : V) (s : S) : AgreeOff v σ (update σ v s) :=
  fun _ hu => (update_of_ne hu σ s).symm

/-- **Agreement off `v` is exactly being a single-site update at `v`.**

This is the workhorse of the module: it converts a quantifier over the
configurations agreeing with `σ` off `v` — an unstructured subset of `V → S` —
into a quantifier over the spin set `S`. -/
theorem agreeOff_iff_update {v : V} {σ τ : V → S} :
    AgreeOff v σ τ ↔ τ = update σ v (τ v) := by
  constructor
  · intro h
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · rw [update_of_ne hu]; exact (h u hu).symm
  · intro h u hu
    conv_rhs => rw [h]
    rw [update_of_ne hu]

/-- Two configurations agreeing off `v` have the *same* single-site update at
`v` for each spin. -/
theorem update_congr_of_agreeOff {v : V} {σ τ : V → S} (h : AgreeOff v σ τ) (s : S) :
    update σ v s = update τ v s := by
  funext u
  by_cases hu : u = v
  · subst hu; simp
  · rw [update_of_ne hu, update_of_ne hu]; exact h u hu

end AgreeUpdate

section AgreeSum

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

instance decidableAgreeOff (v : V) (σ τ : V → S) : Decidable (AgreeOff v σ τ) :=
  inferInstanceAs (Decidable (∀ u, u ≠ v → σ u = τ u))

/-- The configurations agreeing with `σ` off `v` are exactly the single-site
updates of `σ` at `v`. -/
theorem filter_agreeOff (v : V) (σ : V → S) :
    (univ.filter fun τ => AgreeOff v σ τ) = univ.image fun s => update σ v s := by
  ext τ
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · intro h; exact ⟨τ v, (agreeOff_iff_update.mp h).symm⟩
  · rintro ⟨s, rfl⟩; exact agreeOff_update σ v s

/-- **Reindexing a sum over the neighbours of `σ` at `v` as a sum over spins.**
This is the identity that makes the heat-bath row sum computable. -/
theorem sum_ite_agreeOff (v : V) (σ : V → S) (g : (V → S) → ℝ) :
    ∑ τ, (if AgreeOff v σ τ then g τ else 0) = ∑ s, g (update σ v s) := by
  rw [← Finset.sum_filter, filter_agreeOff v σ]
  exact Finset.sum_image fun s _ t _ h => update_injective σ v h

end AgreeSum

/-! ## Weights, the partition function, and the Gibbs distribution

A *weight* is any nonnegative `w : (V → S) → ℝ` of positive total mass.
Following the convention of this development the hypotheses live on the lemmas
rather than on the definitions — except in `gibbs`, where the `FinDist` fields
genuinely demand them. -/

section Weights

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- The **partition function** `Z(w) = ∑_σ w(σ)`. -/
def Z (w : (V → S) → ℝ) : ℝ := ∑ σ, w σ

theorem Z_apply (w : (V → S) → ℝ) : Z w = ∑ σ, w σ := rfl

theorem Z_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) : 0 ≤ Z w :=
  Finset.sum_nonneg fun σ _ => hw σ

/-- If some configuration has positive weight then the partition function is
positive.  This is how the standing hypothesis `0 < Z w` is discharged in
practice: exhibit one feasible configuration. -/
theorem Z_pos_of_pos {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) {σ₀ : V → S} (h : 0 < w σ₀) :
    0 < Z w :=
  lt_of_lt_of_le h (Finset.single_le_sum (fun σ _ => hw σ) (mem_univ σ₀))

/-- The **Gibbs distribution** of a weight function: `μ(σ) = w(σ) / Z(w)`. -/
noncomputable def gibbs (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) :
    FinDist (V → S) where
  p σ := w σ / Z w
  p_nonneg σ := div_nonneg (hw σ) hZ.le
  p_sum := by rw [← Finset.sum_div, ← Z_apply, div_self hZ.ne']

@[simp] theorem gibbs_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (σ : V → S) :
    gibbs w hw hZ σ = w σ / Z w := rfl

/-- The Gibbs distribution charges exactly the configurations of positive
weight. -/
theorem gibbs_pos_iff {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (σ : V → S) :
    0 < gibbs w hw hZ σ ↔ 0 < w σ := by
  rw [gibbs_apply, div_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact h
    · exact absurd hZ (not_lt.mpr h.le)
  · intro h; exact Or.inl ⟨h, hZ⟩

/-- The Gibbs distribution vanishes exactly on the configurations of weight
zero. -/
theorem gibbs_eq_zero_iff {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (σ : V → S) :
    gibbs w hw hZ σ = 0 ↔ w σ = 0 := by
  rw [gibbs_apply, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hZ.ne'
  · intro h; exact Or.inl h

/-- Convenience form of `gibbs_eq_zero_iff`. -/
theorem gibbs_eq_zero {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {σ : V → S}
    (h : w σ = 0) : gibbs w hw hZ σ = 0 := (gibbs_eq_zero_iff hw hZ σ).mpr h

end Weights

/-! ## The local partition function

`Zloc w σ v` normalises the conditional Gibbs distribution of the spin at `v`
given the configuration elsewhere.  The two facts that matter downstream are
that it depends only on the configuration off `v`, and that it dominates
`w σ` itself. -/

section Local

variable {V : Type*} [DecidableEq V] {S : Type*} [Fintype S]

/-- The **local partition function** at the site `v`: the total weight of the
configurations obtained from `σ` by resampling the spin at `v`. -/
def Zloc (w : (V → S) → ℝ) (σ : V → S) (v : V) : ℝ := ∑ s, w (update σ v s)

theorem Zloc_apply (w : (V → S) → ℝ) (σ : V → S) (v : V) :
    Zloc w σ v = ∑ s, w (update σ v s) := rfl

theorem Zloc_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (σ : V → S) (v : V) :
    0 ≤ Zloc w σ v := Finset.sum_nonneg fun _ _ => hw _

/-- **The local partition function only sees the configuration off `v`.**

This is the crux of detailed balance for the heat-bath update: `σ` and all of
its resamplings at `v` carry the same normalising constant, so the two sides of
the detailed-balance identity acquire the same denominator. -/
theorem Zloc_congr_of_agreeOff (w : (V → S) → ℝ) {v : V} {σ τ : V → S}
    (h : AgreeOff v σ τ) : Zloc w σ v = Zloc w τ v :=
  Finset.sum_congr rfl fun s _ => by rw [update_congr_of_agreeOff h s]

/-- The weight of `σ` is one of the terms of `Zloc w σ v`, namely the term
`s = σ v`. -/
theorem w_le_Zloc {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (σ : V → S) (v : V) :
    w σ ≤ Zloc w σ v := by
  have h : w σ = w (update σ v (σ v)) := by rw [update_eq_self]
  rw [h, Zloc_apply]
  exact Finset.single_le_sum (fun s _ => hw _) (mem_univ (σ v))

/-- On the support of the Gibbs distribution the local partition function is
positive, so the conditional distribution at `v` is genuinely defined. -/
theorem Zloc_pos_of_w_pos {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) {σ : V → S} (v : V)
    (h : 0 < w σ) : 0 < Zloc w σ v := lt_of_lt_of_le h (w_le_Zloc hw σ v)

/-- Contrapositive form: where the local partition function vanishes the weight
does too.  This is what makes the degenerate branch of the heat-bath update
invisible to the Gibbs measure. -/
theorem w_eq_zero_of_Zloc_eq_zero {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) {σ : V → S} {v : V}
    (h : Zloc w σ v = 0) : w σ = 0 :=
  le_antisymm (h ▸ w_le_Zloc hw σ v) (hw σ)

end Local

/-! ## The running example: the hard-core model

The monograph's §1.2.  Sites are the vertices of a graph, spins are `Bool`
(occupied or unoccupied), a configuration is feasible when no edge has both
endpoints occupied, and a feasible configuration with `k` occupied sites has
weight `λ^k`.  This section exists only to show that the interface above is
instantiable; the chain itself is in `Arlib.MarkovChains.Chains.Glauber`. -/

section HardCore

variable {V : Type*} [Fintype V] (adj : V → V → Prop) [DecidableRel adj]

/-- A configuration is the indicator of an independent set when no edge of `adj`
has both endpoints occupied. -/
def IsIndep (σ : V → Bool) : Prop := ∀ u v, adj u v → ¬(σ u ∧ σ v)

instance decidableIsIndep (σ : V → Bool) : Decidable (IsIndep adj σ) :=
  inferInstanceAs (Decidable (∀ u v, adj u v → ¬(σ u ∧ σ v)))

/-- The number of occupied sites of a configuration. -/
def occupied (σ : V → Bool) : ℕ := (univ.filter fun v => σ v).card

/-- The **hard-core weight** at activity `lam`: `lam ^ |σ|` on independent sets
and `0` elsewhere. -/
noncomputable def hardCoreWeight (lam : ℝ) (σ : V → Bool) : ℝ :=
  if IsIndep adj σ then lam ^ occupied σ else 0

variable {adj}

/-- The hard-core weight is nonnegative for a nonnegative activity. -/
theorem hardCoreWeight_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (σ : V → Bool) :
    0 ≤ hardCoreWeight adj lam σ := by
  rw [hardCoreWeight]
  split
  · exact pow_nonneg hlam _
  · exact le_rfl

/-- The empty independent set is feasible and has weight `1`. -/
@[simp] theorem hardCoreWeight_false (lam : ℝ) :
    hardCoreWeight adj lam (fun _ => false) = 1 := by
  have hindep : IsIndep adj (fun _ : V => false) := by intro u v _; simp
  have hocc : occupied (fun _ : V => false) = 0 := by simp [occupied]
  rw [hardCoreWeight, if_pos hindep, hocc, pow_zero]

/-- **The hard-core model is a spin system.**  Its partition function is
positive — the empty independent set already contributes `1` — so `gibbs`
applies and the Gibbs distribution of the monograph's §1.2 is available. -/
theorem Z_hardCoreWeight_pos [DecidableEq V] {lam : ℝ} (hlam : 0 ≤ lam) :
    0 < Z (hardCoreWeight adj lam) :=
  Z_pos_of_pos (hardCoreWeight_nonneg hlam) (σ₀ := fun _ => false)
    (by rw [hardCoreWeight_false]; norm_num)

end HardCore

end Arlib.MarkovChains
