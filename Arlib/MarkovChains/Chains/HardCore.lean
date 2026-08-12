/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two running examples: the hard-core model and the Ising model

`Chains/SpinSystem.lean` introduces the hard-core model of the monograph's §1.2
as a weight function and proves that its partition function is positive — and
there the thread stops.  Nothing connects it to the chain the monograph is about.
This module ties the knot: it computes the hard-core local partition function in
closed form, reads off the transition probabilities of the Glauber dynamics as
the monograph states them (`λ/(1+λ)` and `1/(1+λ)` at a free vertex, a
deterministic eviction at a blocked one), and then discharges the hypotheses of
`glauber_reversible` and `glauber_nonnegDefinite` so that the general theory is
visibly *applied* to a named model rather than merely applicable.

The same is done for the Ising model, and the two are worth reading side by side
because of a contrast that is invisible in the general theory.  The hard-core
weight vanishes on most configurations, so `0 < Z` has to be *earned* — the
all-empty configuration is exhibited by hand — and consequently every statement
about the chain carries a hypothesis on the activity `λ`, and the degenerate
branch of `siteUpdate` (where `Zloc = 0`) is a live possibility at `λ = 0`.  The
Ising weight is an exponential, hence strictly positive, so `0 < Z` holds with
*no hypotheses at all*, the Gibbs measure is fully supported, and every
conditional law is genuinely defined.  Positivity of the weight, not any deeper
feature, is what separates a "hard" constraint model from a "soft" one.

The third thing this module does is calibration, in the sense of §1.1 of the
roadmap: on a graph with **no edges** the hard-core model degenerates completely,
and everything can be computed outright — the weight is a product over sites, the
partition function is `(1+λ)^n`, the Gibbs measure is the product of Bernoulli
`λ/(1+λ)` measures, and the single-site update draws the new spin at `v` from that
Bernoulli law *whatever the rest of the configuration is*.  In the extreme case of
a single site the update is literally the chain of
`Chains/IndependentSampler.lean`, which is proved here for an arbitrary weight.

## Main declarations

### The hard-core model

* `IndepOff`, `FreeAt` — the two local predicates the update depends on: `σ` is
  independent away from `v`, and every neighbour of `v` is unoccupied (which,
  read at `u = v`, also excludes a self-loop at `v`).
* `isIndep_update_false_iff`, `isIndep_update_true_iff` — feasibility of the two
  resamplings at `v` in terms of those predicates.
* **`Zloc_hardCoreWeight`** — the exact trichotomy for the hard-core local
  partition function: `0`, `λ^k`, or `λ^k·(1+λ)`, where `k = occupiedOff v σ` is
  the number of occupied sites *other than* `v`.
* **`siteUpdate_hardCoreWeight`** — hence the explicit single-site update: at a
  free vertex the new spin is `true` with probability `λ/(1+λ)`, and at a blocked
  vertex it is `false` with probability `1`.  `hardCoreSiteChain_apply` is the
  same statement for the chain.
* **`hardCoreGlauber_reversible`**, **`hardCoreGlauber_nonnegDefinite`** — the
  general theory landing on the model, with all hypotheses discharged.

### Calibration: no edges

* `hardCoreWeight_noEdges_prod`, **`Z_hardCoreWeight_noEdges`** (`= (1+λ)^n`) and
  **`hardCoreGibbs_noEdges`** — the Gibbs measure is a product measure.
* **`siteUpdate_hardCoreWeight_noEdges`** — the law of the new spin at `v` is a
  fixed Bernoulli, independent of `σ`; the update touches nothing else.
* **`siteUpdate_eq_gibbs_of_unique`** — for *any* weight on a one-site spin
  system the single-site update is the independent sampler of
  `Chains/IndependentSampler.lean`.

### The Ising model

* `spin`, `isingEnergy`, `isingWeight`; `isingWeight_pos` and
  **`Z_isingWeight_pos`**, which needs no hypotheses.
* `isingField` — the local field `∑_{u ≠ v} (J u v + J v u) · s(σ u)`, and
  **`isingEnergy_update`**, the affine dependence of the energy on the spin at
  `v`.
* `logistic`, and **`siteUpdate_isingWeight_true`**: the probability of setting
  the spin at `v` to `+1` is `logistic (2 β · isingField)`.
* **`isingGlauber_reversible`**, **`isingGlauber_nonnegDefinite`**, and
  `isingGibbs_pos` (full support).

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Chains.IndependentSampler
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The local structure of the hard-core model

A single-site update at `v` sees the configuration only through two predicates:
whether `σ` violates the independence constraint *away* from `v` (in which case
both resamplings are infeasible and the local partition function vanishes), and
whether `v` is *free*, i.e. all of its neighbours are unoccupied.  Everything in
this section is the translation of `IsIndep` into those two predicates. -/

section LocalDefs

variable {V : Type*}

/-- **`σ` is independent away from `v`**: no edge with *both* endpoints different
from `v` has both endpoints occupied.

This is the part of the hard-core constraint that a resampling at `v` cannot
repair, so it is exactly the condition for `Zloc` to be nonzero. -/
def IndepOff (adj : V → V → Prop) (v : V) (σ : V → Bool) : Prop :=
  ∀ u u', u ≠ v → u' ≠ v → adj u u' → ¬(σ u ∧ σ u')

/-- **`v` is free in `σ`**: every vertex adjacent to `v` (in either direction) is
distinct from `v` and unoccupied.

Reading the definition at `u = v` says `¬ adj v v`: a self-loop at `v` forbids
occupying `v` just as an occupied neighbour does, and folding the two cases
together keeps the statement of `Zloc_hardCoreWeight` a clean trichotomy for an
arbitrary relation `adj`, symmetric or not, loopless or not. -/
def FreeAt (adj : V → V → Prop) (v : V) (σ : V → Bool) : Prop :=
  ∀ u, (adj u v ∨ adj v u) → u ≠ v ∧ σ u = false

/-- An independent configuration is in particular independent away from any
site. -/
theorem IsIndep.indepOff {adj : V → V → Prop} {σ : V → Bool} (h : IsIndep adj σ) (v : V) :
    IndepOff adj v σ :=
  fun u u' _ _ huu' => h u u' huu'

end LocalDefs

section LocalDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {adj : V → V → Prop} [DecidableRel adj]

instance decidableIndepOff (v : V) (σ : V → Bool) : Decidable (IndepOff adj v σ) :=
  inferInstanceAs (Decidable (∀ u u', u ≠ v → u' ≠ v → adj u u' → ¬(σ u ∧ σ u')))

instance decidableFreeAt (v : V) (σ : V → Bool) : Decidable (FreeAt adj v σ) :=
  inferInstanceAs (Decidable (∀ u, (adj u v ∨ adj v u) → u ≠ v ∧ σ u = false))

end LocalDecidable

section LocalUpdate

variable {V : Type*} [DecidableEq V] {adj : V → V → Prop}

/-- **Emptying `v` is feasible exactly when `σ` is independent away from `v`.**
No constraint involving `v` can be violated once `v` is unoccupied. -/
theorem isIndep_update_false_iff (v : V) (σ : V → Bool) :
    IsIndep adj (update σ v false) ↔ IndepOff adj v σ := by
  constructor
  · intro h u u' hu hu' huu' hc
    exact h u u' huu' (by rw [update_of_ne hu, update_of_ne hu']; exact hc)
  · intro h u u' huu' hc
    obtain ⟨h1, h2⟩ := hc
    have hu : u ≠ v := by rintro rfl; simp [update] at h1
    have hu' : u' ≠ v := by rintro rfl; simp [update] at h2
    rw [update_of_ne hu] at h1
    rw [update_of_ne hu'] at h2
    exact h u u' hu hu' huu' ⟨h1, h2⟩

/-- **Occupying `v` is feasible exactly when `σ` is independent away from `v` and
`v` is free.** -/
theorem isIndep_update_true_iff (v : V) (σ : V → Bool) :
    IsIndep adj (update σ v true) ↔ IndepOff adj v σ ∧ FreeAt adj v σ := by
  constructor
  · intro h
    refine ⟨fun u u' hu hu' huu' hc => h u u' huu' ?_, fun u hu => ?_⟩
    · rw [update_of_ne hu, update_of_ne hu']; exact hc
    · have hne : u ≠ v := fun hq => by
        have hvv : adj v v := by rcases hu with h1 | h1 <;> exact hq ▸ h1
        exact h v v hvv ⟨by simp, by simp⟩
      refine ⟨hne, ?_⟩
      by_contra hcon
      have hut : σ u = true := by
        cases hb : σ u
        · exact absurd hb hcon
        · rfl
      rcases hu with h1 | h1
      · exact h u v h1 ⟨by rw [update_of_ne hne]; exact hut, by simp⟩
      · exact h v u h1 ⟨by simp, by rw [update_of_ne hne]; exact hut⟩
  · rintro ⟨h1, h2⟩ u u' huu' hc
    obtain ⟨ha, hb⟩ := hc
    by_cases hu : u = v
    · obtain ⟨hne, hz⟩ := h2 u' (Or.inr (hu ▸ huu'))
      rw [update_of_ne hne] at hb
      rw [hz] at hb
      exact absurd hb (by simp)
    · by_cases hu' : u' = v
      · obtain ⟨hne, hz⟩ := h2 u (Or.inl (hu' ▸ huu'))
        rw [update_of_ne hne] at ha
        rw [hz] at ha
        exact absurd ha (by simp)
      · rw [update_of_ne hu] at ha
        rw [update_of_ne hu'] at hb
        exact h1 u u' hu hu' huu' ⟨ha, hb⟩

end LocalUpdate

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of occupied sites **other than `v`**.  This is the exponent that
appears in every branch of the hard-core local partition function. -/
def occupiedOff (v : V) (σ : V → Bool) : ℕ := (univ.filter fun u => u ≠ v ∧ σ u).card

/-- Emptying `v` leaves exactly the sites occupied away from `v`. -/
theorem occupied_update_false (v : V) (σ : V → Bool) :
    occupied (update σ v false) = occupiedOff v σ := by
  refine congrArg Finset.card (Finset.ext fun u => ?_)
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hne : u ≠ v := by
      intro hq
      rw [hq, update_self] at h
      exact absurd h (by simp)
    exact ⟨hne, by rwa [update_of_ne hne] at h⟩
  · rintro ⟨hne, h⟩
    rwa [update_of_ne hne]

/-- Occupying `v` adds exactly one to the count. -/
theorem occupied_update_true (v : V) (σ : V → Bool) :
    occupied (update σ v true) = occupiedOff v σ + 1 := by
  have hins : (univ.filter fun u => update σ v true u)
      = insert v (univ.filter fun u => u ≠ v ∧ σ u) := by
    refine Finset.ext fun u => ?_
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      by_cases hne : u = v
      · exact Or.inl hne
      · exact Or.inr ⟨hne, by rwa [update_of_ne hne] at h⟩
    · rintro (rfl | ⟨hne, h⟩)
      · simp
      · rwa [update_of_ne hne]
  have hnot : v ∉ (univ.filter fun u => u ≠ v ∧ σ u) := by simp
  rw [occupied, hins, Finset.card_insert_of_notMem hnot, occupiedOff]

end Counting

/-! ## The local partition function of the hard-core model

The trichotomy below is the computational heart of the module.  Note that the
`1 + λ` of the informal description is only the *last factor*: the local
partition function also carries the weight `λ^k` of the `k` sites occupied away
from `v`, which is common to both resamplings.  That common factor cancels in the
transition probabilities, which is why the informal description is right about
the chain and wrong about `Zloc`. -/

section HardCoreZloc

variable {V : Type*} [Fintype V] [DecidableEq V] {adj : V → V → Prop} [DecidableRel adj]

/-- **The hard-core local partition function, in closed form.**

With `k = occupiedOff v σ` the number of occupied sites other than `v`:

* if `σ` already violates independence away from `v`, both resamplings are
  infeasible and `Zloc = 0`;
* if `σ` is independent away from `v` but `v` is blocked — some neighbour of `v`
  is occupied, or `adj` has a self-loop at `v` — only the empty resampling
  survives and `Zloc = λ^k`;
* if in addition `v` is free, both resamplings survive and
  `Zloc = λ^k + λ^{k+1} = λ^k (1 + λ)`.

No hypothesis on `λ` is needed: this is an identity of the definitions. -/
theorem Zloc_hardCoreWeight (lam : ℝ) (σ : V → Bool) (v : V) :
    Zloc (hardCoreWeight adj lam) σ v
      = if IndepOff adj v σ then
          (if FreeAt adj v σ then lam ^ occupiedOff v σ * (1 + lam)
            else lam ^ occupiedOff v σ)
        else 0 := by
  simp only [Zloc_apply, Fintype.sum_bool, hardCoreWeight]
  by_cases h1 : IndepOff adj v σ
  · rw [if_pos h1, if_pos ((isIndep_update_false_iff v σ).mpr h1), occupied_update_false]
    by_cases h2 : FreeAt adj v σ
    · rw [if_pos h2, if_pos ((isIndep_update_true_iff v σ).mpr ⟨h1, h2⟩),
        occupied_update_true, pow_succ]
      ring
    · rw [if_neg h2, if_neg fun hh => h2 ((isIndep_update_true_iff v σ).mp hh).2]
      ring
  · rw [if_neg h1, if_neg fun hh => h1 ((isIndep_update_false_iff v σ).mp hh),
      if_neg fun hh => h1 ((isIndep_update_true_iff v σ).mp hh).1]
    ring

/-- At a positive activity the hard-core local partition function is positive as
soon as `σ` is independent away from `v` — in particular at every configuration
the Gibbs measure charges.  So the degenerate branch of `siteUpdate` is unreachable
on the support, and the chain below is the honest heat-bath update. -/
theorem Zloc_hardCoreWeight_pos {lam : ℝ} (hlam : 0 < lam) {v : V} {σ : V → Bool}
    (h : IndepOff adj v σ) : 0 < Zloc (hardCoreWeight adj lam) σ v := by
  rw [Zloc_hardCoreWeight, if_pos h]
  split
  · exact mul_pos (pow_pos hlam _) (by linarith)
  · exact pow_pos hlam _

end HardCoreZloc

/-! ## The explicit single-site update

The monograph's §1.2 describes the Glauber dynamics for the hard-core model
operationally: propose to occupy `v` with probability `λ/(1+λ)` and to empty it
with probability `1/(1+λ)`, and reject a proposal that breaks independence.  The
heat-bath update built in `Chains/Glauber.lean` from `Zloc` is exactly that, and
the lemmas below say so. -/

section HardCoreUpdate

variable {V : Type*} [Fintype V] [DecidableEq V] {adj : V → V → Prop} [DecidableRel adj]

/-- Occupying `v`: probability `λ/(1+λ)` at a free vertex, `0` at a blocked
one. -/
theorem siteUpdate_hardCoreWeight_true {lam : ℝ} (hlam : 0 < lam) (v : V) {σ : V → Bool}
    (h : IndepOff adj v σ) :
    siteUpdate (hardCoreWeight adj lam) v σ (update σ v true)
      = if FreeAt adj v σ then lam / (1 + lam) else 0 := by
  have hz := Zloc_hardCoreWeight_pos hlam h
  have hk : (lam : ℝ) ^ occupiedOff v σ ≠ 0 := (pow_pos hlam _).ne'
  have h1l : (1 : ℝ) + lam ≠ 0 := by positivity
  rw [siteUpdate_of_Zloc_ne_zero hz.ne', if_pos (agreeOff_update σ v true),
    Zloc_hardCoreWeight, if_pos h, hardCoreWeight]
  by_cases h2 : FreeAt adj v σ
  · rw [if_pos h2, if_pos h2, if_pos ((isIndep_update_true_iff v σ).mpr ⟨h, h2⟩),
      occupied_update_true, pow_succ]
    rw [mul_comm ((lam : ℝ) ^ occupiedOff v σ) lam,
      mul_comm ((lam : ℝ) ^ occupiedOff v σ) (1 + lam)]
    field_simp
  · rw [if_neg h2, if_neg h2, if_neg fun hh => h2 ((isIndep_update_true_iff v σ).mp hh).2,
      zero_div]

/-- Emptying `v`: probability `1/(1+λ)` at a free vertex, `1` at a blocked one. -/
theorem siteUpdate_hardCoreWeight_false {lam : ℝ} (hlam : 0 < lam) (v : V) {σ : V → Bool}
    (h : IndepOff adj v σ) :
    siteUpdate (hardCoreWeight adj lam) v σ (update σ v false)
      = if FreeAt adj v σ then 1 / (1 + lam) else 1 := by
  have hz := Zloc_hardCoreWeight_pos hlam h
  have hk : (lam : ℝ) ^ occupiedOff v σ ≠ 0 := (pow_pos hlam _).ne'
  have h1l : (1 : ℝ) + lam ≠ 0 := by positivity
  rw [siteUpdate_of_Zloc_ne_zero hz.ne', if_pos (agreeOff_update σ v false),
    Zloc_hardCoreWeight, if_pos h, hardCoreWeight,
    if_pos ((isIndep_update_false_iff v σ).mpr h), occupied_update_false]
  by_cases h2 : FreeAt adj v σ
  · rw [if_pos h2, if_pos h2]
    field_simp
  · rw [if_neg h2, if_neg h2, div_self hk]

/-- **The hard-core single-site update, in full.**

From a configuration `σ` that is independent away from `v`, the update at `v`
leaves every other site alone and sets the spin at `v` to `true` with probability
`λ/(1+λ)` if `v` is free, and to `false` otherwise.  This is exactly the chain of
the monograph's §1.2, including the "reject the proposal" clause: at a blocked
vertex the proposal to occupy is rejected and `v` stays empty with probability
`1`. -/
theorem siteUpdate_hardCoreWeight {lam : ℝ} (hlam : 0 < lam) (v : V) {σ : V → Bool}
    (h : IndepOff adj v σ) (τ : V → Bool) :
    siteUpdate (hardCoreWeight adj lam) v σ τ
      = if AgreeOff v σ τ then
          (if τ v then (if FreeAt adj v σ then lam / (1 + lam) else 0)
            else (if FreeAt adj v σ then 1 / (1 + lam) else 1))
        else 0 := by
  by_cases hA : AgreeOff v σ τ
  · rw [if_pos hA]
    have hτ : τ = update σ v (τ v) := agreeOff_iff_update.mp hA
    cases hb : τ v
    · rw [if_neg (by simp)]
      rw [hτ, hb]
      exact siteUpdate_hardCoreWeight_false hlam v h
    · rw [if_pos (by simp)]
      rw [hτ, hb]
      exact siteUpdate_hardCoreWeight_true hlam v h
  · have hz := Zloc_hardCoreWeight_pos hlam h
    rw [siteUpdate_of_Zloc_ne_zero hz.ne', if_neg hA, if_neg hA]

end HardCoreUpdate

/-! ## The general theory, landed on the hard-core model

Nothing below is deep: the point is that `glauber_reversible` and
`glauber_nonnegDefinite` are *applicable*, and that their hypotheses — a
nonnegative weight of positive total mass — are discharged by the two facts
already proved in `Chains/SpinSystem.lean`. -/

section HardCoreChain

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **hard-core Gibbs distribution** at activity `λ ≥ 0`: the uniform measure
on independent sets weighted by `λ^{|σ|}`. -/
noncomputable def hardCoreGibbs (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) : FinDist (V → Bool) :=
  gibbs (hardCoreWeight adj lam) (hardCoreWeight_nonneg hlam) (Z_hardCoreWeight_pos hlam)

@[simp] theorem hardCoreGibbs_apply (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) (σ : V → Bool) :
    hardCoreGibbs adj hlam σ = hardCoreWeight adj lam σ / Z (hardCoreWeight adj lam) := rfl

/-- The **hard-core single-site heat-bath update** at the site `v`. -/
noncomputable def hardCoreSiteChain (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) (v : V) : FinChain (V → Bool) :=
  siteChain (hardCoreWeight adj lam) (hardCoreWeight_nonneg hlam) v

/-- **The hard-core heat-bath update, as a chain.**  The restatement of
`siteUpdate_hardCoreWeight` for `hardCoreSiteChain`; this is the row of the
transition matrix of the monograph's §1.2. -/
theorem hardCoreSiteChain_apply {adj : V → V → Prop} [DecidableRel adj] {lam : ℝ}
    (hlam : 0 < lam) (v : V) {σ : V → Bool} (h : IndepOff adj v σ) (τ : V → Bool) :
    hardCoreSiteChain adj hlam.le v σ τ
      = if AgreeOff v σ τ then
          (if τ v then (if FreeAt adj v σ then lam / (1 + lam) else 0)
            else (if FreeAt adj v σ then 1 / (1 + lam) else 1))
        else 0 :=
  siteUpdate_hardCoreWeight hlam v h τ

/-- **The hard-core heat-bath update is reversible** with respect to the
hard-core Gibbs distribution. -/
theorem hardCoreSiteChain_reversible (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) (v : V) :
    Reversible (hardCoreGibbs adj hlam) (hardCoreSiteChain adj hlam v) :=
  siteChain_reversible _ _ _ v

/-- **The hard-core heat-bath update is positive semidefinite.** -/
theorem hardCoreSiteChain_nonnegDefinite (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) (v : V) :
    NonnegDefinite (hardCoreGibbs adj hlam) (hardCoreSiteChain adj hlam v) :=
  siteChain_nonnegDefinite _ _ _ v

section Dynamics

variable [Nonempty V]

/-- The **hard-core Glauber dynamics**: pick a vertex uniformly at random and
perform the heat-bath update there. -/
noncomputable def hardCoreGlauber (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) : FinChain (V → Bool) :=
  glauber (hardCoreWeight adj lam) (hardCoreWeight_nonneg hlam)

/-- **The hard-core Glauber dynamics is reversible with respect to the hard-core
Gibbs distribution.**  The general `glauber_reversible` with its two hypotheses
discharged: nonnegativity of `λ^{|σ|}`, and positivity of `Z` from the all-empty
independent set. -/
theorem hardCoreGlauber_reversible (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Reversible (hardCoreGibbs adj hlam) (hardCoreGlauber adj hlam) :=
  glauber_reversible _ _ _

/-- The hard-core Gibbs distribution is stationary for the hard-core Glauber
dynamics. -/
theorem hardCoreGlauber_stationary (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Stationary (hardCoreGibbs adj hlam) (hardCoreGlauber adj hlam) :=
  glauber_stationary _ _ _

/-- **The hard-core Glauber dynamics is positive semidefinite.**  With a Poincaré
inequality this is what upgrades a spectral gap to an *absolute* spectral bound,
and hence what makes the gap control the mixing time via
`mixesWithin_lazy_of_gap`. -/
theorem hardCoreGlauber_nonnegDefinite (adj : V → V → Prop) [DecidableRel adj] {lam : ℝ}
    (hlam : 0 ≤ lam) :
    NonnegDefinite (hardCoreGibbs adj hlam) (hardCoreGlauber adj hlam) :=
  glauber_nonnegDefinite _ _ _

end Dynamics

end HardCoreChain

/-! ## Calibration: the hard-core model with no edges

`Chains/` earns its place by checking the general machinery against chains that
can be computed exactly, and the empty graph is the case where the hard-core
model can be computed completely.  Every configuration is independent, so the
constraint disappears, the weight factorises over sites, `Z = (1+λ)^n`, and the
Gibbs distribution is a product of independent Bernoulli `λ/(1+λ)` measures.
Correspondingly the single-site update at `v` resamples the spin at `v` from that
Bernoulli measure *ignoring the current configuration altogether*, which is the
independent-sampler behaviour of `Chains/IndependentSampler.lean` restricted to
one coordinate. -/

/-- The empty graph on `V`. -/
def noEdges (V : Type*) : V → V → Prop := fun _ _ => False

section NoEdgesLocal

variable {V : Type*}

instance decidableNoEdges : DecidableRel (noEdges V) := fun _ _ => Decidable.isFalse id

/-- With no edges every configuration is independent. -/
theorem isIndep_noEdges (σ : V → Bool) : IsIndep (noEdges V) σ := fun _ _ h => h.elim

/-- With no edges every configuration is independent away from every site. -/
theorem indepOff_noEdges (v : V) (σ : V → Bool) : IndepOff (noEdges V) v σ :=
  fun _ _ _ _ h => h.elim

/-- With no edges every site is free in every configuration. -/
theorem freeAt_noEdges (v : V) (σ : V → Bool) : FreeAt (noEdges V) v σ := by
  rintro u (h | h) <;> exact h.elim

end NoEdgesLocal

section NoEdgesWeight

variable {V : Type*} [Fintype V]

/-- With no edges the constraint disappears and the weight is just `λ^{|σ|}`. -/
theorem hardCoreWeight_noEdges (lam : ℝ) (σ : V → Bool) :
    hardCoreWeight (noEdges V) lam σ = lam ^ occupied σ :=
  if_pos (isIndep_noEdges σ)

/-- **The weight factorises over sites**: `λ^{|σ|} = ∏_v (λ if σ v else 1)`.  This
is the statement that the empty-graph hard-core model is a product model. -/
theorem hardCoreWeight_noEdges_prod (lam : ℝ) (σ : V → Bool) :
    hardCoreWeight (noEdges V) lam σ = ∏ u, (if σ u then lam else 1) := by
  rw [hardCoreWeight_noEdges, ← Finset.prod_filter, Finset.prod_const, occupied]

end NoEdgesWeight

section NoEdges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The partition function of the empty graph is `(1+λ)^n`.**  A sum over `2^n`
configurations collapses to a product of `n` two-term sums. -/
theorem Z_hardCoreWeight_noEdges (lam : ℝ) :
    Z (hardCoreWeight (noEdges V) lam) = (1 + lam) ^ Fintype.card V := by
  have hprod : ∀ σ : V → Bool,
      hardCoreWeight (noEdges V) lam σ
        = ∏ u : V, (fun (_ : V) (b : Bool) => if b then lam else 1) u (σ u) :=
    hardCoreWeight_noEdges_prod lam
  rw [Z_apply, Finset.sum_congr rfl fun σ _ => hprod σ,
    ← Fintype.prod_sum (fun (_ : V) (b : Bool) => if b then lam else 1)]
  have hcell : ∀ _u : V, (∑ b : Bool, if b then lam else 1) = 1 + lam := by
    intro _u
    rw [Fintype.sum_bool]
    norm_num
    ring
  rw [Finset.prod_congr rfl fun u _ => hcell u, Finset.prod_const, Finset.card_univ]

/-- **The empty-graph hard-core Gibbs measure is a product measure**: each site is
independently occupied with probability `λ/(1+λ)`.  This is the exact answer the
general theory has to be consistent with. -/
theorem hardCoreGibbs_noEdges {lam : ℝ} (hlam : 0 ≤ lam) (σ : V → Bool) :
    hardCoreGibbs (noEdges V) hlam σ
      = ∏ u, (if σ u then lam / (1 + lam) else 1 / (1 + lam)) := by
  have hcell : ∀ u : V, (if σ u then lam / (1 + lam) else 1 / (1 + lam))
      = (if σ u then lam else 1) / (1 + lam) := by
    intro u; cases σ u <;> simp
  rw [hardCoreGibbs_apply, hardCoreWeight_noEdges_prod, Z_hardCoreWeight_noEdges,
    Finset.prod_congr rfl fun u _ => hcell u, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]

/-- **The empty-graph local partition function is `λ^k (1 + λ)` unconditionally**,
the constraint branch of `Zloc_hardCoreWeight` being unreachable. -/
theorem Zloc_hardCoreWeight_noEdges (lam : ℝ) (σ : V → Bool) (v : V) :
    Zloc (hardCoreWeight (noEdges V) lam) σ v = lam ^ occupiedOff v σ * (1 + lam) := by
  rw [Zloc_hardCoreWeight, if_pos (indepOff_noEdges v σ), if_pos (freeAt_noEdges v σ)]

/-- **The empty-graph single-site update ignores the configuration.**

From any `σ`, the update at `v` keeps the other sites and sets the spin at `v` to
`true` with probability `λ/(1+λ)` and to `false` with probability `1/(1+λ)` — the
same Bernoulli law whatever `σ` is.  In the language of
`Chains/IndependentSampler.lean` this says that in the `v` coordinate the chain
*is* an independent sampler; the general theory's slack, if any, has to show up
somewhere other than here. -/
theorem siteUpdate_hardCoreWeight_noEdges {lam : ℝ} (hlam : 0 < lam) (v : V)
    (σ τ : V → Bool) :
    siteUpdate (hardCoreWeight (noEdges V) lam) v σ τ
      = if AgreeOff v σ τ then (if τ v then lam / (1 + lam) else 1 / (1 + lam)) else 0 := by
  rw [siteUpdate_hardCoreWeight hlam v (indepOff_noEdges v σ) τ,
    if_pos (freeAt_noEdges v σ), if_pos (freeAt_noEdges v σ)]

end NoEdges

/-! ## A one-site spin system is an independent sampler

The extreme degeneration.  On a spin system with a single site there is nothing
to condition on, so the conditional law at `v` is the Gibbs measure itself and
the heat-bath update redraws the whole configuration from `μ` in one step.  That
chain is exactly `independentSampler` of `Chains/IndependentSampler.lean`, whose
Dirichlet form is the variance and whose Poincaré constant is `1`.  The statement
holds for an arbitrary weight — the hard-core model on a one-vertex graph is a
special case. -/

section OneSiteUpdate

variable {V : Type*} [DecidableEq V] [Unique V] {S : Type*}

/-- On a one-site spin system every configuration is a constant function. -/
theorem update_eq_const_of_unique (σ : V → S) (v : V) (s : S) :
    update σ v s = fun _ => s := by
  funext u
  rw [Subsingleton.elim u v, update_self]

end OneSiteUpdate

section OneSiteZloc

variable {V : Type*} [Fintype V] [DecidableEq V] [Unique V]
variable {S : Type*} [Fintype S]

/-- On a one-site spin system the local partition function at `v` is the global
partition function: resampling the single site explores all of `V → S`. -/
theorem Zloc_eq_Z_of_unique (w : (V → S) → ℝ) (σ : V → S) (v : V) : Zloc w σ v = Z w := by
  rw [Zloc_apply, Z_apply]
  refine (Fintype.sum_equiv (Equiv.funUnique V S) w (fun s => w (update σ v s)) fun τ => ?_).symm
  have hτ : update σ v ((Equiv.funUnique V S) τ) = τ := by
    funext u
    rw [update_eq_const_of_unique σ v ((Equiv.funUnique V S) τ)]
    exact congrArg τ (Subsingleton.elim default u)
  exact (congrArg w hτ).symm

end OneSiteZloc

section OneSite

variable {V : Type*} [Fintype V] [DecidableEq V] [Unique V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **On a one-site spin system the single-site update is the independent
sampler.**  Every row of the transition matrix is the Gibbs distribution itself,
so the chain mixes in one step and its Poincaré constant is exactly `1`
(`independentSampler_spectralGapAtLeast`). -/
theorem siteUpdate_eq_gibbs_of_unique (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (σ τ : V → S) :
    siteUpdate w v σ τ = independentSampler (gibbs w hw hZ) σ τ := by
  have hz : Zloc w σ v ≠ 0 := by rw [Zloc_eq_Z_of_unique]; exact hZ.ne'
  have hA : AgreeOff v σ τ := fun u hu => absurd (Subsingleton.elim u v) hu
  rw [siteUpdate_of_Zloc_ne_zero hz, if_pos hA, Zloc_eq_Z_of_unique]
  rfl

end OneSite

/-! ## The Ising model

Spins are `±1`, encoded as `Bool` with `spin true = 1` and `spin false = -1`, and
the weight of a configuration is `exp(β ∑_{u,v} J(u,v) s(σ u) s(σ v))`.  The
double sum runs over *all* ordered pairs, including `u = v`; the diagonal
contributes the constant `∑_v J(v,v)` because `s(σ v)² = 1`, so it is invisible
to the Gibbs measure, and the ordered sum counts each unordered pair twice, which
is why the local field below carries `J u v + J v u` rather than `J v u`.

The contrast with the hard-core model is the point.  `Real.exp` is strictly
positive, so the weight is positive with no hypotheses whatsoever: `0 < Z`
requires no feasible configuration to be exhibited, the Gibbs measure is fully
supported, `Zloc` never vanishes, and the degenerate branch of `siteUpdate` is
unreachable everywhere rather than merely off the support. -/

/-- The spin value of a Boolean label: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem spin_true : spin true = 1 := rfl

@[simp] theorem spin_false : spin false = -1 := rfl

/-- A spin squares to `1`.  This is the only algebraic property of `spin` used
below, and it is what makes the energy *affine* in each individual spin. -/
@[simp] theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num

section IsingWeight

variable {V : Type*} [Fintype V]

/-- The **Ising energy** `∑_u ∑_v J(u,v) s(σ u) s(σ v)`, the ordered double sum. -/
def isingEnergy (J : V → V → ℝ) (σ : V → Bool) : ℝ :=
  ∑ u, ∑ u', J u u' * spin (σ u) * spin (σ u')

/-- The **Ising weight** at inverse temperature `β`: `exp(β · H(σ))`. -/
noncomputable def isingWeight (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (beta * isingEnergy J σ)

/-- **The Ising weight is strictly positive**, for every `J`, `β` and `σ`.  This
one line is the entire difference between a soft and a hard constraint model. -/
theorem isingWeight_pos (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) :
    0 < isingWeight J beta σ := Real.exp_pos _

theorem isingWeight_nonneg (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) :
    0 ≤ isingWeight J beta σ := (isingWeight_pos J beta σ).le

end IsingWeight

section Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The Ising partition function is positive, with no hypotheses at all.**
Compare `Z_hardCoreWeight_pos`, which has to exhibit the all-empty independent
set and needs `0 ≤ λ`. -/
theorem Z_isingWeight_pos (J : V → V → ℝ) (beta : ℝ) : 0 < Z (isingWeight J beta) :=
  Z_pos_of_pos (isingWeight_nonneg J beta) (σ₀ := fun _ => false) (isingWeight_pos J beta _)

/-- The **local field** at `v`: `∑_{u ≠ v} (J(u,v) + J(v,u)) s(σ u)`.  Both
orientations appear because the energy sums over ordered pairs; for a symmetric
coupling this is `2 ∑_{u ≠ v} J(v,u) s(σ u)` (`isingField_of_symm`). -/
def isingField (J : V → V → ℝ) (v : V) (σ : V → Bool) : ℝ :=
  ∑ u ∈ univ.erase v, (J u v + J v u) * spin (σ u)

/-- The part of the energy that does not involve `v` at all. -/
def isingRest (J : V → V → ℝ) (v : V) (σ : V → Bool) : ℝ :=
  ∑ u ∈ univ.erase v, ∑ u' ∈ univ.erase v, J u u' * spin (σ u) * spin (σ u')

/-- For a symmetric coupling the local field is twice the naive one. -/
theorem isingField_of_symm {J : V → V → ℝ} (hJ : ∀ u u', J u u' = J u' u) (v : V)
    (σ : V → Bool) :
    isingField J v σ = 2 * ∑ u ∈ univ.erase v, J v u * spin (σ u) := by
  rw [isingField, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [hJ u v]; ring

/-- Neither the local field nor the rest energy sees the spin at `v`. -/
@[simp] theorem isingField_update (J : V → V → ℝ) (v : V) (σ : V → Bool) (s : Bool) :
    isingField J v (update σ v s) = isingField J v σ :=
  Finset.sum_congr rfl fun u hu => by rw [update_of_ne (Finset.mem_erase.mp hu).1]

@[simp] theorem isingRest_update (J : V → V → ℝ) (v : V) (σ : V → Bool) (s : Bool) :
    isingRest J v (update σ v s) = isingRest J v σ :=
  Finset.sum_congr rfl fun u hu =>
    Finset.sum_congr rfl fun u' hu' => by
      rw [update_of_ne (Finset.mem_erase.mp hu).1, update_of_ne (Finset.mem_erase.mp hu').1]

/-- **The Ising energy is affine in the spin at `v`.**

`H(σ^{v←s}) = R + J(v,v) + s(s)·F`, where `R = isingRest` and `F = isingField`
depend only on the configuration off `v`.  Everything about the single-site
update follows from this identity, and it is the only place the double sum is
actually taken apart. -/
theorem isingEnergy_update (J : V → V → ℝ) (v : V) (σ : V → Bool) (s : Bool) :
    isingEnergy J (update σ v s)
      = isingRest J v σ + J v v + spin s * isingField J v σ := by
  have hv : update σ v s v = s := update_self σ v s
  have hoff : ∀ u ∈ univ.erase v, update σ v s u = σ u := fun u hu =>
    update_of_ne (Finset.mem_erase.mp hu).1 σ s
  -- Split the inner sum at `u' = v`, for every `u`.
  have hinner : ∀ u : V, ∑ u', J u u' * spin (update σ v s u) * spin (update σ v s u')
      = J u v * spin (update σ v s u) * spin s
        + ∑ u' ∈ univ.erase v, J u u' * spin (update σ v s u) * spin (σ u') := by
    intro u
    rw [← Finset.add_sum_erase univ
      (fun u' => J u u' * spin (update σ v s u) * spin (update σ v s u')) (mem_univ v), hv]
    congr 1
    exact Finset.sum_congr rfl fun u' hu' => by rw [hoff u' hu']
  -- Split the outer sum at `u = v`.
  have houter : isingEnergy J (update σ v s)
      = (∑ u', J v u' * spin (update σ v s v) * spin (update σ v s u'))
        + ∑ u ∈ univ.erase v, ∑ u', J u u' * spin (update σ v s u) * spin (update σ v s u') := by
    rw [isingEnergy]
    exact (Finset.add_sum_erase univ
      (fun u => ∑ u', J u u' * spin (update σ v s u) * spin (update σ v s u'))
      (mem_univ v)).symm
  -- The diagonal block.
  have hdiag : (∑ u', J v u' * spin (update σ v s v) * spin (update σ v s u'))
      = J v v + spin s * ∑ u ∈ univ.erase v, J v u * spin (σ u) := by
    rw [hinner v, hv, Finset.mul_sum]
    have hs : spin s * spin s = 1 := spin_mul_self s
    rw [Finset.sum_congr rfl fun u _ =>
      (by ring : J v u * spin s * spin (σ u) = spin s * (J v u * spin (σ u)))]
    linear_combination J v v * hs
  -- The off-diagonal block.
  have hrow : ∑ u ∈ univ.erase v, ∑ u', J u u' * spin (update σ v s u) * spin (update σ v s u')
      = spin s * (∑ u ∈ univ.erase v, J u v * spin (σ u)) + isingRest J v σ := by
    rw [Finset.sum_congr rfl fun u hu => by
      rw [hinner u, hoff u hu], Finset.sum_add_distrib, isingRest, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  -- The local field is the sum of the two orientations.
  have hfield : isingField J v σ
      = (∑ u ∈ univ.erase v, J u v * spin (σ u))
        + ∑ u ∈ univ.erase v, J v u * spin (σ u) := by
    rw [isingField, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [houter, hdiag, hrow, hfield]
  ring

/-! ### The logistic form of the update -/

/-- The **logistic function** `x ↦ 1/(1 + e^{-x})`. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem logistic_apply (x : ℝ) : logistic x = 1 / (1 + Real.exp (-x)) := rfl

/-- The two branches of a two-point Gibbs law add to `1`. -/
theorem logistic_add_logistic_neg (x : ℝ) : logistic x + logistic (-x) = 1 := by
  have h0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have h1 : (1 : ℝ) + Real.exp x ≠ 0 := by positivity
  have h2 : (1 : ℝ) + (Real.exp x)⁻¹ ≠ 0 := by positivity
  rw [logistic, logistic, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- The identity that turns a two-point Gibbs law into a logistic function:
`e^y / (e^y + e^{-y}) = logistic (2y)`. -/
theorem exp_div_add_exp_neg (y : ℝ) :
    Real.exp y / (Real.exp y + Real.exp (-y)) = logistic (2 * y) := by
  have h0 : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have h2 : Real.exp (-(2 * y)) = (Real.exp y)⁻¹ * (Real.exp y)⁻¹ := by
    rw [show -(2 * y) = -y + -y by ring, Real.exp_add, Real.exp_neg]
  rw [logistic, h2, Real.exp_neg]
  field_simp

/-- The Ising local partition function, factored.  The common factor
`exp(β(R + J(v,v)))` cancels in the transition probabilities, exactly as `λ^k`
does in the hard-core model. -/
theorem Zloc_isingWeight (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) (v : V) :
    Zloc (isingWeight J beta) σ v
      = Real.exp (beta * (isingRest J v σ + J v v))
        * (Real.exp (beta * isingField J v σ) + Real.exp (-(beta * isingField J v σ))) := by
  simp only [Zloc_apply, Fintype.sum_bool, isingWeight, isingEnergy_update, spin_true, spin_false]
  rw [show beta * (isingRest J v σ + J v v + 1 * isingField J v σ)
      = beta * (isingRest J v σ + J v v) + beta * isingField J v σ by ring,
    show beta * (isingRest J v σ + J v v + -1 * isingField J v σ)
      = beta * (isingRest J v σ + J v v) + -(beta * isingField J v σ) by ring,
    Real.exp_add, Real.exp_add]
  ring

theorem Zloc_isingWeight_pos (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) (v : V) :
    0 < Zloc (isingWeight J beta) σ v := by
  rw [Zloc_isingWeight]; positivity

/-- **The Ising single-site update, in logistic form.**

From `σ`, the heat-bath update at `v` sets the spin at `v` to `+1` with
probability `logistic (2 β h_v(σ))`, where `h_v(σ) = ∑_{u ≠ v} (J(u,v)+J(v,u))
s(σ u)` is the local field at `v`.  No hypothesis is needed: the Ising weight is
positive everywhere. -/
theorem siteUpdate_isingWeight_true (J : V → V → ℝ) (beta : ℝ) (v : V) (σ : V → Bool) :
    siteUpdate (isingWeight J beta) v σ (update σ v true)
      = logistic (2 * (beta * isingField J v σ)) := by
  have hz := (Zloc_isingWeight_pos J beta σ v).ne'
  rw [siteUpdate_of_Zloc_ne_zero hz, if_pos (agreeOff_update σ v true), Zloc_isingWeight,
    isingWeight, isingEnergy_update, spin_true,
    show beta * (isingRest J v σ + J v v + 1 * isingField J v σ)
      = beta * (isingRest J v σ + J v v) + beta * isingField J v σ by ring,
    Real.exp_add, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  exact exp_div_add_exp_neg _

/-- The complementary branch: the spin at `v` is set to `-1` with probability
`logistic (-2 β h_v(σ)) = 1 - logistic (2 β h_v(σ))`. -/
theorem siteUpdate_isingWeight_false (J : V → V → ℝ) (beta : ℝ) (v : V) (σ : V → Bool) :
    siteUpdate (isingWeight J beta) v σ (update σ v false)
      = logistic (-(2 * (beta * isingField J v σ))) := by
  have hz := (Zloc_isingWeight_pos J beta σ v).ne'
  rw [siteUpdate_of_Zloc_ne_zero hz, if_pos (agreeOff_update σ v false), Zloc_isingWeight,
    isingWeight, isingEnergy_update, spin_false,
    show beta * (isingRest J v σ + J v v + -1 * isingField J v σ)
      = beta * (isingRest J v σ + J v v) + -(beta * isingField J v σ) by ring,
    Real.exp_add, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  rw [show Real.exp (beta * isingField J v σ) + Real.exp (-(beta * isingField J v σ))
      = Real.exp (-(beta * isingField J v σ)) + Real.exp (-(-(beta * isingField J v σ))) by
    rw [neg_neg]; ring]
  rw [exp_div_add_exp_neg]
  ring_nf

/-! ### The general theory, landed on the Ising model -/

/-- The **Ising Gibbs distribution**. -/
noncomputable def isingGibbs (J : V → V → ℝ) (beta : ℝ) : FinDist (V → Bool) :=
  gibbs (isingWeight J beta) (isingWeight_nonneg J beta) (Z_isingWeight_pos J beta)

@[simp] theorem isingGibbs_apply (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) :
    isingGibbs J beta σ = isingWeight J beta σ / Z (isingWeight J beta) := rfl

/-- **The Ising Gibbs distribution is fully supported.**  Unlike the hard-core
measure, which vanishes off the independent sets, this one charges every one of
the `2^n` configurations — which is what makes hypotheses like `hpos` of
`dirichlet_siteChain_eq_zero_iff` automatic here. -/
theorem isingGibbs_pos (J : V → V → ℝ) (beta : ℝ) (σ : V → Bool) : 0 < isingGibbs J beta σ :=
  div_pos (isingWeight_pos J beta σ) (Z_isingWeight_pos J beta)

/-- The **Ising single-site heat-bath update** at the site `v`. -/
noncomputable def isingSiteChain (J : V → V → ℝ) (beta : ℝ) (v : V) : FinChain (V → Bool) :=
  siteChain (isingWeight J beta) (isingWeight_nonneg J beta) v

/-- **The Ising heat-bath update is reversible** with respect to the Ising Gibbs
distribution. -/
theorem isingSiteChain_reversible (J : V → V → ℝ) (beta : ℝ) (v : V) :
    Reversible (isingGibbs J beta) (isingSiteChain J beta v) :=
  siteChain_reversible _ _ _ v

/-- **The Ising heat-bath update is positive semidefinite.** -/
theorem isingSiteChain_nonnegDefinite (J : V → V → ℝ) (beta : ℝ) (v : V) :
    NonnegDefinite (isingGibbs J beta) (isingSiteChain J beta v) :=
  siteChain_nonnegDefinite _ _ _ v

section Dynamics

variable [Nonempty V]

/-- The **Ising Glauber dynamics**. -/
noncomputable def isingGlauber (J : V → V → ℝ) (beta : ℝ) : FinChain (V → Bool) :=
  glauber (isingWeight J beta) (isingWeight_nonneg J beta)

/-- **The Ising Glauber dynamics is reversible with respect to the Ising Gibbs
distribution** — with, in contrast to the hard-core case, no hypotheses on the
parameters at all. -/
theorem isingGlauber_reversible (J : V → V → ℝ) (beta : ℝ) :
    Reversible (isingGibbs J beta) (isingGlauber J beta) :=
  glauber_reversible _ _ _

theorem isingGlauber_stationary (J : V → V → ℝ) (beta : ℝ) :
    Stationary (isingGibbs J beta) (isingGlauber J beta) :=
  glauber_stationary _ _ _

/-- **The Ising Glauber dynamics is positive semidefinite.** -/
theorem isingGlauber_nonnegDefinite (J : V → V → ℝ) (beta : ℝ) :
    NonnegDefinite (isingGibbs J beta) (isingGlauber J beta) :=
  glauber_nonnegDefinite _ _ _

end Dynamics

end Ising

end Arlib.MarkovChains

