/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Pinnings and conditional Gibbs measures

A *pinning* fixes the spins on a subset `Λ ⊆ V` and leaves the rest free.  The
Gibbs measure conditioned on a pinning is the object the whole spectral
independence programme is stated over: influence, spectral independence and the
local walks are all defined *for every pinning simultaneously*, and the
local-to-global induction moves between pinnings of successive sizes.

The observation that organises this module is that **conditioning does not leave
the category**: the conditional measure is again a Gibbs measure, for the weight
that has been zeroed off the pinned event.  So there is no new theory to build —
`pinWeight` produces a weight, and every result about `gibbs`, `Zloc`,
`siteChain` and `glauber` applies to it verbatim.

* `AgreesOn Λ η σ` — `σ` matches the pinning `η` on `Λ`.
* `pinWeight w Λ η` — the weight `w` restricted to the pinned event, and
  `pinWeight_union`, which says pinning twice is pinning on the union.  Pinnings
  compose; this is what makes the induction on `|Λ|` work.
* `Pr_agreesOn` — the pinned event has Gibbs probability `Z(w|Λ,η) / Z(w)`, and
  `gibbsPin_eq_cond` — the conditional measure really is conditioning.
* **`siteUpdate_eq_gibbsPin`** — the headline: the single-site heat-bath update at
  `v` *is* the Gibbs measure conditioned on the pinning of `V \ {v}` by the
  current configuration.  This is the definition of the Glauber dynamics as
  usually stated in words ("resample the spin at `v` from its conditional
  distribution"), recovered here as a theorem about `Chains.Glauber.siteUpdate`,
  and it is the bridge from the chain to the pinning-indexed quantities.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Pinnings -/

section AgreesOn

variable {V : Type*} {S : Type*}

/-- `σ` **agrees with the pinning `η` on `Λ`**: the two configurations have the
same spins at every pinned site. -/
def AgreesOn (Λ : Finset V) (η σ : V → S) : Prop := ∀ v ∈ Λ, σ v = η v

instance decidableAgreesOn [DecidableEq S] (Λ : Finset V) (η σ : V → S) :
    Decidable (AgreesOn Λ η σ) := by
  unfold AgreesOn; infer_instance

@[simp] theorem agreesOn_empty (η σ : V → S) : AgreesOn (∅ : Finset V) η σ := by
  intro v hv; exact absurd hv (Finset.notMem_empty v)

@[simp] theorem agreesOn_self (Λ : Finset V) (η : V → S) : AgreesOn Λ η η :=
  fun _ _ => rfl

/-- Pinning on a larger set is a stronger constraint. -/
theorem AgreesOn.mono {Λ Λ' : Finset V} (h : Λ ⊆ Λ') {η σ : V → S}
    (hσ : AgreesOn Λ' η σ) : AgreesOn Λ η σ := fun v hv => hσ v (h hv)

/-- **Pinnings compose**: agreeing on a union is agreeing on each part. -/
theorem agreesOn_union {Λ Λ' : Finset V} [DecidableEq V] (η σ : V → S) :
    AgreesOn (Λ ∪ Λ') η σ ↔ AgreesOn Λ η σ ∧ AgreesOn Λ' η σ := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (Finset.mem_union_left _ hv),
      fun v hv => h v (Finset.mem_union_right _ hv)⟩
  · rintro ⟨h1, h2⟩ v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h1 v hv
    · exact h2 v hv

end AgreesOn

/-! ## The pinned weight

Conditioning a Gibbs measure on a pinning is the same as zeroing its weight off
the pinned event.  This keeps us inside `Chains.SpinSystem`, so nothing about
conditional measures has to be redeveloped. -/

section PinWeight

variable {V : Type*} {S : Type*} [DecidableEq S]

/-- The weight `w` **restricted to the pinned event**: `w` on configurations
agreeing with `η` on `Λ`, and `0` elsewhere.  The Gibbs measure of `pinWeight`
is the Gibbs measure of `w` conditioned on the pinning. -/
def pinWeight (w : (V → S) → ℝ) (Λ : Finset V) (η : V → S) : (V → S) → ℝ :=
  fun σ => if AgreesOn Λ η σ then w σ else 0

theorem pinWeight_apply (w : (V → S) → ℝ) (Λ : Finset V) (η σ : V → S) :
    pinWeight w Λ η σ = if AgreesOn Λ η σ then w σ else 0 := rfl

theorem pinWeight_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (Λ : Finset V) (η σ : V → S) :
    0 ≤ pinWeight w Λ η σ := by
  rw [pinWeight_apply]; split
  · exact hw σ
  · exact le_rfl

theorem pinWeight_of_agreesOn {w : (V → S) → ℝ} {Λ : Finset V} {η σ : V → S}
    (h : AgreesOn Λ η σ) : pinWeight w Λ η σ = w σ := by
  rw [pinWeight_apply, if_pos h]

theorem pinWeight_of_not_agreesOn {w : (V → S) → ℝ} {Λ : Finset V} {η σ : V → S}
    (h : ¬ AgreesOn Λ η σ) : pinWeight w Λ η σ = 0 := by
  rw [pinWeight_apply, if_neg h]

/-- Pinning nothing changes nothing. -/
@[simp] theorem pinWeight_empty (w : (V → S) → ℝ) (η : V → S) :
    pinWeight w ∅ η = w := by
  funext σ; rw [pinWeight_apply, if_pos (agreesOn_empty η σ)]

/-- **Pinning twice is pinning once, on the union.**  This is what lets the
local-to-global argument add one pinned site at a time. -/
theorem pinWeight_union [DecidableEq V] (w : (V → S) → ℝ) (Λ Λ' : Finset V) (η : V → S) :
    pinWeight (pinWeight w Λ η) Λ' η = pinWeight w (Λ ∪ Λ') η := by
  funext σ
  simp only [pinWeight_apply]
  by_cases h1 : AgreesOn Λ η σ <;> by_cases h2 : AgreesOn Λ' η σ <;>
    simp [h1, h2, agreesOn_union]

end PinWeight

/-! ## The pinned partition function and the conditioning identity -/

section Conditioning

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The pinned partition function is the weight of the pinned event. -/
theorem Z_pinWeight (w : (V → S) → ℝ) (Λ : Finset V) (η : V → S) :
    Z (pinWeight w Λ η) = ∑ σ ∈ univ.filter (AgreesOn Λ η), w σ := by
  rw [Z_apply, Finset.sum_filter]
  rfl

/-- **The pinned event has Gibbs probability `Z(w|Λ,η) / Z(w)`.** -/
theorem Pr_agreesOn {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (η : V → S) :
    Pr (gibbs w hw hZ) (univ.filter (AgreesOn Λ η)) = Z (pinWeight w Λ η) / Z w := by
  rw [Pr_apply, Z_pinWeight, Finset.sum_div]
  exact Finset.sum_congr rfl fun σ _ => rfl

/-- **The pinned Gibbs measure really is conditioning.**  On the pinned event it
is the original measure renormalised by the probability of that event. -/
theorem gibbsPin_eq_cond {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    {Λ : Finset V} {η : V → S} (hZ' : 0 < Z (pinWeight w Λ η)) {σ : V → S}
    (hσ : AgreesOn Λ η σ) :
    gibbs (pinWeight w Λ η) (pinWeight_nonneg hw Λ η) hZ' σ
      = gibbs w hw hZ σ / Pr (gibbs w hw hZ) (univ.filter (AgreesOn Λ η)) := by
  have hZw : Z w ≠ 0 := hZ.ne'
  have hZp : Z (pinWeight w Λ η) ≠ 0 := hZ'.ne'
  rw [Pr_agreesOn hw hZ, gibbs_apply, gibbs_apply, pinWeight_of_agreesOn hσ]
  field_simp

end Conditioning

/-! ## The Glauber dynamics as resampling from a conditional measure

The single-site update at `v` is exactly the Gibbs measure conditioned on
pinning every *other* site to its current value.  Stating the chain this way is
what connects it to the pinning-indexed machinery of the local walks. -/

section EraseAgree

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*}

/-- Pinning every site but `v` is exactly agreeing off `v`. -/
theorem agreesOn_erase_iff_agreeOff (v : V) (σ τ : V → S) :
    AgreesOn (univ.erase v) σ τ ↔ AgreeOff v σ τ := by
  constructor
  · intro h u hu
    exact (h u (Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩)).symm
  · intro h u hu
    exact (h u (Finset.mem_erase.mp hu).1).symm

end EraseAgree

section SiteUpdate

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The partition function of the "everything but `v`" pinning is the local
partition function at `v`. -/
theorem Z_pinWeight_erase (w : (V → S) → ℝ) (v : V) (σ : V → S) :
    Z (pinWeight w (univ.erase v) σ) = Zloc w σ v := by
  rw [Z_apply]
  have : ∀ τ : V → S, pinWeight w (univ.erase v) σ τ
      = if AgreeOff v σ τ then w τ else 0 := by
    intro τ
    rw [pinWeight_apply]
    by_cases h : AgreeOff v σ τ
    · rw [if_pos ((agreesOn_erase_iff_agreeOff v σ τ).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((agreesOn_erase_iff_agreeOff v σ τ).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl fun τ _ => this τ, sum_ite_agreeOff v σ w, Zloc_apply]

/-- **The single-site heat-bath update is the conditional Gibbs measure.**

`siteUpdate w v σ` is the Gibbs measure of `w` conditioned on pinning every site
other than `v` to its value in `σ`.  This is the textbook description of the
Glauber dynamics — "redraw the spin at `v` from its conditional distribution
given the rest" — proved here rather than taken as the definition. -/
theorem siteUpdate_eq_gibbsPin {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (v : V) (σ : V → S)
    (hZ : 0 < Z (pinWeight w (univ.erase v) σ)) (τ : V → S) :
    siteUpdate w v σ τ
      = gibbs (pinWeight w (univ.erase v) σ) (pinWeight_nonneg hw _ _) hZ τ := by
  have hZ0 : Zloc w σ v ≠ 0 := by
    rw [← Z_pinWeight_erase]; exact hZ.ne'
  rw [siteUpdate_of_Zloc_ne_zero hZ0, gibbs_apply, pinWeight_apply,
    Z_pinWeight_erase]
  by_cases h : AgreeOff v σ τ
  · rw [if_pos h, if_pos ((agreesOn_erase_iff_agreeOff v σ τ).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((agreesOn_erase_iff_agreeOff v σ τ).mp hc)),
      zero_div]

end SiteUpdate

end Arlib.MarkovChains
