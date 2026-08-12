/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Heat-bath block dynamics

The Glauber dynamics resamples one site at a time.  *Heat-bath block dynamics*
resamples a whole block `B ⊆ V` at a time: from a configuration `σ` it keeps the
spins on `V ∖ B` and redraws `σ|_B` from the Gibbs distribution conditioned on
what it kept.  The monograph needs this generality twice.  It is the setting in
which positive semidefiniteness is proved — "the transition matrix of a
heat-bath update for one block is PSD, and the block dynamics is a mixture of
block updates" — and the *uniform block dynamics* on blocks of a fixed size is
the chain that delivers optimal mixing later on.  The Glauber dynamics is the
case of singleton blocks, and that is a theorem here
(`blockChain_singleton`), not a parallel development.

The pinning vocabulary of `Arlib.MarkovChains.Chains.Pinning` is exactly what
the construction wants.  A block update from `σ` is supported on the
configurations agreeing with `σ` on the *complement* of the block — the block is
what is free — so its normaliser is the partition function of the weight pinned
on `Bᶜ`.  That is the definition of `Zblk` below, and detailed balance holds for
the same reason as in the single-site case: `Zblk w B σ` depends only on the
configuration off `B` (`Zblk_congr_of_agreesOn`), so two configurations
exchanged by a block update carry the same denominator and the two sides of the
detailed-balance identity reduce to the symmetric numerator `w σ · w τ`.

One simplification over `Chains.Glauber` deserves mention: no reindexing over
spins is needed anywhere.  There the row sum had to be converted from a sum over
neighbours of `σ` into a sum over `S` (`sum_ite_agreeOff`); here the row sum is
`∑ τ, (if AgreesOn Bᶜ σ τ then w τ else 0)`, which *is* `Zblk w B σ` by
definition.

* `Zblk` — the block-local partition function, with `Zblk_nonneg`,
  **`Zblk_congr_of_agreesOn`**, `w_le_Zblk`, `Zblk_pos_of_w_pos` and
  **`Zblk_singleton`** (`Zblk w {v} σ = Zloc w σ v`), which ties the module to
  the single-site theory.
* `blockUpdate`, `blockChain` — the heat-bath update on one block, as a
  `FinChain (V → S)`.
* **`blockChain_reversible`** — the Gibbs distribution satisfies detailed
  balance for a single block update.
* `blockUpdate_congr_left`, `sum_blockUpdate_mul`, `act_blockChain_idem` — a
  block update is an **idempotent**, and hence, being self-adjoint,
* **`blockChain_nonnegDefinite`** — positive semidefinite.  This is the
  monograph's PSD claim for one block; no eigenvalue appears.
* `blockDynamics` — the **block dynamics** for a family of blocks, as
  `FinKernel.avg` of the block updates, with `blockDynamics_reversible`,
  `blockDynamics_stationary` and **`blockDynamics_nonnegDefinite`**; the last is
  the monograph's "a mixture of PSD kernels is PSD", one lemma application.
* **`blockChain_singleton`**, `blockDynamics_singletons_eq_glauber` — the
  Glauber dynamics is the block dynamics of the singleton blocks, on the nose.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Chains.Pinning
import Arlib.MarkovChains.Techniques.Mixture

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Agreement on a set is an equivalence

`AgreesOn Λ η σ` reads "`σ` agrees with `η` on `Λ`", and as a relation between
`η` and `σ` it is an equivalence relation.  `Chains.Pinning` records reflexivity
and monotonicity in `Λ`; symmetry and transitivity are what the block update
needs, and they are immediate. -/

section AgreesOnEquiv

variable {V : Type*} {S : Type*}

/-- Agreement on `Λ` is symmetric. -/
theorem AgreesOn.symm {Λ : Finset V} {η σ : V → S} (h : AgreesOn Λ η σ) : AgreesOn Λ σ η :=
  fun v hv => (h v hv).symm

/-- Agreement on `Λ` is transitive. -/
theorem AgreesOn.trans {Λ : Finset V} {η σ ρ : V → S} (h : AgreesOn Λ η σ)
    (h' : AgreesOn Λ σ ρ) : AgreesOn Λ η ρ :=
  fun v hv => (h' v hv).trans (h v hv)

/-- Agreement on `Λ` is a symmetric relation. -/
theorem agreesOn_comm {Λ : Finset V} {η σ : V → S} : AgreesOn Λ η σ ↔ AgreesOn Λ σ η :=
  ⟨AgreesOn.symm, AgreesOn.symm⟩

/-- **Configurations agreeing on `Λ` constrain the same set of configurations.**
This is what makes the rows of a block update at two configurations agreeing off
the block coincide. -/
theorem agreesOn_congr_left {Λ : Finset V} {η η' : V → S} (h : AgreesOn Λ η η') (ρ : V → S) :
    AgreesOn Λ η ρ ↔ AgreesOn Λ η' ρ :=
  ⟨fun hρ => h.symm.trans hρ, fun hρ => h.trans hρ⟩

end AgreesOnEquiv

/-! ## Singleton blocks are sites, at the level of agreement

The complement of a singleton block is "everything but `v`", so agreeing off the
block `{v}` is agreeing off the site `v`.  This is the combinatorial half of the
identification of the Glauber dynamics with the singleton-block dynamics. -/

section ComplSingleton

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*}

/-- Agreeing on the complement of `{v}` is agreeing off `v`. -/
theorem agreesOn_compl_singleton_iff (v : V) (σ τ : V → S) :
    AgreesOn ({v} : Finset V)ᶜ σ τ ↔ AgreeOff v σ τ := by
  rw [Finset.compl_singleton]
  exact agreesOn_erase_iff_agreeOff v σ τ

end ComplSingleton

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The block-local partition function

`Zblk w B σ` is the total weight of the configurations agreeing with `σ` off the
block `B`; equivalently, the partition function of `w` pinned on `Bᶜ` by `σ`.
It normalises the conditional Gibbs distribution on `B` given the configuration
elsewhere.  Note the complement: the block is the *free* part, so the pinning is
on its complement. -/

/-- The **block-local partition function**: the total weight of the
configurations obtained from `σ` by resampling the spins inside the block `B`.
It is the partition function of the weight pinned on `Bᶜ` by `σ`. -/
def Zblk (w : (V → S) → ℝ) (B : Finset V) (σ : V → S) : ℝ := Z (pinWeight w Bᶜ σ)

theorem Zblk_apply (w : (V → S) → ℝ) (B : Finset V) (σ : V → S) :
    Zblk w B σ = ∑ τ, (if AgreesOn Bᶜ σ τ then w τ else 0) := rfl

/-- The block-local partition function is the pinned partition function; this is
the definition, recorded for rewriting. -/
theorem Zblk_eq_Z_pinWeight (w : (V → S) → ℝ) (B : Finset V) (σ : V → S) :
    Zblk w B σ = Z (pinWeight w Bᶜ σ) := rfl

theorem Zblk_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (B : Finset V) (σ : V → S) :
    0 ≤ Zblk w B σ :=
  Z_nonneg (pinWeight_nonneg hw Bᶜ σ)

/-- **The block-local partition function only sees the configuration off `B`.**

This is the crux of detailed balance for the block update, exactly as
`Zloc_congr_of_agreeOff` is for the single-site update: two configurations
exchanged by a block update carry the same normaliser, so the two sides of the
detailed-balance identity acquire the same denominator. -/
theorem Zblk_congr_of_agreesOn (w : (V → S) → ℝ) {B : Finset V} {σ τ : V → S}
    (h : AgreesOn Bᶜ σ τ) : Zblk w B σ = Zblk w B τ := by
  rw [Zblk_apply, Zblk_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  by_cases hρ : AgreesOn Bᶜ σ ρ
  · rw [if_pos hρ, if_pos ((agreesOn_congr_left h ρ).mp hρ)]
  · rw [if_neg hρ, if_neg fun hc => hρ ((agreesOn_congr_left h ρ).mpr hc)]

/-- The weight of `σ` is one of the terms of `Zblk w B σ`, namely the term
`τ = σ`, since `σ` agrees with itself off `B`. -/
theorem w_le_Zblk {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (B : Finset V) (σ : V → S) :
    w σ ≤ Zblk w B σ :=
  calc w σ = (if AgreesOn Bᶜ σ σ then w σ else 0) := (if_pos (agreesOn_self Bᶜ σ)).symm
    _ ≤ ∑ τ, (if AgreesOn Bᶜ σ τ then w τ else 0) :=
        Finset.single_le_sum (f := fun τ => if AgreesOn Bᶜ σ τ then w τ else 0)
          (fun ρ _ => by split; exacts [hw ρ, le_rfl]) (mem_univ σ)
    _ = Zblk w B σ := (Zblk_apply w B σ).symm

/-- On the support of the Gibbs distribution the block-local partition function
is positive, so the conditional distribution on the block is genuinely
defined. -/
theorem Zblk_pos_of_w_pos {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (B : Finset V) {σ : V → S}
    (h : 0 < w σ) : 0 < Zblk w B σ := lt_of_lt_of_le h (w_le_Zblk hw B σ)

/-- Contrapositive form: where the block-local partition function vanishes the
weight does too.  This is what makes the degenerate branch of the block update
invisible to the Gibbs measure. -/
theorem w_eq_zero_of_Zblk_eq_zero {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) {B : Finset V}
    {σ : V → S} (h : Zblk w B σ = 0) : w σ = 0 :=
  le_antisymm (h ▸ w_le_Zblk hw B σ) (hw σ)

/-! ## Singleton blocks are sites -/

/-- **The block-local partition function of a singleton block is the local
partition function.**  This is what ties the present module to
`Arlib.MarkovChains.Chains.Glauber`. -/
theorem Zblk_singleton (w : (V → S) → ℝ) (v : V) (σ : V → S) :
    Zblk w {v} σ = Zloc w σ v := by
  rw [Zblk_eq_Z_pinWeight, Finset.compl_singleton, Z_pinWeight_erase]

/-! ## The block heat-bath update -/

/-- The **heat-bath update on the block `B`**: from `σ`, keep the spins off `B`
and draw the spins on `B` from the conditional Gibbs distribution, which assigns
the configuration `τ` (agreeing with `σ` off `B`) probability
`w τ / Zblk w B σ`.

Where the block-local partition function vanishes there is no conditional
distribution to draw from, and the chain holds still; by `w_le_Zblk` this happens
only at configurations of weight `0`, which the Gibbs distribution does not
charge. -/
noncomputable def blockUpdate (w : (V → S) → ℝ) (B : Finset V) (σ τ : V → S) : ℝ :=
  if Zblk w B σ = 0 then (if τ = σ then 1 else 0)
  else if AgreesOn Bᶜ σ τ then w τ / Zblk w B σ else 0

/-- On the degenerate branch the update is the identity row. -/
theorem blockUpdate_of_Zblk_eq_zero {w : (V → S) → ℝ} {B : Finset V} {σ : V → S}
    (h : Zblk w B σ = 0) (τ : V → S) :
    blockUpdate w B σ τ = if τ = σ then 1 else 0 := by
  rw [blockUpdate, if_pos h]

/-- On the branch that matters the update is the conditional Gibbs distribution
on the block. -/
theorem blockUpdate_of_Zblk_ne_zero {w : (V → S) → ℝ} {B : Finset V} {σ : V → S}
    (h : Zblk w B σ ≠ 0) (τ : V → S) :
    blockUpdate w B σ τ = if AgreesOn Bᶜ σ τ then w τ / Zblk w B σ else 0 := by
  rw [blockUpdate, if_neg h]

theorem blockUpdate_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (B : Finset V) (σ τ : V → S) :
    0 ≤ blockUpdate w B σ τ := by
  rw [blockUpdate]
  split
  · split
    · exact zero_le_one
    · exact le_rfl
  · split
    · exact div_nonneg (hw τ) (Zblk_nonneg hw B σ)
    · exact le_rfl

/-- Each row of the block update is a probability distribution.  On the main
branch this is exactly the statement that `Zblk` normalises the conditional law,
and — unlike in the single-site case — no reindexing is involved: the sum of the
numerators over the configurations agreeing with `σ` off `B` *is* `Zblk w B σ`,
by the definitions of `Z` and `pinWeight`. -/
theorem sum_blockUpdate (w : (V → S) → ℝ) (B : Finset V) (σ : V → S) :
    ∑ τ, blockUpdate w B σ τ = 1 := by
  by_cases hz : Zblk w B σ = 0
  · simp [blockUpdate_of_Zblk_eq_zero hz]
  · have step : ∀ τ : V → S,
        blockUpdate w B σ τ = (if AgreesOn Bᶜ σ τ then w τ else 0) / Zblk w B σ := by
      intro τ
      rw [blockUpdate_of_Zblk_ne_zero hz]
      by_cases hA : AgreesOn Bᶜ σ τ
      · rw [if_pos hA, if_pos hA]
      · rw [if_neg hA, if_neg hA, zero_div]
    rw [Finset.sum_congr rfl fun τ _ => step τ, ← Finset.sum_div, ← Zblk_apply, div_self hz]

/-- The **block heat-bath chain** on the block `B`. -/
noncomputable def blockChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (B : Finset V) :
    FinChain (V → S) where
  P := blockUpdate w B
  P_nonneg := blockUpdate_nonneg hw B
  P_sum := sum_blockUpdate w B

@[simp] theorem blockChain_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (B : Finset V)
    (σ τ : V → S) : blockChain w hw B σ τ = blockUpdate w B σ τ := rfl

/-! ## Detailed balance -/

/-- **The block heat-bath update is reversible with respect to the Gibbs
distribution.**

On the branch where the block-local partition function is positive and `σ`, `τ`
agree off `B`, both sides of the detailed-balance identity equal
`w σ · w τ / (Z w · Zblk w B σ)`; the two denominators agree because `Zblk` only
depends on the configuration off `B` (`Zblk_congr_of_agreesOn`).  If `σ` and `τ`
do not agree off `B` both sides vanish, and if a block-local partition function
vanishes then so does the corresponding weight, hence the corresponding Gibbs
mass. -/
theorem blockChain_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (B : Finset V) : Reversible (gibbs w hw hZ) (blockChain w hw B) := by
  intro σ τ
  rw [blockChain_apply, blockChain_apply]
  by_cases hzσ : Zblk w B σ = 0
  · have hσ : w σ = 0 := w_eq_zero_of_Zblk_eq_zero hw hzσ
    rw [gibbs_eq_zero hw hZ hσ, zero_mul]
    by_cases hzτ : Zblk w B τ = 0
    · rw [gibbs_eq_zero hw hZ (w_eq_zero_of_Zblk_eq_zero hw hzτ), zero_mul]
    · rw [blockUpdate_of_Zblk_ne_zero hzτ, hσ]
      simp
  · by_cases hzτ : Zblk w B τ = 0
    · have hτ : w τ = 0 := w_eq_zero_of_Zblk_eq_zero hw hzτ
      rw [gibbs_eq_zero hw hZ hτ, zero_mul, blockUpdate_of_Zblk_ne_zero hzσ, hτ]
      simp
    · rw [blockUpdate_of_Zblk_ne_zero hzσ, blockUpdate_of_Zblk_ne_zero hzτ]
      by_cases hA : AgreesOn Bᶜ σ τ
      · rw [if_pos hA, if_pos hA.symm, Zblk_congr_of_agreesOn w hA, gibbs_apply, gibbs_apply]
        ring
      · rw [if_neg hA, if_neg fun k => hA k.symm]
        simp

/-- The Gibbs distribution is stationary for the block update. -/
theorem blockChain_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (B : Finset V) : Stationary (gibbs w hw hZ) (blockChain w hw B) :=
  (blockChain_reversible w hw hZ B).stationary

/-! ## A block update is a projection

After a heat-bath update on `B` the spins on `B` are already distributed
according to the conditional law, so updating again changes nothing.  Formally:
the rows of `blockUpdate` at configurations agreeing off `B` are *identical*,
whence `P ∘ P = P`.  Combined with self-adjointness (reversibility) this gives
positive semidefiniteness in one line, with no eigenvalue anywhere. -/

/-- **Rows at configurations agreeing off `B` coincide.**  This is the reason a
block update is idempotent. -/
theorem blockUpdate_congr_left {w : (V → S) → ℝ} {B : Finset V} {σ ρ : V → S}
    (h : AgreesOn Bᶜ σ ρ) (hz : Zblk w B σ ≠ 0) (τ : V → S) :
    blockUpdate w B ρ τ = blockUpdate w B σ τ := by
  have hzr : Zblk w B ρ = Zblk w B σ := (Zblk_congr_of_agreesOn w h).symm
  rw [blockUpdate_of_Zblk_ne_zero (by rw [hzr]; exact hz), blockUpdate_of_Zblk_ne_zero hz, hzr]
  by_cases hA : AgreesOn Bᶜ σ τ
  · rw [if_pos ((agreesOn_congr_left h τ).mp hA), if_pos hA]
  · rw [if_neg fun k => hA ((agreesOn_congr_left h τ).mpr k), if_neg hA]

/-- **The block update is idempotent**, entrywise. -/
theorem sum_blockUpdate_mul (w : (V → S) → ℝ) (B : Finset V) (σ τ : V → S) :
    ∑ ρ, blockUpdate w B σ ρ * blockUpdate w B ρ τ = blockUpdate w B σ τ := by
  by_cases hz : Zblk w B σ = 0
  · simp only [blockUpdate_of_Zblk_eq_zero hz, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' univ σ fun ρ => blockUpdate w B ρ τ, if_pos (mem_univ σ)]
    exact blockUpdate_of_Zblk_eq_zero hz τ
  · have key : ∀ ρ : V → S, blockUpdate w B σ ρ * blockUpdate w B ρ τ
        = blockUpdate w B σ ρ * blockUpdate w B σ τ := by
      intro ρ
      by_cases hA : AgreesOn Bᶜ σ ρ
      · rw [blockUpdate_congr_left hA hz]
      · have h0 : blockUpdate w B σ ρ = 0 := by
          rw [blockUpdate_of_Zblk_ne_zero hz, if_neg hA]
        rw [h0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun ρ _ => key ρ, ← Finset.sum_mul, sum_blockUpdate w B σ, one_mul]

/-- The action of the block update on functions is idempotent: `P (P f) = P f`. -/
theorem act_blockChain_idem (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (B : Finset V)
    (f : (V → S) → ℝ) :
    (blockChain w hw B).act ((blockChain w hw B).act f) = (blockChain w hw B).act f := by
  funext σ
  simp only [FinKernel.act_apply, blockChain_apply]
  calc ∑ ρ, blockUpdate w B σ ρ * ∑ τ, blockUpdate w B ρ τ * f τ
      = ∑ ρ, ∑ τ, blockUpdate w B σ ρ * blockUpdate w B ρ τ * f τ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
    _ = ∑ τ, ∑ ρ, blockUpdate w B σ ρ * blockUpdate w B ρ τ * f τ := Finset.sum_comm
    _ = ∑ τ, blockUpdate w B σ τ * f τ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← Finset.sum_mul, sum_blockUpdate_mul w B σ τ]

/-- **The heat-bath update for one block is positive semidefinite.**

This is the monograph's claim (§ "Spectral Gap"): the transition matrix of a
heat-bath update for one block is PSD.  The proof here is the elementary one —
the update is a self-adjoint idempotent in `L²(μ)`, so reversibility gives
`⟪f, P (P f)⟫ = ⟪P f, P f⟫` and idempotence rewrites the left-hand side as
`⟪f, P f⟫`, whence `⟪f, P f⟫ = ⟪P f, P f⟫ ≥ 0`.  No eigenvalue, and no
block-diagonal decomposition, is needed. -/
theorem blockChain_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (B : Finset V) : NonnegDefinite (gibbs w hw hZ) (blockChain w hw B) := by
  intro f
  have h := ip_act_comm (blockChain_reversible w hw hZ B) f ((blockChain w hw B).act f)
  rw [act_blockChain_idem w hw B f] at h
  rw [h]
  exact ip_self_nonneg _ _

/-! ## The block dynamics

Pick a block uniformly at random from a family `𝓑 : ι → Finset V` and perform
the heat-bath update there.  Because the mixture algebra already exists in
`Arlib.MarkovChains.Techniques.Mixture`, every property of the block dynamics is
one lemma application away from the corresponding property of a single block
update. -/

section BlockDynamics

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The **heat-bath block dynamics** of a spin system for the family of blocks
`𝓑`: the uniform average over `i` of the heat-bath updates on `𝓑 i`.  Taking
the blocks to be the singletons recovers the Glauber dynamics
(`blockDynamics_singletons_eq_glauber`). -/
noncomputable def blockDynamics (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (𝓑 : ι → Finset V) :
    FinChain (V → S) :=
  FinKernel.avg fun i => blockChain w hw (𝓑 i)

theorem blockDynamics_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (𝓑 : ι → Finset V)
    (σ τ : V → S) :
    blockDynamics w hw 𝓑 σ τ
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, blockChain w hw (𝓑 i) σ τ := rfl

/-- **The block dynamics is reversible with respect to the Gibbs
distribution.**  Detailed balance is a linear condition, so it survives the
average over blocks. -/
theorem blockDynamics_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (𝓑 : ι → Finset V) : Reversible (gibbs w hw hZ) (blockDynamics w hw 𝓑) :=
  avg_reversible fun i => blockChain_reversible w hw hZ (𝓑 i)

/-- **The Gibbs distribution is stationary for the block dynamics.** -/
theorem blockDynamics_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (𝓑 : ι → Finset V) : Stationary (gibbs w hw hZ) (blockDynamics w hw 𝓑) :=
  avg_stationary fun i => blockChain_stationary w hw hZ (𝓑 i)

/-- **The heat-bath block dynamics is positive semidefinite.**

This is the monograph's argument in full: the transition matrix of a heat-bath
update for one block is PSD (`blockChain_nonnegDefinite`), and the block
dynamics is a mixture of block updates, so `avg_nonnegDefinite` applies.  It is
what makes the absolute spectral gap of the block dynamics equal to its spectral
gap, and hence what lets a Poincaré inequality control the decay of variance. -/
theorem blockDynamics_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (𝓑 : ι → Finset V) : NonnegDefinite (gibbs w hw hZ) (blockDynamics w hw 𝓑) :=
  avg_nonnegDefinite fun i => blockChain_nonnegDefinite w hw hZ (𝓑 i)

end BlockDynamics

/-! ## The Glauber dynamics is the singleton-block case

The monograph states this in passing — "the Glauber dynamics is the special case
of the heat-bath block dynamics where the blocks are single vertices" — and here
it is an equality of transition matrices, so every result about the block
dynamics specialises to `Chains.Glauber` verbatim. -/

/-- The heat-bath update on a singleton block is the single-site update. -/
theorem blockUpdate_singleton (w : (V → S) → ℝ) (v : V) (σ τ : V → S) :
    blockUpdate w {v} σ τ = siteUpdate w v σ τ := by
  rw [blockUpdate, siteUpdate, Zblk_singleton]
  by_cases hz : Zloc w σ v = 0
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    by_cases hA : AgreeOff v σ τ
    · rw [if_pos ((agreesOn_compl_singleton_iff v σ τ).mpr hA), if_pos hA]
    · rw [if_neg fun hc => hA ((agreesOn_compl_singleton_iff v σ τ).mp hc), if_neg hA]

/-- **A singleton block is a site**: the block heat-bath chain on `{v}` is the
single-site heat-bath chain at `v`. -/
theorem blockChain_singleton (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (v : V) :
    blockChain w hw {v} = siteChain w hw v :=
  FinKernel.ext' fun σ τ => blockUpdate_singleton w v σ τ

section Singletons

variable [Nonempty V]

/-- **The Glauber dynamics is the block dynamics of the singleton blocks.**

This is the sense in which `Arlib.MarkovChains.Chains.Glauber` is a corollary of
the present module rather than a parallel development: `glauber_nonnegDefinite`,
for instance, is `blockDynamics_nonnegDefinite` rewritten along this
equality. -/
theorem blockDynamics_singletons_eq_glauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) :
    blockDynamics w hw (fun v : V => {v}) = glauber w hw :=
  FinKernel.ext' fun σ τ => by
    rw [blockDynamics_apply, glauber_apply]
    exact congrArg _ (Finset.sum_congr rfl fun v _ => by
      rw [blockChain_singleton w hw v])

end Singletons

end Arlib.MarkovChains
