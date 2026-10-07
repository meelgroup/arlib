/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.ProbRAM
import Arlib.Computation.ChargedPMF
import Arlib.Computation.Realization

/-!
# Distributional refinement of randomized charged computations

The authoring interface remains `PMF (Charged κ κₛ α)`. A certificate proves
exact equality of decoded output laws, representation invariants for every
reachable concrete execution, and support-wise actual machine cost bounds.
The decoder and all PMF observations are specification-only. Sequencing uses
only represented results to select executable continuations; state and cost
remain internal to the probabilistic machine semantics.
-/
namespace Arlib.Computation
universe u
noncomputable section

/-- Exact output-law agreement and support-wise representation and cost bounds.
`decode` is mathematical; it is never called by the probabilistic RAM program. -/
structure ProbRealizes {κ κₛ : Type} {α β : Type u} {w : ℕ}
    (μ : PMF (Charged κ κₛ α)) (q : ProbRAM w β) (Pre : RamState w → Prop)
    (decode : β → RamState w → α) (Post : α → β → RamState w → Prop) (budget : ℕ) : Prop where
  law : ∀ σ, Pre σ → q.decodedOutputs decode σ = μ.map Charged.val
  invariant : ∀ σ, Pre σ → ∀ result ∈ (q.run σ).support,
    Post (decode result.1 result.2.1) result.1 result.2.1
  steps_le : ∀ σ, Pre σ → ∀ result ∈ (q.run σ).support,
    CostVec.steps CostModel.unitCost result.2.2 ≤ budget

/-- Abstract probabilistic sequencing retains both charged instruction tallies.
The continuation receives the first abstract result; this is a helper over the
existing interface, not a new authoring monad. -/
def chargedBind {κ κₛ : Type} [DecidableEq κ] {α β : Type u}
    (μ : PMF (Charged κ κₛ α)) (f : α → PMF (Charged κ κₛ β)) :
    PMF (Charged κ κₛ β) :=
  μ.bind fun first => (f first.val).map fun next => first >>= fun _ => next

/-- Abstract sequencing produces the ordinary composition of output laws. -/
theorem chargedBind_law {κ κₛ : Type} [DecidableEq κ] {α β : Type u}
    (μ : PMF (Charged κ κₛ α)) (f : α → PMF (Charged κ κₛ β)) :
    (chargedBind μ f).map Charged.val =
      (μ.map Charged.val).bind fun a => (f a).map Charged.val := by
  simp [chargedBind, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

private theorem bind_congr_support {α β : Type u} (μ : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ μ.support, f a = g a) : μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · simp [(μ.apply_eq_zero_iff a).mpr ha]

namespace ProbRealizes
variable {κ κₛ : Type} {α β γ δ : Type u} {w : ℕ}

/-- Forward already represented results under the existing charged interface. -/
theorem pure (a : α) (b : β) (Pre : RamState w → Prop) (decode : β → RamState w → α)
    (Post : α → β → RamState w → Prop) (hdecode : ∀ σ, Pre σ → decode b σ = a)
    (hpost : ∀ σ, Pre σ → Post a b σ) :
    ProbRealizes (PMF.pure (pure a : Charged κ κₛ α))
      (ProbRAM.pure b) Pre decode Post 0 := by
  constructor
  · intro σ hσ
    simp [PMF.pure_map, hdecode σ hσ]
  · intro σ hσ result hr
    rw [ProbRAM.run_pure, PMF.mem_support_pure_iff] at hr
    subst result
    simpa only [hdecode σ hσ] using hpost σ hσ
  · intro σ _ result hr
    rw [ProbRAM.run_pure, PMF.mem_support_pure_iff] at hr
    subst result
    simp

/-- Lift a deterministic realization with a meaningful output decoder into a
probabilistic certificate whose distribution is a point mass. -/
theorem deterministic {p : Charged κ κₛ α} {q : RAM w β}
    {Pre : RamState w → Prop} {decode : β → RamState w → α}
    {Post : α → β → RamState w → Prop} {budget : ℕ}
    (h : Realizes p q Pre (fun a b σ => decode b σ = a ∧ Post a b σ) budget) :
    ProbRealizes (PMF.pure p) (ProbRAM.lift q) Pre decode Post budget := by
  constructor
  · intro σ hσ
    simp [PMF.pure_map, (h.correct σ hσ).1]
  · intro σ hσ result hr
    rw [ProbRAM.run_lift, PMF.mem_support_pure_iff] at hr
    subst result
    have hp := h.correct σ hσ
    simpa only [hp.1] using hp.2
  · intro σ hσ result hr
    rw [ProbRAM.run_lift, PMF.mem_support_pure_iff] at hr
    subst result
    exact h.steps_le σ hσ

/-- The support certificate establishes the actual machine worst-case bound. -/
theorem worstSteps_le {μ : PMF (Charged κ κₛ α)} {q : ProbRAM w β}
    {Pre : RamState w → Prop} {decode : β → RamState w → α}
    {Post : α → β → RamState w → Prop} {budget : ℕ}
    (h : ProbRealizes μ q Pre decode Post budget) (σ : RamState w) (hσ : Pre σ) :
    q.worstSteps σ ≤ (budget : ℕ∞) :=
  (ProbRAM.worstSteps_le_iff q σ budget).mpr (h.steps_le σ hσ)

/-- Restrict inputs, relax the support invariant and enlarge the cost budget. -/
theorem consequence {μ : PMF (Charged κ κₛ α)} {q : ProbRAM w β}
    {Pre Pre' : RamState w → Prop} {decode : β → RamState w → α}
    {Post Post' : α → β → RamState w → Prop} {budget budget' : ℕ}
    (h : ProbRealizes μ q Pre decode Post budget)
    (hpre : ∀ σ, Pre' σ → Pre σ)
    (hpost : ∀ a b σ, Post a b σ → Post' a b σ)
    (hb : budget ≤ budget') : ProbRealizes μ q Pre' decode Post' budget' := by
  constructor
  · intro σ hσ; exact h.law σ (hpre σ hσ)
  · intro σ hσ r hr; exact hpost _ _ _ (h.invariant σ (hpre σ hσ) r hr)
  · intro σ hσ r hr; exact le_trans (h.steps_le σ (hpre σ hσ) r hr) hb

/-- Distributional sequencing transports the represented intermediate result and
state into the continuation precondition, and adds actual execution budgets. -/
theorem bind [DecidableEq κ] {μ : PMF (Charged κ κₛ α)} {q : ProbRAM w β}
    {f : α → PMF (Charged κ κₛ γ)} {g : β → ProbRAM w δ}
    {Pre : RamState w → Prop} {decode₁ : β → RamState w → α} {decode₂ : δ → RamState w → γ}
    {Mid : α → β → RamState w → Prop} {Post : γ → δ → RamState w → Prop}
    {b₁ b₂ : ℕ}
    (hp : ProbRealizes μ q Pre decode₁ Mid b₁)
    (hf : ∀ a b, ProbRealizes (f a) (g b)
      (fun σ => Mid a b σ ∧ decode₁ b σ = a) decode₂ Post b₂) :
    ProbRealizes (chargedBind μ f) (q >>= g) Pre decode₂ Post (b₁ + b₂) := by
  constructor
  · intro σ hσ
    calc
      (q >>= g).decodedOutputs decode₂ σ =
          (q.run σ).bind (fun first => (g first.1).decodedOutputs decode₂ first.2.1) := by
        rw [ProbRAM.decodedOutputs_bind]
      _ = (q.run σ).bind (fun first => (f (decode₁ first.1 first.2.1)).map Charged.val) := by
        apply bind_congr_support
        intro first hfirst
        exact (hf (decode₁ first.1 first.2.1) first.1).law first.2.1
          ⟨hp.invariant σ hσ first hfirst, rfl⟩
      _ = (q.decodedOutputs decode₁ σ).bind (fun a => (f a).map Charged.val) := by
        simp [ProbRAM.decodedOutputs, PMF.bind_map, Function.comp_def]
      _ = (μ.map Charged.val).bind (fun a => (f a).map Charged.val) := by
        rw [hp.law σ hσ]
      _ = (chargedBind μ f).map Charged.val := (chargedBind_law μ f).symm
  · intro σ hσ result hr
    rw [ProbRAM.run_bind, PMF.mem_support_bind_iff] at hr
    obtain ⟨first, hfirst, hr⟩ := hr
    rw [PMF.mem_support_map_iff] at hr
    obtain ⟨next, hnext, rfl⟩ := hr
    exact (hf (decode₁ first.1 first.2.1) first.1).invariant first.2.1
      ⟨hp.invariant σ hσ first hfirst, rfl⟩ next hnext
  · intro σ hσ result hr
    rw [ProbRAM.run_bind, PMF.mem_support_bind_iff] at hr
    obtain ⟨first, hfirst, hr⟩ := hr
    rw [PMF.mem_support_map_iff] at hr
    obtain ⟨next, hnext, rfl⟩ := hr
    rw [CostVec.steps_add]
    exact Nat.add_le_add (hp.steps_le σ hσ first hfirst)
      ((hf (decode₁ first.1 first.2.1) first.1).steps_le first.2.1
        ⟨hp.invariant σ hσ first hfirst, rfl⟩ next hnext)

end ProbRealizes

namespace ProbabilityRealization

/-- A randomized charged instruction in the existing PMF authoring interface. -/
def fairBit : PMF (Charged Op Unit Bool) :=
  ProbRAM.fair.map (Charged.op .randBit)

/-- A fair-bit draw preserves any asserted memory invariant and pays one actual
random-bit instruction. Its law is Bernoulli one-half, independently per bind. -/
theorem fairBit_realizes (F : RamState w → Prop) :
    ProbRealizes fairBit (ProbRAM.randBit : ProbRAM w Bool) F (fun b _ => b)
      (fun _ _ σ => F σ) 1 := by
  constructor
  · intro σ _
    simp only [ProbRAM.decodedOutputs, ProbRAM.run_randBit, fairBit, PMF.map_comp]
    rfl
  · intro σ hσ r hr
    have h := ProbRAM.randBit_support hr
    simpa only [h.1] using hσ
  · intro σ _ r hr
    have h := ProbRAM.randBit_support hr
    simp [h.2]

/-- Two charged fair draws, with their charges accumulated by abstract bind. -/
def twoBits : PMF (Charged Op Unit (Bool × Bool)) :=
  chargedBind fairBit fun first =>
    chargedBind fairBit fun second => PMF.pure (pure (first, second))

/-- The two-draw randomized authoring program is realized by two actual fair-bit
instructions, with state-aware decoding and generic sequencing twice. -/
theorem twoBits_realizes (F : RamState w → Prop) :
    ProbRealizes twoBits (ProbRAM.twoBits : ProbRAM w (Bool × Bool)) F (fun b _ => b)
      (fun _ _ σ => F σ) 2 := by
  unfold twoBits ProbRAM.twoBits
  apply ProbRealizes.bind (b₁ := 1) (b₂ := 1)
    (decode₁ := fun b _ => b) (Mid := fun _ _ σ => F σ) (fairBit_realizes F)
  intro first bfirst
  let G : RamState w → Prop := fun σ => F σ ∧ bfirst = first
  change ProbRealizes (chargedBind fairBit _)
    (ProbRAM.randBit >>= fun second => ProbRAM.pure (bfirst, second))
    G (fun b _ => b) (fun _ _ σ => F σ) (1 + 0)
  apply ProbRealizes.bind (b₁ := 1) (b₂ := 0)
    (decode₁ := fun b _ => b) (Mid := fun _ _ σ => G σ) (fairBit_realizes G)
  intro second bsecond
  apply ProbRealizes.pure (first, second) (bfirst, bsecond)
    (fun σ => G σ ∧ bsecond = second) (fun b _ => b) (fun _ _ σ => F σ)
  · intro σ hσ
    exact Prod.ext hσ.1.2 hσ.2
  · intro σ hσ
    exact hσ.1.1

end ProbabilityRealization
end
end Arlib.Computation
