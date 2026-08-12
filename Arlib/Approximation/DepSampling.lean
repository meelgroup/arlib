/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Parsimonious
import Arlib.Approximation.Pinned
import Mathlib.Data.Sigma.Basic

/-!
# Almost-uniform sampling when the solution *type* moves with the instance

`IsFPAUS size g A` (`Arlib.Approximation.Counting`) is stated for
`g : α → Finset Ω` and `A : α → ℝ → PMF (Option Ω × ℕ)` with **one** `Ω`, fixed
before the instance is named.  That is the right definition for a sampling
problem whose solutions all live in one universe of objects — satisfying
assignments of a propositional formula, spanning trees of a graph — and it is
wrong for a *family* of problems whose solution objects are typed by the
instance.  The two symptoms are the same fact seen from either side:

* a family of conjunctive queries whose **constant domain** grows has answers in
  `List (C m)`, a type that moves with `m`, so it is not an `IsFPAUS` instance
  family at all;
* a family of tree automata whose **label alphabet** grows has accepted trees in
  `LTree (Γ m)`, and the usual repair is to *tag*: replace `Γ m` by
  `Σ m, Γ m` and push every solution set forward along the tag.  Tagging works,
  and it is noise.

This module removes both symptoms at once, by making the solution type a
function of the instance.

## The definition

```
structure IsFPAUSDep {α : Type u} {Ω : α → Type v} (size : α → ℕ)
    (g : (w : α) → Finset (Ω w)) (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) : Prop
```

with the *same three clauses*, read in the fibre over `w`.  Nothing about the
content changes: `uniform` still pins `Pr[output = x]` inside
`[(1-δ)/|g w|, (1+δ)/|g w|]` for every `x ∈ g w`, `empty` still forces `none` on
an instance with no solutions, and `polytime` is verbatim the same inequality
between natural numbers.  This is possible because every clause of `IsFPAUS`
already quantifies over `w` first and mentions `Ω` only *underneath* that
quantifier — the fixed `Ω` was never load-bearing, only convenient.

**The constant case is not a special case by fiat**: `isFPAUS_iff_dep` is an
`Iff`, and it holds by `Iff.rfl` up to reassembling the three fields.  So
`IsFPAUSDep` is a generalisation of `IsFPAUS` in the strict sense — every
existing consumer of `IsFPAUS` may be read as a consumer of the dependent form
at a constant family and *vice versa*, and no existing theorem changes meaning.

## Tagging is subsumed, exactly

`isFPAUSDep_iff_tagged` is the sharp statement about the workaround.  Given
**any** family of embeddings `tag w : Ω w ↪ T` into a single type `T`,

    IsFPAUSDep size g A  ↔  IsFPAUS size (fun w => (g w).map (tag w)) (tagAlg tag A)

— an `Iff`, for an arbitrary injective tagging, with no hypothesis relating the
`tag w` to each other.  So the tagged statement and the dependent statement have
the same content: a development that tagged its solutions lost nothing and
gained nothing, and may now stop.  `sigmaEmb` is the canonical tagging, into
`Σ w, Ω w`, and `isFPAUSDep_iff_tagged_sigma` is the corollary; but the general
form is what applies to a development that tagged by something *coarser* than
the instance — an index `m` rather than the instance itself, which is the shape
a `Σ`-family actually produces.

The `Iff` is what makes this a subsumption rather than a convenience.  A one-way
implication would leave open that the tagged form is strictly stronger, i.e.
that a tagged sampler must additionally be uniform *across* fibres.  It is not:
`uniform` only ever compares `Pr[output = x]` with `|g w|` at a single `w`.

## What does **not** need the same treatment: `IsFPRAS`

An FPRAS returns a *number*.  Its output type is `ℝ` — written into the
definition, not a parameter — so there is no `Ω` to make depend on the instance,
and a family of counting problems whose solution objects move is still a family
of `α → ℝ` for one moving `α`, which a `Σ`-type already handles with no new
definition.  `isFPRAS_no_dependent_output` records this as a triviality one can
point at rather than as prose: the counting analogue of `isFPAUS_iff_dep` is the
identity, because `IsFPRAS size f A` never mentions a solution type.  A
`IsFPRASDep` would be `IsFPRAS` with a phantom parameter, and is not built here.

## What is ported, and what is not

* `IsFPAUSDep.comp_bijection` — the transfer theorem, with source and target
  solution types **both** moving.  Same proof as `IsFPAUS.comp_bijection`;
  `decodeOpt` needs only that `Ω₁ w` and `Ω₂ (h w)` lie in a common universe,
  which they do fibrewise.
* `IsFPAUSDep.PinnedTime`, with `polytime`, `weaken`, `exists_pinnedTime`,
  `of_pinnedTime`, `pinnedTime_of_cost_zero`, and the pinned transfer theorems
  `comp_bijection_pinned_on` / `comp_bijection_pinned`.  All of these are
  statements about the *second* component of the output pair, which is `ℕ` in
  every fibre, so none of them notices that `Ω` moved.
* `IsFPAUSDep.Charges`, with `not_cost_zero` and `map_add`.  Likewise.

**Not ported, and why.**  `Arlib.Approximation.Sampling`'s `PreprocessedSampler`
assembly is *not* restated here.  Its hypotheses include a polynomial bound on
`Real.log (g w).card` and a retry loop whose failure probability is measured
against one fixed `Ω`; the assembly itself would go through fibrewise, but every
one of its inputs (`retrySampler`, `between_of_abs_sub_le`, `outProbR_retryPMF`)
is a statement about a *single* `PMF` on a *single* type and is therefore
already applicable in a fibre without any dependent restatement.  Restating them
would duplicate a hundred lemmas to change nothing.  The rule is: a lemma that
quantifies over instances needs the dependent form; a lemma about one run does
not.

`ParsimoniousReduction` and `PinnedReduction` are likewise not given dependent
twins.  They bundle a counting datum (`f w = g (toFun w)`, on `ℝ`) with a
sampling datum, and the counting half is already universe-blind; a caller whose
solution types move takes `IsFPRAS.comp_parsimonious` and
`IsFPAUSDep.comp_bijection` separately, which is what
`CQCount.Capstone.KDomain` does.

## Main results

* `IsFPAUSDep` — the definition.
* `isFPAUS_iff_dep` — the constant case, as an `Iff`.
* `isFPAUSDep_iff_tagged`, `isFPAUSDep_iff_tagged_sigma` — tagging is subsumed.
* `IsFPAUSDep.comp_bijection`, `.comp_bijection_pinned_on`,
  `.comp_bijection_pinned` — transfer along a bijective reduction.
* `IsFPAUSDep.PinnedTime`, `IsFPAUSDep.Charges` and their API.
* `isFPRAS_no_dependent_output` — the negative on the counting side.
-/

universe u u₁ u₂ v w

namespace Arlib.Approximation

open scoped ENNReal

/-! ## A universe-general form of `outProbR_map`

`outProbR_map` is stated in `Counting` inside a section with
`variable {β γ : Type u}`, so its source and target types are forced into the
*same* universe.  Every use in the library satisfies that, and the tagging
theorem below does not: `Ω w : Type v` is tagged into `Σ w : α, Ω w :
Type (max u v)`.  The statement is added here rather than by loosening the
existing one, so that no elaborated consumer of `outProbR_map` changes at all. -/

/-- `outProb_map` with the source and target types in arbitrary, possibly
different, universes.  The proof is the original one; only the binders differ. -/
theorem outProb_map' {β : Type u} {γ : Type v} (μ : PMF (β × ℕ)) (F : β × ℕ → γ × ℕ)
    (φ : β → γ) (hF : ∀ p, (F p).1 = φ p.1) (S : Set γ) :
    outProb (μ.map F) S = outProb μ (φ ⁻¹' S) := by
  rw [outProb, PMF.toOuterMeasure_map_apply]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hF p]

/-- Real-valued form of `outProb_map'`. -/
theorem outProbR_map' {β : Type u} {γ : Type v} (μ : PMF (β × ℕ)) (F : β × ℕ → γ × ℕ)
    (φ : β → γ) (hF : ∀ p, (F p).1 = φ p.1) (S : Set γ) :
    outProbR (μ.map F) S = outProbR μ (φ ⁻¹' S) := by
  rw [outProbR, outProbR, outProb_map' μ F φ hF]

/-- `mem_support_map` across two universes; same proof, wider binders. -/
theorem mem_support_map' {β : Type u} {γ : Type v} {μ : PMF (β × ℕ)}
    {F : β × ℕ → γ × ℕ} {p : γ × ℕ} (hp : p ∈ (μ.map F).support) :
    ∃ q ∈ μ.support, F q = p := by
  rwa [PMF.support_map] at hp

/-! ## The dependent definition -/

/-- **A fully polynomial-time almost-uniform sampler for a family of solution
sets whose ambient type moves with the instance.**

`Ω : α → Type v` gives each instance its own solution type; `g w : Finset (Ω w)`
its solution set; `A w δ : PMF (Option (Ω w) × ℕ)` the joint law of the
sampler's output and step count in that fibre.  The three clauses are
`IsFPAUS`'s, read fibrewise, and say exactly what `IsFPAUS`'s say — see
`isFPAUS_iff_dep`, which is an `Iff` at a constant `Ω`.

Nothing here is uniform *across* fibres except the two constants of `polytime`,
and that is deliberate: those constants are the entire content of "polynomial
time in the instance size", and letting them vary with the instance would empty
the clause. -/
structure IsFPAUSDep {α : Type u} {Ω : α → Type v} (size : α → ℕ)
    (g : (w : α) → Finset (Ω w))
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) : Prop where
  /-- Every solution of `w` is returned with probability within `(1 ± δ)` of
  uniform on `g w`. -/
  uniform : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty → ∀ x ∈ g w,
    outProbR (A w δ) {some x} ∈ Set.Icc ((1-δ)/(g w).card) ((1+δ)/(g w).card)
  /-- On an instance with no solutions the sampler reports `none`. -/
  empty : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, g w = ∅ → outProbR (A w δ) {none} = 1
  /-- Every run takes time polynomial in the instance size and in `log(1/δ)`,
  with **one** pair of constants for the whole family. -/
  polytime : ∃ c d : ℕ, ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
    p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ d

/-! ## The constant case

The point of this section is that `IsFPAUSDep` is a *generalisation* and not a
neighbouring notion.  The `Iff` is what protects every existing consumer of
`IsFPAUS`: a theorem stated in either form may be used in the other. -/

/-- **`IsFPAUS` is `IsFPAUSDep` at a constant family, on the nose.**

An `Iff`, not an implication in either direction: the three clauses are the same
propositions, and the proof is reassembling the fields.  Consequently no theorem
about `IsFPAUS` becomes weaker or stronger when read through `IsFPAUSDep`, and a
development may migrate one statement at a time. -/
theorem isFPAUS_iff_dep {α : Type u} {Ω₀ : Type v} (size : α → ℕ) (g : α → Finset Ω₀)
    (A : α → ℝ → PMF (Option Ω₀ × ℕ)) :
    IsFPAUS size g A ↔ IsFPAUSDep (Ω := fun _ => Ω₀) size g A :=
  ⟨fun h => ⟨h.uniform, h.empty, h.polytime⟩, fun h => ⟨h.uniform, h.empty, h.polytime⟩⟩

/-- The forward direction, as a term a caller can apply. -/
theorem IsFPAUS.toDep {α : Type u} {Ω₀ : Type v} {size : α → ℕ} {g : α → Finset Ω₀}
    {A : α → ℝ → PMF (Option Ω₀ × ℕ)} (h : IsFPAUS size g A) :
    IsFPAUSDep (Ω := fun _ => Ω₀) size g A := (isFPAUS_iff_dep size g A).1 h

/-- The backward direction, as a term a caller can apply. -/
theorem IsFPAUSDep.toConst {α : Type u} {Ω₀ : Type v} {size : α → ℕ} {g : α → Finset Ω₀}
    {A : α → ℝ → PMF (Option Ω₀ × ℕ)} (h : IsFPAUSDep (Ω := fun _ => Ω₀) size g A) :
    IsFPAUS size g A := (isFPAUS_iff_dep size g A).2 h

/-! ## Tagging is subsumed

The workaround for a moving solution type is to embed every fibre into one type
and push the solution sets forward.  The theorems here say that the workaround
changes nothing: the tagged `IsFPAUS` statement and the untagged `IsFPAUSDep`
statement are *equivalent*, for an arbitrary family of embeddings. -/

section Tagging

variable {α : Type u} {Ω : α → Type v} {T : Type w}

/-- The tagged sampler: run `A w`, then relabel its output by `tag w`.  The step
count is untouched, which is why every cost statement transports. -/
noncomputable def tagAlg (tag : (w : α) → Ω w ↪ T)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) : α → ℝ → PMF (Option T × ℕ) :=
  fun w δ => (A w δ).map (fun p => (p.1.map (tag w), p.2))

@[simp] theorem tagAlg_apply (tag : (w : α) → Ω w ↪ T)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) (w : α) (δ : ℝ) :
    tagAlg tag A w δ = (A w δ).map (fun p => (p.1.map (tag w), p.2)) := rfl

/-- The event "the tagged output is `tag w x`" is the event "the raw output is
`x`", because `tag w` is injective.  This is the only computation the
equivalence needs. -/
theorem outProbR_tagAlg_some (tag : (w : α) → Ω w ↪ T)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) (w : α) (δ : ℝ) (x : Ω w) :
    outProbR (tagAlg tag A w δ) {some (tag w x)} = outProbR (A w δ) {some x} := by
  rw [tagAlg, outProbR_map' (A w δ) (fun p => (p.1.map (tag w), p.2))
      (fun o => o.map (tag w)) (fun _ => rfl)]
  congr 1
  ext o
  cases o with
  | none => simp
  | some y =>
    simp only [Set.mem_preimage, Option.map_some, Set.mem_singleton_iff, Option.some.injEq]
    exact ⟨fun h => (tag w).injective h, fun h => congrArg _ h⟩

/-- Tagging does not change the probability of reporting `none`. -/
theorem outProbR_tagAlg_none (tag : (w : α) → Ω w ↪ T)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) (w : α) (δ : ℝ) :
    outProbR (tagAlg tag A w δ) {none} = outProbR (A w δ) {none} := by
  rw [tagAlg, outProbR_map' (A w δ) (fun p => (p.1.map (tag w), p.2))
      (fun o => o.map (tag w)) (fun _ => rfl)]
  congr 1
  ext o
  cases o <;> simp

/-- Tagging does not change the step count, in either direction. -/
theorem mem_support_tagAlg_iff (tag : (w : α) → Ω w ↪ T)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) (w : α) (δ : ℝ) (n : ℕ) :
    (∃ p ∈ (tagAlg tag A w δ).support, p.2 = n) ↔ ∃ q ∈ (A w δ).support, q.2 = n := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [tagAlg_apply] at hp
    obtain ⟨q, hq, rfl⟩ := mem_support_map' hp
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(q.1.map (tag w), q.2), ?_, rfl⟩
    rw [tagAlg_apply, PMF.support_map]
    exact ⟨q, hq, rfl⟩

/-- **Tagging is subsumed.**

For *any* family of embeddings `tag w : Ω w ↪ T` into a single type — no
relation between the `tag w` assumed — the tagged `IsFPAUS` statement and the
dependent statement are equivalent.

Read left to right this says the dependent form is at least as strong as any
tagging.  Read right to left it says a development that tagged proved nothing
extra: in particular a tagged sampler is *not* additionally required to be
uniform across fibres, since `IsFPAUS.uniform` compares `Pr[output = x]` only
with `|g w|` at the single `w` that produced `x`.  Both directions matter, and
together they say the tagging device is content-free. -/
theorem isFPAUSDep_iff_tagged {size : α → ℕ} {g : (w : α) → Finset (Ω w)}
    {A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)} (tag : (w : α) → Ω w ↪ T) :
    IsFPAUSDep size g A ↔ IsFPAUS size (fun w => (g w).map (tag w)) (tagAlg tag A) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro w δ hδ hne x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      have hne' : (g w).Nonempty := by
        rwa [← Finset.card_pos, ← Finset.card_map (tag w), Finset.card_pos]
      rw [outProbR_tagAlg_some, Finset.card_map]
      exact h.uniform w δ hδ hne' y hy
    · intro w δ hδ hemp
      rw [outProbR_tagAlg_none]
      exact h.empty w δ hδ (Finset.map_eq_empty.1 hemp)
    · obtain ⟨c, d, hcd⟩ := h.polytime
      refine ⟨c, d, fun w δ hδ p hp => ?_⟩
      rw [tagAlg_apply] at hp
      obtain ⟨q, hq, rfl⟩ := mem_support_map' hp
      exact hcd w δ hδ q hq
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro w δ hδ hne x hx
      have hx' : tag w x ∈ (g w).map (tag w) := Finset.mem_map_of_mem _ hx
      have hne' : ((g w).map (tag w)).Nonempty := ⟨_, hx'⟩
      have := h.uniform w δ hδ hne' _ hx'
      rwa [outProbR_tagAlg_some, Finset.card_map] at this
    · intro w δ hδ hemp
      have := h.empty w δ hδ (by rw [hemp]; simp)
      rwa [outProbR_tagAlg_none] at this
    · obtain ⟨c, d, hcd⟩ := h.polytime
      refine ⟨c, d, fun w δ hδ q hq => ?_⟩
      refine hcd w δ hδ (q.1.map (tag w), q.2) ?_
      rw [tagAlg_apply, PMF.support_map]
      exact ⟨q, hq, rfl⟩

/-- The canonical tagging: `x ↦ ⟨w, x⟩` into `Σ w, Ω w`. -/
def sigmaEmb (w : α) : Ω w ↪ (Σ w : α, Ω w) := ⟨Sigma.mk w, sigma_mk_injective⟩

@[simp] theorem sigmaEmb_apply (w : α) (x : Ω w) :
    sigmaEmb w x = (⟨w, x⟩ : Σ w : α, Ω w) := rfl

/-- **The `Σ`-tagging is subsumed** — `isFPAUSDep_iff_tagged` at the canonical
embedding.  This is the shape a development reaches for first, and it is
recorded separately so that the corollary can be applied without naming a
tagging. -/
theorem isFPAUSDep_iff_tagged_sigma {size : α → ℕ} {g : (w : α) → Finset (Ω w)}
    {A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)} :
    IsFPAUSDep size g A ↔
      IsFPAUS size (fun w => (g w).map (sigmaEmb w)) (tagAlg sigmaEmb A) :=
  isFPAUSDep_iff_tagged sigmaEmb

end Tagging

/-! ## Transporting a dependent FPAUS along a bijective reduction

Both solution types move: the source's with the source instance, the target's
with the target instance.  Nothing in the proof of `IsFPAUS.comp_bijection`
noticed which type it was working in — `decodeOpt` and `decodeOpt_preimage_some`
are statements in a fibre — so the script is unchanged. -/

/-- **A bijective reduction transports a dependent FPAUS.**

The datum is a family of bijections `e w : ↥(g₁ w) ≃ ↥(g₂ (h w))`, exactly as in
`IsFPAUS.comp_bijection`, except that now the two sides of each bijection live
in types that both depend on the instance.  All three clauses transfer without
loss in `δ`.

The one universe constraint is that `Ω₁ w` and `Ω₂ v` lie in a common universe —
needed by `decodeOpt`, which is a map between two solution types at a *fixed*
pair of instances.  Every application has them both in `Type`. -/
theorem IsFPAUSDep.comp_bijection {α : Type u₁} {β : Type u₂}
    {Ω₁ : α → Type v} {Ω₂ : β → Type v}
    {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : (w : α) → Finset (Ω₁ w)} {g₂ : (b : β) → Finset (Ω₂ b)}
    {h : α → β} {cost : α → ℕ}
    {B : (b : β) → ℝ → PMF (Option (Ω₂ b) × ℕ)}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_poly : PolyBounded sizeA cost)
    (hsize : PolyBounded sizeA fun w => sizeB (h w))
    (hg : IsFPAUSDep sizeB g₂ B) :
    IsFPAUSDep sizeA g₁ (fun w δ => (B (h w) δ).map
      (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))) where
  uniform := by
    intro w δ hδ hne x hx
    have hcard : (g₁ w).card = (g₂ (h w)).card := card_eq_of_equiv (e w)
    have h0 : 0 < (g₂ (h w)).card := by
      rw [← hcard]; exact Finset.card_pos.mpr hne
    rw [outProbR_map (B (h w) δ)
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))
        (decodeOpt (g₁ w) (g₂ (h w)) (e w)) (fun _ => rfl) {some x},
      decodeOpt_preimage_some (e w) hx, hcard]
    exact hg.uniform (h w) δ hδ (Finset.card_pos.mp h0) _ (e w ⟨x, hx⟩).2
  empty := by
    intro w δ hδ hemp
    have hcard : (g₁ w).card = (g₂ (h w)).card := card_eq_of_equiv (e w)
    have hemp2 : g₂ (h w) = ∅ := by
      rw [← Finset.card_eq_zero, ← hcard, Finset.card_eq_zero]; exact hemp
    rw [outProbR_map (B (h w) δ)
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))
        (decodeOpt (g₁ w) (g₂ (h w)) (e w)) (fun _ => rfl) {none},
      decodeOpt_preimage_none_of_empty (e w) hemp2]
    exact outProbR_univ _
  polytime := by
    obtain ⟨c, d, hcd⟩ := hg.polytime
    obtain ⟨c', d', hc'⟩ := hsize
    obtain ⟨c'', d'', hc''⟩ := hcost_poly
    obtain ⟨C, D, hCD⟩ := poly_comp_add c c' c'' d d' d''
    refine ⟨C, D, ?_⟩
    intro w δ hδ p hp
    obtain ⟨q, hq, rfl⟩ := mem_support_map hp
    show q.2 + cost w ≤ C * (sizeA w + ⌈Real.log (1/δ)⌉₊ + 1) ^ D
    have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hc' w
    have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈Real.log (1/δ)⌉₊ + 1) ^ d :=
      le_trans (hcd (h w) δ hδ q hq)
        (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
    exact le_trans (Nat.add_le_add h1 (hc'' w)) (hCD (sizeA w) ⌈Real.log (1/δ)⌉₊)

/-! ## The cost API, ported

Every statement in this section is about the *second* component of the output
pair, which is `ℕ` in every fibre.  None of them mentions `Ω` except to bind it,
so the ports are literal. -/

/-- **`IsFPAUSDep.polytime` with the `∃ c d` removed**, the dependent twin of
`IsFPAUS.PinnedTime`. -/
def IsFPAUSDep.PinnedTime {α : Type u} {Ω : α → Type v} (size : α → ℕ)
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) (c e : ℕ) : Prop :=
  ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
    p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ e

/-- **Every run records a positive step count**, the dependent twin of
`IsFPAUS.Charges` — and, as there, the weakest companion that the zero-cost
non-algorithm fails. -/
def IsFPAUSDep.Charges {α : Type u} {Ω : α → Type v}
    (A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)) : Prop :=
  ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support, 0 < p.2

namespace IsFPAUSDep

variable {α : Type u} {Ω : α → Type v} {size : α → ℕ} {g : (w : α) → Finset (Ω w)}
  {A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ)} {c e : ℕ}

/-- A pinned time bound discharges the `polytime` field. -/
theorem PinnedTime.polytime (h : IsFPAUSDep.PinnedTime size A c e) :
    ∃ c d : ℕ, ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
      p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ d := ⟨c, e, h⟩

/-- Weakening a pinned time bound. -/
theorem PinnedTime.weaken {c' e' : ℕ} (h : IsFPAUSDep.PinnedTime size A c e)
    (hc : c ≤ c') (he : e ≤ e') : IsFPAUSDep.PinnedTime size A c' e' := fun w δ hδ p hp =>
  (h w δ hδ p hp).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he))

/-- **What an `IsFPAUSDep` gives back**: some pinned pair, and no more. -/
theorem exists_pinnedTime (h : IsFPAUSDep size g A) :
    ∃ c e : ℕ, IsFPAUSDep.PinnedTime size A c e := h.polytime

/-- An `IsFPAUSDep` may be *assembled* from a pinned time bound. -/
theorem of_pinnedTime
    (hu : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty → ∀ x ∈ g w,
      outProbR (A w δ) {some x} ∈ Set.Icc ((1-δ)/(g w).card) ((1+δ)/(g w).card))
    (he : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, g w = ∅ → outProbR (A w δ) {none} = 1)
    (h : IsFPAUSDep.PinnedTime size A c e) : IsFPAUSDep size g A where
  uniform := hu
  empty := he
  polytime := h.polytime

/-- **The degeneracy, stated, in the dependent form.**  The sampler that records
`0` steps meets `PinnedTime size A c e` at *every* pair of constants, `(0,0)`
included.  Making the solution type depend on the instance does not repair the
cost model, and nothing here should be read as if it did. -/
theorem pinnedTime_of_cost_zero
    (h : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support, p.2 = 0) (c e : ℕ) :
    IsFPAUSDep.PinnedTime size A c e := fun w δ hδ p hp => by
  rw [h w δ hδ p hp]; exact Nat.zero_le _

/-- **`Charges` rejects it.** -/
theorem Charges.not_cost_zero (hA : IsFPAUSDep.Charges A) (w : α) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1) {p : Option (Ω w) × ℕ} (hp : p ∈ (A w δ).support) :
    p.2 ≠ 0 := (hA w δ hδ p hp).ne'

end IsFPAUSDep

/-- **`Charges` survives the reduction**, in the dependent form.  As in
`IsFPAUS.Charges.map_add`, the decoder is left arbitrary: the lemma is about the
step count only, and the composed algorithm's shape is "run `B` at `h w`,
relabel, add `cost w`" whatever the relabelling is. -/
theorem IsFPAUSDep.Charges.map_add {α : Type u₁} {β : Type u₂}
    {Ω₁ : α → Type v} {Ω₂ : β → Type v}
    {B : (b : β) → ℝ → PMF (Option (Ω₂ b) × ℕ)} {hm : α → β} {cost : α → ℕ}
    (dec : (w : α) → Option (Ω₂ (hm w)) → Option (Ω₁ w))
    (hB : ∀ w : α, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (B (hm w) δ).support, 0 < p.2) :
    IsFPAUSDep.Charges
      (fun w δ => (B (hm w) δ).map (fun p => (dec w p.1, p.2 + cost w))) := by
  intro w δ hδ p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  have := hB w δ hδ q hq
  show 0 < q.2 + cost w
  omega

/-! ### The pinned transfer theorems -/

/-- **`IsFPAUSDep.comp_bijection`, with the exponent surviving the hop.**

The first component of the conclusion is `IsFPAUSDep.comp_bijection` verbatim, so
this theorem proves nothing new about accuracy and cannot disagree with the
unpinned one; the second names the composed algorithm's polynomial, at exactly
`Pinned`'s `pinnedCompConst` and `pinnedCompExp`. -/
theorem IsFPAUSDep.comp_bijection_pinned_on {α : Type u₁} {β : Type u₂}
    {Ω₁ : α → Type v} {Ω₂ : β → Type v}
    {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : (w : α) → Finset (Ω₁ w)} {g₂ : (b : β) → Finset (Ω₂ b)}
    {h : α → β} {cost : α → ℕ}
    {B : (b : β) → ℝ → PMF (Option (Ω₂ b) × ℕ)} {c c' c'' d d' d'' : ℕ}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_pin : PinnedBounded sizeA cost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hg : IsFPAUSDep sizeB g₂ B)
    (hB : IsFPAUSDep.PinnedTime (Ω := fun w : α => Ω₂ (h w))
      (fun w => sizeB (h w)) (fun w => B (h w)) c d) :
    IsFPAUSDep sizeA g₁ (fun w δ => (B (h w) δ).map
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
      ∧ IsFPAUSDep.PinnedTime sizeA
          (fun w δ => (B (h w) δ).map
            (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') := by
  refine ⟨IsFPAUSDep.comp_bijection e hcost_pin.polyBounded hsize_pin.polyBounded hg, ?_⟩
  intro w δ hδ p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  show q.2 + cost w
    ≤ pinnedCompConst c c' c'' d
        * (sizeA w + ⌈Real.log (1/δ)⌉₊ + 1) ^ pinnedCompExp d d' d''
  have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hsize_pin w
  have hB' : q.2 ≤ c * (sizeB (h w) + ⌈Real.log (1/δ)⌉₊ + 1) ^ d := hB w δ hδ q hq
  have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈Real.log (1/δ)⌉₊ + 1) ^ d :=
    le_trans hB' (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
  exact le_trans (Nat.add_le_add h1 (hcost_pin w))
    (poly_comp_add_pinned c c' c'' d d' d'' (sizeA w) ⌈Real.log (1/δ)⌉₊)

/-- **`comp_bijection_pinned_on` with the sampler's bound assumed at every target
instance.**  The convenient form. -/
theorem IsFPAUSDep.comp_bijection_pinned {α : Type u₁} {β : Type u₂}
    {Ω₁ : α → Type v} {Ω₂ : β → Type v}
    {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : (w : α) → Finset (Ω₁ w)} {g₂ : (b : β) → Finset (Ω₂ b)}
    {h : α → β} {cost : α → ℕ}
    {B : (b : β) → ℝ → PMF (Option (Ω₂ b) × ℕ)} {c c' c'' d d' d'' : ℕ}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_pin : PinnedBounded sizeA cost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hg : IsFPAUSDep sizeB g₂ B)
    (hB : IsFPAUSDep.PinnedTime sizeB B c d) :
    IsFPAUSDep sizeA g₁ (fun w δ => (B (h w) δ).map
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
      ∧ IsFPAUSDep.PinnedTime sizeA
          (fun w δ => (B (h w) δ).map
            (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') :=
  IsFPAUSDep.comp_bijection_pinned_on e hcost_pin hsize_pin hg (fun w => hB (h w))

/-! ## Satisfiability, and what it costs

`IsFPAUSDep` must not be a predicate nothing satisfies — and it must not be one
*everything* satisfies for a bad reason.  `exists_isFPAUSDep` settles the first:
the sampler that draws exactly uniformly from `g w` at cost `0` is an
`IsFPAUSDep` for **every** solution family whatever, moving type included.  That
is the dependent twin of `CQCount.Capstone.exists_isFPAUS`, and it is the second
point too: the object it exhibits is precisely the zero-cost non-algorithm that
`pinnedTime_of_cost_zero` describes and `Charges` excludes.  So the theorem is a
satisfiability certificate and explicitly **not** an algorithm; a hypothesis of
the form `IsFPAUSDep size g B` is free in this cost model exactly as
`IsFPAUS size g B` is.

A *non-degenerate* instance — a family whose solution sets are nonempty and
whose solution type genuinely moves — is `CQCount.Capstone.KDomain.GrowC`, which
needs a source of real instances and so lives in the sibling repository. -/

open scoped Classical in
/-- The exactly uniform law on a nonempty `Finset`, built from `PMF.ofFinset`.
(Mathlib's `PMF.uniformOfFinset` is in `Probability.Distributions.Uniform`, which
this area does not import; `CQCount.Capstone.uniformPMF` is the same
construction.) -/
noncomputable def uniformFinsetPMF {β : Type*} (s : Finset β) (hs : s.Nonempty) : PMF β :=
  PMF.ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s
    (by
      simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
      have h : (s.card : ℝ≥0∞) ≠ 0 := by
        simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
          Finset.nonempty_iff_ne_empty.1 hs
      exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top s.card))
    (fun x hx => by simp only [hx, if_false])

open scoped Classical in
theorem uniformFinsetPMF_apply_of_mem {β : Type*} {s : Finset β} (hs : s.Nonempty) {a : β}
    (ha : a ∈ s) : uniformFinsetPMF s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  rw [uniformFinsetPMF, PMF.ofFinset_apply, if_pos ha]

open scoped Classical in
/-- **The zero-cost exactly-uniform sampler, fibrewise.**  Draws uniformly from
`g w` when there is anything to draw, reports `none` otherwise, and charges
nothing.  Note that it is defined *at each `w` separately*, in that fibre's own
type — which is the whole reason it is available in the dependent setting. -/
noncomputable def trivSamplerDep {α : Type u} {Ω : α → Type v}
    (g : (w : α) → Finset (Ω w)) (w : α) : PMF (Option (Ω w) × ℕ) :=
  if h : (g w).Nonempty then (uniformFinsetPMF (g w) h).map (fun x => (some x, 0))
  else PMF.pure (none, 0)

/-- **Every dependent solution family has an "FPAUS".**

`trivSamplerDep` is *exactly* uniform, so the `(1 ± δ)` window is met with slack
at both ends at every `δ ∈ (0,1)`, and it records `0` steps, so `polytime` holds
at `(c, d) = (1, 0)`.  The dependent twin of `CQCount.Capstone.exists_isFPAUS`,
with the same reading: an `IsFPAUSDep` hypothesis on the target of a reduction is
**free**, and a theorem proved through one says something about the reduction,
not about the existence of an algorithm. -/
theorem exists_isFPAUSDep {α : Type u} {Ω : α → Type v} (size : α → ℕ)
    (g : (w : α) → Finset (Ω w)) :
    ∃ A : (w : α) → ℝ → PMF (Option (Ω w) × ℕ), IsFPAUSDep size g A := by
  classical
  refine ⟨fun w _ => trivSamplerDep g w, ?_, ?_, ⟨1, 0, ?_⟩⟩
  · intro w δ hδ hne x hx
    have hval : outProbR (trivSamplerDep g w) {some x} = ((g w).card : ℝ)⁻¹ := by
      rw [outProbR, trivSamplerDep, dif_pos hne, outProb, PMF.toOuterMeasure_map_apply]
      have hset : ((fun y => ((some y : Option (Ω w)), 0)) ⁻¹'
          {p : Option (Ω w) × ℕ | p.1 ∈ ({some x} : Set (Option (Ω w)))}) = {x} := by
        ext y; simp
      rw [hset, PMF.toOuterMeasure_apply_singleton, uniformFinsetPMF_apply_of_mem hne hx]
      simp
    have hcard : (0:ℝ) < ((g w).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hne
    rw [hval]
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hcard, inv_mul_cancel₀ (ne_of_gt hcard)]
      linarith [hδ.1]
    · rw [le_div_iff₀ hcard, inv_mul_cancel₀ (ne_of_gt hcard)]
      linarith [hδ.1]
  · intro w δ _ hemp
    have hne : ¬ (g w).Nonempty := by rw [hemp]; simp
    rw [outProbR, trivSamplerDep, dif_neg hne, outProb, PMF.toOuterMeasure_pure_apply]
    simp
  · intro w δ _ p hp
    rw [trivSamplerDep] at hp
    split at hp
    · rw [PMF.support_map] at hp
      obtain ⟨y, -, rfl⟩ := hp
      simp
    · rw [PMF.support_pure] at hp
      simp only [Set.mem_singleton_iff] at hp
      simp [hp]

/-! ## The counting side needs nothing

Stated as a theorem rather than as prose, so that a reader who wonders whether
`IsFPRAS` was also frozen can be shown the answer instead of told it. -/

/-- **`IsFPRAS` has no solution type to make dependent.**

The statement is deliberately a triviality: `IsFPRAS size f A` is `Iff.rfl` to
itself after abstracting an arbitrary family of types `Ω : α → Type v`, because
no clause of `IsFPRAS` mentions `Ω`.  An FPRAS returns a real number, and `ℝ`
does not move with the instance.

Consequently there is **no** `IsFPRASDep` in this module.  A family of counting
problems whose solution objects move is already an `IsFPRAS` over the `Σ`-type
of instances, with no new definition and no tagging — which is exactly what
`CQCount.Capstone.KAtoms.StarPath.fpras_starFam` and
`CQCount.Capstone.KDomain.fprasD_fam` do.  Building a symmetric-looking
`IsFPRASDep` with a phantom parameter would suggest a difficulty that does not
exist. -/
theorem isFPRAS_no_dependent_output {α : Type u} (Ω : α → Type v) (size : α → ℕ)
    (f : α → ℝ) (A : α → ℝ → PMF (ℝ × ℕ)) :
    IsFPRAS size f A ↔ ∀ _ : (w : α) → Finset (Ω w), IsFPRAS size f A :=
  ⟨fun h _ => h, fun h => h fun w => (∅ : Finset (Ω w))⟩

end Arlib.Approximation
