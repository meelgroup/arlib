/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Parsimonious

/-!
# Polynomial bounds with the constants written down

`Arlib.Approximation.Counting` models an algorithm as `α → PMF (β × ℕ)`, and
both `IsFPRAS.polytime` and `IsFPAUS.polytime` bound the recorded step count
**from above** by `c * (size w + … + 1) ^ d` for constants `c, d` that are
*existentially quantified*.  That shape is the right definition of "is an FPRAS",
but it is a weak thing to *prove*: the algorithm that records `0` steps satisfies
it, and so does every algorithm whose cost is bounded by any polynomial at all.
A development that has computed an actual exponent has no way, through
`PolyBounded`, to say so.

This module supplies the un-quantified companions.

## What is here

* `PinnedBounded s B c e` — `B w ≤ c * (s w + 1) ^ e`, with `c` and `e`
  *parameters* rather than existentials.  `PinnedBounded.polyBounded` is the
  forgetful map to `PolyBounded`, and `PolyBounded` is exactly
  `∃ c e, PinnedBounded s B c e` (`polyBounded_iff`).
* `IsFPRAS.PinnedTime size A c e` and `IsFPAUS.PinnedTime size A c e` — the
  `polytime` clause with its `∃ c d` removed.  These are *predicates about an
  algorithm*, not fields of a structure, precisely so that they can be added to
  an existing conclusion without changing the type of that conclusion.
* `pinnedCompConst`, `pinnedCompExp`, `poly_comp_add_pinned` — the arithmetic of
  `Parsimonious.poly_comp_add` with the witnesses `⟨c * (c' + 2) ^ d + c'',
  max (max d' 1 * d) d''⟩` promoted from the *proof term* into the *statement*.
  Nothing is proved here that `poly_comp` and `poly_add` did not already prove;
  what changes is that a caller can now read the constants off the statement.
* `IsFPRAS.comp_parsimonious_pinned` and `IsFPAUS.comp_bijection_pinned` — the
  transfer theorems of `Arlib.Approximation.Parsimonious` with the exponent
  surviving the hop.  Each returns a **conjunction**: the original conclusion,
  unchanged and proved by the original theorem, together with the pinned
  running-time statement about the very same composed algorithm.
* `IsFPAUS.Charges` and `IsFPRAS.Charges` — *every* recorded step count is
  positive.  A pinned upper bound is still only an upper bound, and
  `IsFPAUS.pinnedTime_of_cost_zero` / `IsFPRAS.pinnedTime_of_cost_zero` show that
  the algorithm recording `0` meets `PinnedTime size A c e` at **every** pair of
  constants, including `(0, 0)`.  So a pinned conclusion pins a number only when
  it is accompanied by something the zero-cost non-algorithm fails, and `Charges`
  is the weakest such thing.  `Charges.map_add` carries it across the reduction,
  so a caller can transport the sandwich and not just its upper half.
* `IsFPRAS.comp_parsimonious_pinned_on` and `IsFPAUS.comp_bijection_pinned_on` —
  the same, with the *source* algorithm's pinned running time assumed only along
  the reduction, i.e. as
  `PinnedTime (fun w => sizeB (h w)) (fun w => B (h w)) c d`.  This is the form
  that matters in practice: a target algorithm's running-time analysis often
  carries standing normalisation hypotheses (minimum arity, minimum alphabet
  size, tolerance below `1/2`) that the target *type* does not enforce, so a
  bound holding at *every* target instance may be unobtainable while the bound
  at the instances the reduction actually emits is fine.  The unrestricted forms
  are one-line corollaries.

## Why a conjunction, and why a new module

`IsFPRAS` and `IsFPAUS` are `Prop`-valued structures whose `polytime` fields have
existential type.  Strengthening those fields in place would change the type of
every existing consumer; and *replacing* `comp_bijection` by a pinned version
would break every caller.  So the pinned statements are added **alongside**:
`comp_bijection_pinned` is proved by calling `comp_bijection` for the accuracy
half and redoing only the polytime half with the constants kept.  The two
theorems have the same hypotheses up to `PinnedBounded.polyBounded`, so nothing
is assumed here that was not assumed there.

The module is separate from `Parsimonious` for the same reason: `Parsimonious`
is imported by the automata development and by downstream reductions, and this
file adds to it without touching it.

## What is still existential after this

`IsFPRAS.polytime` and `IsFPAUS.polytime` themselves.  A `PinnedTime` conjunct
does not remove the existential from the structure — it stands beside it, and
says of the *same* algorithm what the structure only says exists.  A caller who
wants a number takes the second conjunct; a caller who wants an `IsFPRAS` takes
the first.  Making the structures themselves pinned would be a different
definition of "FPRAS", and not the one the literature uses.
-/

universe u v

namespace Arlib.Approximation

variable {α : Type*} {β : Type*}

/-! ## Polynomial bounds with named constants -/

/-- **`PolyBounded` with the constants exposed.**  `B w ≤ c * (s w + 1) ^ e`.

The `+ 1` is inherited from `PolyBounded`, and for the same two reasons: the
bound must be usable at `s w = 0`, and the base must be at least `1` so that
raising the exponent is monotone. -/
def PinnedBounded {α : Type*} (s B : α → ℕ) (c e : ℕ) : Prop :=
  ∀ w, B w ≤ c * (s w + 1) ^ e

namespace PinnedBounded

variable {s B B' : α → ℕ} {c c' e e' : ℕ}

/-- Forgetting the constants. -/
theorem polyBounded (h : PinnedBounded s B c e) : PolyBounded s B := ⟨c, e, h⟩

/-- A bound below a pinned bound is a pinned bound, at the *same* constants —
which is the point: `PolyBounded.mono` also keeps the constants, but has no way
to say so. -/
theorem mono (h : PinnedBounded s B c e) (hle : ∀ w, B' w ≤ B w) :
    PinnedBounded s B' c e := fun w => (hle w).trans (h w)

/-- A constant function is pinned at `(c, 0)`. -/
theorem const (s : α → ℕ) (c : ℕ) : PinnedBounded s (fun _ => c) c 0 := fun _ => by simp

/-- Enlarging either constant weakens the bound.  Needed whenever two pinned
bounds must be brought to a common pair before being added. -/
theorem weaken (h : PinnedBounded s B c e) (hc : c ≤ c') (he : e ≤ e') :
    PinnedBounded s B c' e' := fun w =>
  (h w).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he))

end PinnedBounded

/-- **`PolyBounded` is exactly the existential closure of `PinnedBounded`.**  So
nothing is lost by working with the pinned form and forgetting at the end, and a
development that only ever produces `PolyBounded` is producing this existential
and no more. -/
theorem polyBounded_iff {s B : α → ℕ} :
    PolyBounded s B ↔ ∃ c e : ℕ, PinnedBounded s B c e := Iff.rfl

/-! ## The `polytime` clauses, unquantified -/

/-- **`IsFPRAS.polytime` with the `∃ c d` removed.**  Note that this mentions
neither `f` nor the accuracy clause: it is a statement about the *cost* half of
an algorithm alone, so that it can be carried beside an `IsFPRAS` without
changing that structure's type. -/
def IsFPRAS.PinnedTime {α : Type*} (size : α → ℕ) (A : α → ℝ → PMF (ℝ × ℕ))
    (c e : ℕ) : Prop :=
  ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w ε).support,
    p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ e

/-- **`IsFPAUS.polytime` with the `∃ c d` removed.**  As in `IsFPAUS`, the second
size parameter is `⌈log (1/δ)⌉₊` and not `⌈δ⁻¹⌉₊`. -/
def IsFPAUS.PinnedTime {α : Type*} {Ω : Type v} (size : α → ℕ)
    (A : α → ℝ → PMF (Option Ω × ℕ)) (c e : ℕ) : Prop :=
  ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
    p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ e

namespace IsFPRAS

variable {size : α → ℕ} {f : α → ℝ} {A : α → ℝ → PMF (ℝ × ℕ)} {c e : ℕ}

/-- A pinned time bound discharges the `polytime` field. -/
theorem PinnedTime.polytime (h : IsFPRAS.PinnedTime size A c e) :
    ∃ c d : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w ε).support,
      p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d := ⟨c, e, h⟩

/-- Weakening a pinned time bound. -/
theorem PinnedTime.weaken {c' e' : ℕ} (h : IsFPRAS.PinnedTime size A c e)
    (hc : c ≤ c') (he : e ≤ e') : IsFPRAS.PinnedTime size A c' e' := fun w ε hε p hp =>
  (h w ε hε p hp).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he))

/-- **What an `IsFPRAS` gives back**: some pinned pair, and no more.  This is the
exact sense in which the definition is existential. -/
theorem exists_pinnedTime (h : IsFPRAS size f A) :
    ∃ c e : ℕ, IsFPRAS.PinnedTime size A c e := h.polytime

/-- An `IsFPRAS` may be *assembled* from a pinned time bound. -/
theorem of_pinnedTime
    (hacc : ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, 3/4 ≤ outProbR (A w ε) {y | |y - f w| ≤ ε * f w})
    (h : IsFPRAS.PinnedTime size A c e) : IsFPRAS size f A where
  accuracy := hacc
  polytime := h.polytime

end IsFPRAS

namespace IsFPAUS

variable {Ω : Type v} {size : α → ℕ} {g : α → Finset Ω}
  {A : α → ℝ → PMF (Option Ω × ℕ)} {c e : ℕ}

/-- A pinned time bound discharges the `polytime` field. -/
theorem PinnedTime.polytime (h : IsFPAUS.PinnedTime size A c e) :
    ∃ c d : ℕ, ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
      p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ d := ⟨c, e, h⟩

/-- Weakening a pinned time bound. -/
theorem PinnedTime.weaken {c' e' : ℕ} (h : IsFPAUS.PinnedTime size A c e)
    (hc : c ≤ c') (he : e ≤ e') : IsFPAUS.PinnedTime size A c' e' := fun w δ hδ p hp =>
  (h w δ hδ p hp).trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he))

/-- **What an `IsFPAUS` gives back**: some pinned pair, and no more. -/
theorem exists_pinnedTime (h : IsFPAUS size g A) :
    ∃ c e : ℕ, IsFPAUS.PinnedTime size A c e := h.polytime

/-- An `IsFPAUS` may be *assembled* from a pinned time bound. -/
theorem of_pinnedTime
    (hu : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty → ∀ x ∈ g w,
      outProbR (A w δ) {some x} ∈ Set.Icc ((1-δ)/(g w).card) ((1+δ)/(g w).card))
    (he : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, g w = ∅ → outProbR (A w δ) {none} = 1)
    (h : IsFPAUS.PinnedTime size A c e) : IsFPAUS size g A where
  uniform := hu
  empty := he
  polytime := h.polytime

end IsFPAUS

/-! ## The other half of the sandwich

A pinned bound is still an upper bound, and an upper bound on a recorded step
count says nothing about the algorithm unless the algorithm records something.
`pinnedTime_of_cost_zero` makes the gap precise — the zero-cost non-algorithm
satisfies `PinnedTime` at *every* pair of constants — and `Charges` is the
minimal companion that excludes it. -/

/-- **Every run records a positive step count.**

Deliberately weak: not "records at least the pinned bound", which would be false
for any algorithm with a fast path, but merely "records something".  That is
already enough to separate a real analysis from `pinnedTime_of_cost_zero`, and
being weak it survives every hop that only *adds* cost. -/
def IsFPAUS.Charges {α : Type*} {Ω : Type v} (A : α → ℝ → PMF (Option Ω × ℕ)) : Prop :=
  ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support, 0 < p.2

/-- **The degeneracy, stated.**

An algorithm that records `0` steps satisfies `IsFPAUS.PinnedTime size A c e` for
*every* `c` and `e`, including `c = e = 0`.  So no pinned running-time statement,
however small its constants, is on its own evidence that a computation was
performed — which is exactly the objection that applies to `IsFPAUS.polytime`,
undiminished by pinning the constants.  What pinning buys is that the bound is a
*number*; what excludes the non-algorithm is `Charges`. -/
theorem IsFPAUS.pinnedTime_of_cost_zero {Ω : Type v} {size : α → ℕ}
    {A : α → ℝ → PMF (Option Ω × ℕ)}
    (h : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support, p.2 = 0) (c e : ℕ) :
    IsFPAUS.PinnedTime size A c e := fun w δ hδ p hp => by
  rw [h w δ hδ p hp]; exact Nat.zero_le _

/-- **`Charges` rejects it.**  The two are incompatible as soon as the algorithm
is run anywhere, and a `PMF`'s support is never empty, so this is not a vacuous
incompatibility. -/
theorem IsFPAUS.Charges.not_cost_zero {Ω : Type v} {A : α → ℝ → PMF (Option Ω × ℕ)}
    (hA : IsFPAUS.Charges A) (w : α) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1)
    {p : Option Ω × ℕ} (hp : p ∈ (A w δ).support) : p.2 ≠ 0 :=
  (hA w δ hδ p hp).ne'

/-- **`Charges` survives the reduction.**

The composed algorithms of `comp_bijection_pinned_on` and of
`ParsimoniousReduction` all have the shape "run `B` at `h w`, relabel the sample,
add `cost w`", and the relabelling does not touch the second component while the
addition only increases it.  Stating it for an arbitrary decoder `dec` rather than
for `decodeOpt` keeps it applicable to both, and to any future decoder. -/
theorem IsFPAUS.Charges.map_add {Ω₁ : Type v} {Ω₂ : Type v}
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} {hm : α → β} {cost : α → ℕ}
    (dec : α → Option Ω₂ → Option Ω₁)
    (hB : ∀ w : α, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (B (hm w) δ).support, 0 < p.2) :
    IsFPAUS.Charges
      (fun w δ => (B (hm w) δ).map (fun p => (dec w p.1, p.2 + cost w))) := by
  intro w δ hδ p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  have := hB w δ hδ q hq
  show 0 < q.2 + cost w
  omega

/-! ### The same, on the counting side

`IsFPRAS` records a step count in exactly the way `IsFPAUS` does, and
`IsFPRAS.polytime` bounds it from above in exactly the way `IsFPAUS.polytime`
does, so the degeneracy and its remedy are the same three statements with `δ`
replaced by `ε` and `Option Ω` by `ℝ`.  They are spelled out rather than derived
from a common generalisation because `IsFPRAS.PinnedTime` and
`IsFPAUS.PinnedTime` differ in their *second size parameter* — `⌈ε⁻¹⌉₊` against
`⌈log (1/δ)⌉₊` — and a shared abstraction would have to be parameterised by that
choice, which would obscure the two definitions this module exists to make
readable. -/

/-- **Every run of a counting algorithm records a positive step count.**

The counting analogue of `IsFPAUS.Charges`, and deliberately as weak: it says
only that the algorithm does *something* on every run, which is already enough to
separate a real running-time analysis from `IsFPRAS.pinnedTime_of_cost_zero`, and
being weak it survives every hop that only adds cost. -/
def IsFPRAS.Charges {α : Type*} (A : α → ℝ → PMF (ℝ × ℕ)) : Prop :=
  ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w ε).support, 0 < p.2

/-- **The degeneracy, stated, on the counting side.**

An estimator that records `0` steps satisfies `IsFPRAS.PinnedTime size A c e` for
*every* `c` and `e`, `(0, 0)` included.  Since a zero-cost estimator may also be
*exact* — return the count itself with probability one — it satisfies the
`accuracy` clause too, and is therefore a complete `IsFPRAS` at every pinned pair
of constants.  So a pinned counting bound, however small its constants, is on its
own no evidence that a computation was performed. -/
theorem IsFPRAS.pinnedTime_of_cost_zero {size : α → ℕ} {A : α → ℝ → PMF (ℝ × ℕ)}
    (h : ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w ε).support, p.2 = 0) (c e : ℕ) :
    IsFPRAS.PinnedTime size A c e := fun w ε hε p hp => by
  rw [h w ε hε p hp]; exact Nat.zero_le _

/-- **`Charges` rejects it.**  A `PMF`'s support is never empty, so the
incompatibility is not vacuous: at any `w` and any `ε ∈ (0,1)` there is a point
at which the two clauses contradict each other. -/
theorem IsFPRAS.Charges.not_cost_zero {A : α → ℝ → PMF (ℝ × ℕ)}
    (hA : IsFPRAS.Charges A) (w : α) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1)
    {p : ℝ × ℕ} (hp : p ∈ (A w ε).support) : p.2 ≠ 0 :=
  (hA w ε hε p hp).ne'

/-- **`Charges` survives the reduction.**

The composed algorithm of `IsFPRAS.comp_parsimonious_pinned_on` and of
`ParsimoniousReduction` has the shape "run `B` at `h w`, keep the estimate, add
`cost w`", and the addition only increases the second component.  As on the
sampling side the estimate transformer `dec` is left arbitrary — parsimony makes
it the identity here, but nothing in this lemma needs that, and a reduction that
rescaled the estimate would still charge. -/
theorem IsFPRAS.Charges.map_add {B : β → ℝ → PMF (ℝ × ℕ)} {hm : α → β} {cost : α → ℕ}
    (dec : α → ℝ → ℝ)
    (hB : ∀ w : α, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (B (hm w) ε).support, 0 < p.2) :
    IsFPRAS.Charges
      (fun w ε => (B (hm w) ε).map (fun p => (dec w p.1, p.2 + cost w))) := by
  intro w ε hε p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  have := hB w ε hε q hq
  show 0 < q.2 + cost w
  omega

/-! ## The composition constants

`Parsimonious.poly_comp_add` is stated as `∃ C D, …` and *proved* by exhibiting
`C = c * (c' + 2) ^ d + c''` and `D = max (max d' 1 * d) d''`.  Those two
expressions are the entire content of "the exponent survives a parsimonious
reduction", and they are promoted here from the proof term into the statement. -/

/-- The constant produced by composing an outer polynomial `(c, d)` with an inner
blow-up `(c', d')` and adding a reduction cost `(c'', d'')`.

The `(c' + 2) ^ d` is not slack: `poly_comp` must absorb both the inner constant
`c'` and the additive `m + 1` into a single base, and `+2` is what pays for the
latter. -/
def pinnedCompConst (c c' c'' d : ℕ) : ℕ := c * (c' + 2) ^ d + c''

/-- The exponent produced by the same composition.

`max d' 1 * d` rather than `d' * d`: the summand `m + 1` also has to be absorbed
into `(n + m + 1) ^ (max d' 1)`, and at `d' = 0` the naive product `0` is false.
The outer `max … d''` is the reduction's own cost. -/
def pinnedCompExp (d d' d'' : ℕ) : ℕ := max (max d' 1 * d) d''

/-- **`poly_comp_add` with its witnesses in the statement.**

Identical content to `poly_comp_add`; the difference is that `pinnedCompConst`
and `pinnedCompExp` are now available to a caller who wants to *name* the
resulting polynomial rather than merely assert one exists. -/
theorem poly_comp_add_pinned (c c' c'' d d' d'' n m : ℕ) :
    c * (c' * (n + 1) ^ d' + m + 1) ^ d + c'' * (n + 1) ^ d''
      ≤ pinnedCompConst c c' c'' d * (n + m + 1) ^ pinnedCompExp d d' d'' :=
  le_trans (Nat.add_le_add (poly_comp c c' d d' n m) (le_refl _))
    (poly_add _ c'' _ d'' n m)

/-! ## Transporting a pinned FPRAS -/

/-- **`IsFPRAS.comp_parsimonious`, with the exponent surviving the hop.**

Same reduction data as `IsFPRAS.comp_parsimonious`, with the two `PolyBounded`
hypotheses replaced by `PinnedBounded` ones and the source algorithm's running
time given as an `IsFPRAS.PinnedTime` rather than read out of `hg.polytime`.
The conclusion is a conjunction:

* the first component is *literally* `IsFPRAS.comp_parsimonious` applied to the
  forgetful images of the pinned hypotheses — so this theorem proves nothing new
  about accuracy and cannot disagree with the unpinned one;
* the second names the polynomial of the composed algorithm:

      cost ≤ (c·(c'+2)^d + c'') · (|w| + ⌈ε⁻¹⌉ + 1) ^ max (max d' 1 · d) d''.

**The hypotheses are not stronger than `comp_parsimonious`'s.**  `hg` still
carries the accuracy clause, and `hB` is one instance of `hg.polytime`'s
existential; a caller who has only `hg` obtains `hB` from
`IsFPRAS.exists_pinnedTime`, at constants they then cannot name — which is the
whole asymmetry this module exists to record. -/
theorem IsFPRAS.comp_parsimonious_pinned_on
    {sizeA : α → ℕ} {sizeB : β → ℕ} {f : α → ℝ} {g : β → ℝ}
    {h : α → β} {hcost : α → ℕ} {B : β → ℝ → PMF (ℝ × ℕ)} {c c' c'' d d' d'' : ℕ}
    (hcost_pin : PinnedBounded sizeA hcost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hf : ∀ w, f w = g (h w))
    (hg : IsFPRAS sizeB g B)
    (hB : IsFPRAS.PinnedTime (fun w => sizeB (h w)) (fun w => B (h w)) c d) :
    IsFPRAS sizeA f (fun w ε => (B (h w) ε).map (fun p => (p.1, p.2 + hcost w)))
      ∧ IsFPRAS.PinnedTime sizeA
          (fun w ε => (B (h w) ε).map (fun p => (p.1, p.2 + hcost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') := by
  refine ⟨IsFPRAS.comp_parsimonious hcost_pin.polyBounded hsize_pin.polyBounded hf hg, ?_⟩
  intro w ε hε p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  show q.2 + hcost w ≤ pinnedCompConst c c' c'' d * (sizeA w + ⌈ε⁻¹⌉₊ + 1) ^ pinnedCompExp d d' d''
  have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hsize_pin w
  have hB' : q.2 ≤ c * (sizeB (h w) + ⌈ε⁻¹⌉₊ + 1) ^ d := hB w ε hε q hq
  have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈ε⁻¹⌉₊ + 1) ^ d :=
    le_trans hB'
      (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
  exact le_trans (Nat.add_le_add h1 (hcost_pin w))
    (poly_comp_add_pinned c c' c'' d d' d'' (sizeA w) ⌈ε⁻¹⌉₊)

/-- **`comp_parsimonious_pinned_on` with the source bound assumed everywhere.**
The form a caller with a global `IsFPRAS.PinnedTime` uses. -/
theorem IsFPRAS.comp_parsimonious_pinned
    {sizeA : α → ℕ} {sizeB : β → ℕ} {f : α → ℝ} {g : β → ℝ}
    {h : α → β} {hcost : α → ℕ} {B : β → ℝ → PMF (ℝ × ℕ)} {c c' c'' d d' d'' : ℕ}
    (hcost_pin : PinnedBounded sizeA hcost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hf : ∀ w, f w = g (h w))
    (hg : IsFPRAS sizeB g B)
    (hB : IsFPRAS.PinnedTime sizeB B c d) :
    IsFPRAS sizeA f (fun w ε => (B (h w) ε).map (fun p => (p.1, p.2 + hcost w)))
      ∧ IsFPRAS.PinnedTime sizeA
          (fun w ε => (B (h w) ε).map (fun p => (p.1, p.2 + hcost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') :=
  IsFPRAS.comp_parsimonious_pinned_on hcost_pin hsize_pin hf hg (fun w => hB (h w))

/-! ## Transporting a pinned FPAUS -/

/-- **`IsFPAUS.comp_bijection`, with the exponent surviving the hop.**

The reduction data is unchanged — a family of bijections `e w : ↥(g₁ w) ≃
↥(g₂ (h w))`, a cost, and a size blow-up — but the two bounds are pinned and the
sampler's running time is given as an `IsFPAUS.PinnedTime`.  The first component
of the conclusion is `IsFPAUS.comp_bijection` verbatim; the second is

    cost ≤ (c·(c'+2)^d + c'') · (|w| + ⌈log(1/δ)⌉ + 1) ^ max (max d' 1 · d) d''

for the *same* composed algorithm.  Note that `δ` is passed through the reduction
unchanged, exactly as in the unpinned theorem, so no tolerance rescaling enters
the exponent: the only sources of growth are the size blow-up `d'` and the
reduction's own cost `d''`.

This is the hop at which an explicit `#TA`-level exponent becomes an explicit
`#k-HW`-level exponent.  Without it, `hg.polytime`'s existential is opened at the
first step and the number is gone. -/
theorem IsFPAUS.comp_bijection_pinned_on
    {Ω₁ Ω₂ : Type u} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂} {h : α → β} {cost : α → ℕ}
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} {c c' c'' d d' d'' : ℕ}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_pin : PinnedBounded sizeA cost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hg : IsFPAUS sizeB g₂ B)
    (hB : IsFPAUS.PinnedTime (fun w => sizeB (h w)) (fun w => B (h w)) c d) :
    IsFPAUS sizeA g₁ (fun w δ => (B (h w) δ).map
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
      ∧ IsFPAUS.PinnedTime sizeA
          (fun w δ => (B (h w) δ).map
            (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') := by
  refine ⟨IsFPAUS.comp_bijection e hcost_pin.polyBounded hsize_pin.polyBounded hg, ?_⟩
  intro w δ hδ p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  show q.2 + cost w
    ≤ pinnedCompConst c c' c'' d
        * (sizeA w + ⌈Real.log (1/δ)⌉₊ + 1) ^ pinnedCompExp d d' d''
  have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hsize_pin w
  have hB' : q.2 ≤ c * (sizeB (h w) + ⌈Real.log (1/δ)⌉₊ + 1) ^ d := hB w δ hδ q hq
  have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈Real.log (1/δ)⌉₊ + 1) ^ d :=
    le_trans hB'
      (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
  exact le_trans (Nat.add_le_add h1 (hcost_pin w))
    (poly_comp_add_pinned c c' c'' d d' d'' (sizeA w) ⌈Real.log (1/δ)⌉₊)

/-- **`comp_bijection_pinned_on` with the sampler's bound assumed at every target
instance.**  The convenient form; `comp_bijection_pinned_on` is the one to use
when the target-side bound is only available on a subfamily, which is the usual
situation when the target algorithm's running-time analysis carries standing
normalisation hypotheses that the target *type* does not enforce. -/
theorem IsFPAUS.comp_bijection_pinned
    {Ω₁ Ω₂ : Type u} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂} {h : α → β} {cost : α → ℕ}
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} {c c' c'' d d' d'' : ℕ}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_pin : PinnedBounded sizeA cost c'' d'')
    (hsize_pin : PinnedBounded sizeA (fun w => sizeB (h w)) c' d')
    (hg : IsFPAUS sizeB g₂ B)
    (hB : IsFPAUS.PinnedTime sizeB B c d) :
    IsFPAUS sizeA g₁ (fun w δ => (B (h w) δ).map
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
      ∧ IsFPAUS.PinnedTime sizeA
          (fun w δ => (B (h w) δ).map
            (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w)))
          (pinnedCompConst c c' c'' d) (pinnedCompExp d d' d'') :=
  IsFPAUS.comp_bijection_pinned_on e hcost_pin hsize_pin hg (fun w => hB (h w))

/-! ## The bundled reduction, pinned

`ParsimoniousReduction` carries its two bounds as `PolyBounded`, so it cannot
transport an exponent.  `PinnedReduction` is the same bundle with the constants
named; `toParsimoniousReduction` forgets them, so anything proved of the unpinned
bundle applies. -/

/-- **A parsimonious reduction whose cost and size blow-up have named
constants.**  Same six fields as `ParsimoniousReduction`, with `cost_poly` and
`size_poly` pinned at `(costConst, costExp)` and `(sizeConst, sizeExp)`. -/
structure PinnedReduction {α β : Type*} {Ω₁ Ω₂ : Type u}
    (sizeA : α → ℕ) (sizeB : β → ℕ) (f : α → ℝ) (g : β → ℝ)
    (g₁ : α → Finset Ω₁) (g₂ : β → Finset Ω₂) (costConst costExp sizeConst sizeExp : ℕ) where
  /-- The reduction map on instances. -/
  toFun : α → β
  /-- The cost of computing `toFun` and of decoding a sample back. -/
  cost : α → ℕ
  /-- The reduction runs in time `costConst · (|w| + 1) ^ costExp`. -/
  cost_pinned : PinnedBounded sizeA cost costConst costExp
  /-- The output is of size at most `sizeConst · (|w| + 1) ^ sizeExp`. -/
  size_pinned : PinnedBounded sizeA (fun w => sizeB (toFun w)) sizeConst sizeExp
  /-- **Parsimony**: the reduction preserves the count exactly. -/
  count_eq : ∀ w, f w = g (toFun w)
  /-- The decoding bijection between solution sets. -/
  decode : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (toFun w))

namespace PinnedReduction

variable {Ω₁ Ω₂ : Type u} {sizeA : α → ℕ} {sizeB : β → ℕ} {f : α → ℝ} {g : β → ℝ}
  {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂} {cc ce sc se : ℕ}

/-- Forgetting the constants recovers a `ParsimoniousReduction`, so every
theorem about the latter applies. -/
def toParsimoniousReduction (R : PinnedReduction sizeA sizeB f g g₁ g₂ cc ce sc se) :
    ParsimoniousReduction sizeA sizeB f g g₁ g₂ where
  toFun := R.toFun
  cost := R.cost
  cost_poly := R.cost_pinned.polyBounded
  size_poly := R.size_pinned.polyBounded
  count_eq := R.count_eq
  decode := R.decode

/-- **A pinned FPRAS transfers, with its exponent.** -/
theorem isFPRAS_comp_pinned (R : PinnedReduction sizeA sizeB f g g₁ g₂ cc ce sc se)
    {B : β → ℝ → PMF (ℝ × ℕ)} {c d : ℕ} (hg : IsFPRAS sizeB g B)
    (hB : IsFPRAS.PinnedTime sizeB B c d) :
    IsFPRAS sizeA f (fun w ε => (B (R.toFun w) ε).map (fun p => (p.1, p.2 + R.cost w)))
      ∧ IsFPRAS.PinnedTime sizeA
          (fun w ε => (B (R.toFun w) ε).map (fun p => (p.1, p.2 + R.cost w)))
          (pinnedCompConst c sc cc d) (pinnedCompExp d se ce) :=
  IsFPRAS.comp_parsimonious_pinned R.cost_pinned R.size_pinned R.count_eq hg hB

/-- **A pinned FPAUS transfers, with its exponent.** -/
theorem isFPAUS_comp_pinned (R : PinnedReduction sizeA sizeB f g g₁ g₂ cc ce sc se)
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} {c d : ℕ} (hg : IsFPAUS sizeB g₂ B)
    (hB : IsFPAUS.PinnedTime sizeB B c d) :
    IsFPAUS sizeA g₁ (fun w δ => (B (R.toFun w) δ).map
        (fun p => (decodeOpt (g₁ w) (g₂ (R.toFun w)) (R.decode w) p.1, p.2 + R.cost w)))
      ∧ IsFPAUS.PinnedTime sizeA
          (fun w δ => (B (R.toFun w) δ).map
            (fun p => (decodeOpt (g₁ w) (g₂ (R.toFun w)) (R.decode w) p.1, p.2 + R.cost w)))
          (pinnedCompConst c sc cc d) (pinnedCompExp d se ce) :=
  IsFPAUS.comp_bijection_pinned R.decode R.cost_pinned R.size_pinned hg hB

end PinnedReduction

/-! ## Sanity: the constants at the identity reduction

A reduction that does nothing — `h = id`, `cost = 0`, no size blow-up — must not
change the exponent.  It does not: `pinnedCompExp d 0 0 = d`, and the constant
grows only by the `3 ^ d` that `poly_comp` pays for absorbing `m + 1`. -/

theorem pinnedCompExp_id (d : ℕ) : pinnedCompExp d 0 0 = d := by
  simp [pinnedCompExp]

theorem pinnedCompConst_id (c d : ℕ) : pinnedCompConst c 1 0 d = c * 3 ^ d := by
  simp [pinnedCompConst]

end Arlib.Approximation
